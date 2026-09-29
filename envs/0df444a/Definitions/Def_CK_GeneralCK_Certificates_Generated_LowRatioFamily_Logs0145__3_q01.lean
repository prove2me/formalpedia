-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0145__3_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0145__3_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T05:10:50.658597+00:00
-- url     : https://prove2.me/theorems/4e6f6f33-06de-4e41-861e-ac11f514980c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0145 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0146, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0147) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0145__3_q00

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9344_neg : (336172281 / 1000000000) ≤ -Real.log (1429 / 2000) ∧
    -Real.log (1429 / 2000) ≤ (168086141 / 500000000) := by
  have h := checkLog_sound (w := (571 / 3429)) (n := 12)
    (lo := (336172281 / 1000000000)) (hi := (168086141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1429) = 1/(1429 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9344 : Bounds (-168086141 / 500000000) (-336172281 / 1000000000) (Real.log (1429 / 2000)) := by
  have h := reflection_log_9344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9345_neg : (285459 / 1000000000) ≤ -Real.log (2000000 / 2000571) ∧
    -Real.log (2000000 / 2000571) ≤ (14273 / 50000000) := by
  have h := checkLog_sound (w := (571 / 4000571)) (n := 12)
    (lo := (285459 / 1000000000)) (hi := (14273 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000571 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000571 / 2000000) = 1/(2000000 / 2000571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9345 : Bounds (285459 / 1000000000) (14273 / 50000000) (Real.log (2000571 / 2000000)) := by
  have h := reflection_log_9345_neg
  have he : Real.log (2000571 / 2000000) = -Real.log (2000000 / 2000571) := by
    rw [show ((2000571 / 2000000) : ℝ) = ((2000000 / 2000571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9346_neg : (14277 / 50000000) ≤ -Real.log (1999429 / 2000000) ∧
    -Real.log (1999429 / 2000000) ≤ (285541 / 1000000000) := by
  have h := checkLog_sound (w := (571 / 3999429)) (n := 12)
    (lo := (14277 / 50000000)) (hi := (285541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999429) = 1/(1999429 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9346 : Bounds (-285541 / 1000000000) (-14277 / 50000000) (Real.log (1999429 / 2000000)) := by
  have h := reflection_log_9346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9347_neg : (4217691 / 31250000) ≤ -Real.log (500000 / 572249) ∧
    -Real.log (500000 / 572249) ≤ (134966113 / 1000000000) := by
  have h := checkLog_sound (w := (72249 / 1072249)) (n := 12)
    (lo := (4217691 / 31250000)) (hi := (134966113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572249 / 500000) = 1/(500000 / 572249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9347 : Bounds (4217691 / 31250000) (134966113 / 1000000000) (Real.log (572249 / 500000)) := by
  have h := reflection_log_9347_neg
  have he : Real.log (572249 / 500000) = -Real.log (500000 / 572249) := by
    rw [show ((572249 / 500000) : ℝ) = ((500000 / 572249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9348_neg : (156066847 / 1000000000) ≤ -Real.log (427751 / 500000) ∧
    -Real.log (427751 / 500000) ≤ (4877089 / 31250000) := by
  have h := checkLog_sound (w := (72249 / 927751)) (n := 12)
    (lo := (156066847 / 1000000000)) (hi := (4877089 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427751) = 1/(427751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9348 : Bounds (-4877089 / 31250000) (-156066847 / 1000000000) (Real.log (427751 / 500000)) := by
  have h := reflection_log_9348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9349_neg : (33860111 / 250000000) ≤ -Real.log (1000000 / 1145041) ∧
    -Real.log (1000000 / 1145041) ≤ (27088089 / 200000000) := by
  have h := checkLog_sound (w := (145041 / 2145041)) (n := 12)
    (lo := (33860111 / 250000000)) (hi := (27088089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145041 / 1000000) = 1/(1000000 / 1145041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9349 : Bounds (33860111 / 250000000) (27088089 / 200000000) (Real.log (1145041 / 1000000)) := by
  have h := reflection_log_9349_neg
  have he : Real.log (1145041 / 1000000) = -Real.log (1000000 / 1145041) := by
    rw [show ((1145041 / 1000000) : ℝ) = ((1000000 / 1145041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9350_neg : (39175441 / 250000000) ≤ -Real.log (854959 / 1000000) ∧
    -Real.log (854959 / 1000000) ≤ (31340353 / 200000000) := by
  have h := checkLog_sound (w := (145041 / 1854959)) (n := 12)
    (lo := (39175441 / 250000000)) (hi := (31340353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854959) = 1/(854959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9350 : Bounds (-31340353 / 200000000) (-39175441 / 250000000) (Real.log (854959 / 1000000)) := by
  have h := reflection_log_9350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9351_neg : (531533 / 25000000) ≤ -Real.log (978963108319 / 1000000000000) ∧
    -Real.log (978963108319 / 1000000000000) ≤ (21261321 / 1000000000) := by
  have h := checkLog_sound (w := (21036891681 / 1978963108319)) (n := 12)
    (lo := (531533 / 25000000)) (hi := (21261321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978963108319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978963108319) = 1/(978963108319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9351 : Bounds (-21261321 / 1000000000) (-531533 / 25000000) (Real.log (978963108319 / 1000000000000)) := by
  have h := reflection_log_9351_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9352_neg : (10550367 / 500000000) ≤ -Real.log (244780081999 / 250000000000) ∧
    -Real.log (244780081999 / 250000000000) ≤ (4220147 / 200000000) := by
  have h := checkLog_sound (w := (5219918001 / 494780081999)) (n := 12)
    (lo := (10550367 / 500000000)) (hi := (4220147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244780081999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244780081999) = 1/(244780081999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9352 : Bounds (-4220147 / 200000000) (-10550367 / 500000000) (Real.log (244780081999 / 250000000000)) := by
  have h := reflection_log_9352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9353_neg : (454739 / 1562500) ≤ -Real.log (250000000000 / 334452169603) ∧
    -Real.log (250000000000 / 334452169603) ≤ (291032961 / 1000000000) := by
  have h := checkLog_sound (w := (84452169603 / 584452169603)) (n := 12)
    (lo := (454739 / 1562500)) (hi := (291032961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334452169603 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334452169603 / 250000000000) = 1/(250000000000 / 334452169603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9353 : Bounds (454739 / 1562500) (291032961 / 1000000000) (Real.log (334452169603 / 250000000000)) := by
  have h := reflection_log_9353_neg
  have he : Real.log (334452169603 / 250000000000) = -Real.log (250000000000 / 334452169603) := by
    rw [show ((334452169603 / 250000000000) : ℝ) = ((250000000000 / 334452169603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9354_neg : (2282361 / 7812500) ≤ -Real.log (250000000000 / 334823365799) ∧
    -Real.log (250000000000 / 334823365799) ≤ (292142209 / 1000000000) := by
  have h := checkLog_sound (w := (84823365799 / 584823365799)) (n := 12)
    (lo := (2282361 / 7812500)) (hi := (292142209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334823365799 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334823365799 / 250000000000) = 1/(250000000000 / 334823365799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9354 : Bounds (2282361 / 7812500) (292142209 / 1000000000) (Real.log (334823365799 / 250000000000)) := by
  have h := reflection_log_9354_neg
  have he : Real.log (334823365799 / 250000000000) = -Real.log (250000000000 / 334823365799) := by
    rw [show ((334823365799 / 250000000000) : ℝ) = ((250000000000 / 334823365799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9355_neg : (293115727 / 500000000) ≤ -Real.log (500000000000 / 898601398601) ∧
    -Real.log (500000000000 / 898601398601) ≤ (117246291 / 200000000) := by
  have h := checkLog_sound (w := (398601398601 / 1398601398601)) (n := 12)
    (lo := (293115727 / 500000000)) (hi := (117246291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((898601398601 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(898601398601 / 500000000000) = 1/(500000000000 / 898601398601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9355 : Bounds (293115727 / 500000000) (117246291 / 200000000) (Real.log (898601398601 / 500000000000)) := by
  have h := reflection_log_9355_neg
  have he : Real.log (898601398601 / 500000000000) = -Real.log (500000000000 / 898601398601) := by
    rw [show ((898601398601 / 500000000000) : ℝ) = ((500000000000 / 898601398601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9356_neg : (587320029 / 1000000000) ≤ -Real.log (500000000000 / 899580125963) ∧
    -Real.log (500000000000 / 899580125963) ≤ (58732003 / 100000000) := by
  have h := checkLog_sound (w := (399580125963 / 1399580125963)) (n := 12)
    (lo := (587320029 / 1000000000)) (hi := (58732003 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899580125963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899580125963 / 500000000000) = 1/(500000000000 / 899580125963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9356 : Bounds (587320029 / 1000000000) (58732003 / 100000000) (Real.log (899580125963 / 500000000000)) := by
  have h := reflection_log_9356_neg
  have he : Real.log (899580125963 / 500000000000) = -Real.log (500000000000 / 899580125963) := by
    rw [show ((899580125963 / 500000000000) : ℝ) = ((500000000000 / 899580125963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9357_neg : (2012293 / 8000000) ≤ -Real.log (500 / 643) ∧
    -Real.log (500 / 643) ≤ (125768313 / 500000000) := by
  have h := checkLog_sound (w := (143 / 1143)) (n := 12)
    (lo := (2012293 / 8000000)) (hi := (125768313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643 / 500) = 1/(500 / 643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9357 : Bounds (2012293 / 8000000) (125768313 / 500000000) (Real.log (643 / 500)) := by
  have h := reflection_log_9357_neg
  have he : Real.log (643 / 500) = -Real.log (500 / 643) := by
    rw [show ((643 / 500) : ℝ) = ((500 / 643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9358_neg : (84218079 / 250000000) ≤ -Real.log (357 / 500) ∧
    -Real.log (357 / 500) ≤ (336872317 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 857)) (n := 12)
    (lo := (84218079 / 250000000)) (hi := (336872317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 357) = 1/(357 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9358 : Bounds (-336872317 / 1000000000) (-84218079 / 250000000) (Real.log (357 / 500)) := by
  have h := reflection_log_9358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9359_neg : (285959 / 1000000000) ≤ -Real.log (500000 / 500143) ∧
    -Real.log (500000 / 500143) ≤ (7149 / 25000000) := by
  have h := checkLog_sound (w := (143 / 1000143)) (n := 12)
    (lo := (285959 / 1000000000)) (hi := (7149 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500143 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500143 / 500000) = 1/(500000 / 500143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9359 : Bounds (285959 / 1000000000) (7149 / 25000000) (Real.log (500143 / 500000)) := by
  have h := reflection_log_9359_neg
  have he : Real.log (500143 / 500000) = -Real.log (500000 / 500143) := by
    rw [show ((500143 / 500000) : ℝ) = ((500000 / 500143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9360_neg : (7151 / 25000000) ≤ -Real.log (499857 / 500000) ∧
    -Real.log (499857 / 500000) ≤ (286041 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 999857)) (n := 12)
    (lo := (7151 / 25000000)) (hi := (286041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499857) = 1/(499857 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9360 : Bounds (-286041 / 1000000000) (-7151 / 25000000) (Real.log (499857 / 500000)) := by
  have h := reflection_log_9360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9361_neg : (67597067 / 500000000) ≤ -Real.log (1000000 / 1144759) ∧
    -Real.log (1000000 / 1144759) ≤ (27038827 / 200000000) := by
  have h := checkLog_sound (w := (144759 / 2144759)) (n := 12)
    (lo := (67597067 / 500000000)) (hi := (27038827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1144759 / 1000000) = 1/(1000000 / 1144759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9361 : Bounds (67597067 / 500000000) (27038827 / 200000000) (Real.log (1144759 / 1000000)) := by
  have h := reflection_log_9361_neg
  have he : Real.log (1144759 / 1000000) = -Real.log (1000000 / 1144759) := by
    rw [show ((1144759 / 1000000) : ℝ) = ((1000000 / 1144759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9362_neg : (78185989 / 500000000) ≤ -Real.log (855241 / 1000000) ∧
    -Real.log (855241 / 1000000) ≤ (156371979 / 1000000000) := by
  have h := checkLog_sound (w := (144759 / 1855241)) (n := 12)
    (lo := (78185989 / 500000000)) (hi := (156371979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 855241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 855241) = 1/(855241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9362 : Bounds (-156371979 / 1000000000) (-78185989 / 500000000) (Real.log (855241 / 1000000)) := by
  have h := reflection_log_9362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9363_neg : (13566923 / 100000000) ≤ -Real.log (1000000 / 1145303) ∧
    -Real.log (1000000 / 1145303) ≤ (135669231 / 1000000000) := by
  have h := checkLog_sound (w := (145303 / 2145303)) (n := 12)
    (lo := (13566923 / 100000000)) (hi := (135669231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145303 / 1000000) = 1/(1000000 / 1145303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9363 : Bounds (13566923 / 100000000) (135669231 / 1000000000) (Real.log (1145303 / 1000000)) := by
  have h := reflection_log_9363_neg
  have he : Real.log (1145303 / 1000000) = -Real.log (1000000 / 1145303) := by
    rw [show ((1145303 / 1000000) : ℝ) = ((1000000 / 1145303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9364_neg : (78504129 / 500000000) ≤ -Real.log (854697 / 1000000) ∧
    -Real.log (854697 / 1000000) ≤ (157008259 / 1000000000) := by
  have h := checkLog_sound (w := (145303 / 1854697)) (n := 12)
    (lo := (78504129 / 500000000)) (hi := (157008259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854697) = 1/(854697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9364 : Bounds (-157008259 / 1000000000) (-78504129 / 500000000) (Real.log (854697 / 1000000)) := by
  have h := reflection_log_9364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9365_neg : (5334757 / 250000000) ≤ -Real.log (978887038191 / 1000000000000) ∧
    -Real.log (978887038191 / 1000000000000) ≤ (21339029 / 1000000000) := by
  have h := checkLog_sound (w := (21112961809 / 1978887038191)) (n := 12)
    (lo := (5334757 / 250000000)) (hi := (21339029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978887038191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978887038191) = 1/(978887038191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9365 : Bounds (-21339029 / 1000000000) (-5334757 / 250000000) (Real.log (978887038191 / 1000000000000)) := by
  have h := reflection_log_9365_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9366_neg : (21177843 / 1000000000) ≤ -Real.log (979044831919 / 1000000000000) ∧
    -Real.log (979044831919 / 1000000000000) ≤ (5294461 / 250000000) := by
  have h := checkLog_sound (w := (20955168081 / 1979044831919)) (n := 12)
    (lo := (21177843 / 1000000000)) (hi := (5294461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979044831919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979044831919) = 1/(979044831919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9366 : Bounds (-5294461 / 250000000) (-21177843 / 1000000000) (Real.log (979044831919 / 1000000000000)) := by
  have h := reflection_log_9366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9367_neg : (9111441 / 31250000) ≤ -Real.log (250000000000 / 334630531043) ∧
    -Real.log (250000000000 / 334630531043) ≤ (291566113 / 1000000000) := by
  have h := checkLog_sound (w := (84630531043 / 584630531043)) (n := 12)
    (lo := (9111441 / 31250000)) (hi := (291566113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334630531043 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334630531043 / 250000000000) = 1/(250000000000 / 334630531043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9367 : Bounds (9111441 / 31250000) (291566113 / 1000000000) (Real.log (334630531043 / 250000000000)) := by
  have h := reflection_log_9367_neg
  have he : Real.log (334630531043 / 250000000000) = -Real.log (250000000000 / 334630531043) := by
    rw [show ((334630531043 / 250000000000) : ℝ) = ((250000000000 / 334630531043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9368_neg : (292677489 / 1000000000) ≤ -Real.log (125000000000 / 167501319181) ∧
    -Real.log (125000000000 / 167501319181) ≤ (29267749 / 100000000) := by
  have h := checkLog_sound (w := (42501319181 / 292501319181)) (n := 12)
    (lo := (292677489 / 1000000000)) (hi := (29267749 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167501319181 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167501319181 / 125000000000) = 1/(125000000000 / 167501319181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9368 : Bounds (292677489 / 1000000000) (29267749 / 100000000) (Real.log (167501319181 / 125000000000)) := by
  have h := reflection_log_9368_neg
  have he : Real.log (167501319181 / 125000000000) = -Real.log (125000000000 / 167501319181) := by
    rw [show ((167501319181 / 125000000000) : ℝ) = ((125000000000 / 167501319181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9369_neg : (587320029 / 1000000000) ≤ -Real.log (250000000000 / 449790062981) ∧
    -Real.log (250000000000 / 449790062981) ≤ (58732003 / 100000000) := by
  have h := checkLog_sound (w := (199790062981 / 699790062981)) (n := 12)
    (lo := (587320029 / 1000000000)) (hi := (58732003 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449790062981 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449790062981 / 250000000000) = 1/(250000000000 / 449790062981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9369 : Bounds (587320029 / 1000000000) (58732003 / 100000000) (Real.log (449790062981 / 250000000000)) := by
  have h := reflection_log_9369_neg
  have he : Real.log (449790062981 / 250000000000) = -Real.log (250000000000 / 449790062981) := by
    rw [show ((449790062981 / 250000000000) : ℝ) = ((250000000000 / 449790062981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9370_neg : (294204471 / 500000000) ≤ -Real.log (50000000000 / 90056022409) ∧
    -Real.log (50000000000 / 90056022409) ≤ (588408943 / 1000000000) := by
  have h := checkLog_sound (w := (40056022409 / 140056022409)) (n := 12)
    (lo := (294204471 / 500000000)) (hi := (588408943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90056022409 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90056022409 / 50000000000) = 1/(50000000000 / 90056022409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9370 : Bounds (294204471 / 500000000) (588408943 / 1000000000) (Real.log (90056022409 / 50000000000)) := by
  have h := reflection_log_9370_neg
  have he : Real.log (90056022409 / 50000000000) = -Real.log (50000000000 / 90056022409) := by
    rw [show ((90056022409 / 50000000000) : ℝ) = ((50000000000 / 90056022409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9371_neg : (31490669 / 125000000) ≤ -Real.log (2000 / 2573) ∧
    -Real.log (2000 / 2573) ≤ (251925353 / 1000000000) := by
  have h := checkLog_sound (w := (573 / 4573)) (n := 12)
    (lo := (31490669 / 125000000)) (hi := (251925353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2573 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2573 / 2000) = 1/(2000 / 2573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9371 : Bounds (31490669 / 125000000) (251925353 / 1000000000) (Real.log (2573 / 2000)) := by
  have h := reflection_log_9371_neg
  have he : Real.log (2573 / 2000) = -Real.log (2000 / 2573) := by
    rw [show ((2573 / 2000) : ℝ) = ((2000 / 2573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9372_neg : (168786421 / 500000000) ≤ -Real.log (1427 / 2000) ∧
    -Real.log (1427 / 2000) ≤ (337572843 / 1000000000) := by
  have h := checkLog_sound (w := (573 / 3427)) (n := 12)
    (lo := (168786421 / 500000000)) (hi := (337572843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1427) = 1/(1427 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9372 : Bounds (-337572843 / 1000000000) (-168786421 / 500000000) (Real.log (1427 / 2000)) := by
  have h := reflection_log_9372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9373_neg : (143229 / 500000000) ≤ -Real.log (2000000 / 2000573) ∧
    -Real.log (2000000 / 2000573) ≤ (286459 / 1000000000) := by
  have h := checkLog_sound (w := (573 / 4000573)) (n := 12)
    (lo := (143229 / 500000000)) (hi := (286459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000573 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000573 / 2000000) = 1/(2000000 / 2000573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9373 : Bounds (143229 / 500000000) (286459 / 1000000000) (Real.log (2000573 / 2000000)) := by
  have h := reflection_log_9373_neg
  have he : Real.log (2000573 / 2000000) = -Real.log (2000000 / 2000573) := by
    rw [show ((2000573 / 2000000) : ℝ) = ((2000000 / 2000573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9374_neg : (286541 / 1000000000) ≤ -Real.log (1999427 / 2000000) ∧
    -Real.log (1999427 / 2000000) ≤ (143271 / 500000000) := by
  have h := checkLog_sound (w := (573 / 3999427)) (n := 12)
    (lo := (286541 / 1000000000)) (hi := (143271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999427) = 1/(1999427 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9374 : Bounds (-143271 / 500000000) (-286541 / 1000000000) (Real.log (1999427 / 2000000)) := by
  have h := reflection_log_9374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9375_neg : (16927763 / 125000000) ≤ -Real.log (50000 / 57251) ∧
    -Real.log (50000 / 57251) ≤ (27084421 / 200000000) := by
  have h := checkLog_sound (w := (7251 / 107251)) (n := 12)
    (lo := (16927763 / 125000000)) (hi := (27084421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57251 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57251 / 50000) = 1/(50000 / 57251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9375 : Bounds (16927763 / 125000000) (27084421 / 200000000) (Real.log (57251 / 50000)) := by
  have h := reflection_log_9375_neg
  have he : Real.log (57251 / 50000) = -Real.log (50000 / 57251) := by
    rw [show ((57251 / 50000) : ℝ) = ((50000 / 57251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9376_neg : (78338601 / 500000000) ≤ -Real.log (42749 / 50000) ∧
    -Real.log (42749 / 50000) ≤ (156677203 / 1000000000) := by
  have h := checkLog_sound (w := (7251 / 92749)) (n := 12)
    (lo := (78338601 / 500000000)) (hi := (156677203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42749) = 1/(42749 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9376 : Bounds (-156677203 / 1000000000) (-78338601 / 500000000) (Real.log (42749 / 50000)) := by
  have h := reflection_log_9376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9377_neg : (27179593 / 200000000) ≤ -Real.log (200000 / 229113) ∧
    -Real.log (200000 / 229113) ≤ (67948983 / 500000000) := by
  have h := checkLog_sound (w := (29113 / 429113)) (n := 12)
    (lo := (27179593 / 200000000)) (hi := (67948983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229113 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229113 / 200000) = 1/(200000 / 229113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9377 : Bounds (27179593 / 200000000) (67948983 / 500000000) (Real.log (229113 / 200000)) := by
  have h := reflection_log_9377_neg
  have he : Real.log (229113 / 200000) = -Real.log (200000 / 229113) := by
    rw [show ((229113 / 200000) : ℝ) = ((200000 / 229113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9378_neg : (157314847 / 1000000000) ≤ -Real.log (170887 / 200000) ∧
    -Real.log (170887 / 200000) ≤ (4916089 / 31250000) := by
  have h := checkLog_sound (w := (29113 / 370887)) (n := 12)
    (lo := (157314847 / 1000000000)) (hi := (4916089 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 170887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 170887) = 1/(170887 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9378 : Bounds (-4916089 / 31250000) (-157314847 / 1000000000) (Real.log (170887 / 200000)) := by
  have h := reflection_log_9378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9379_neg : (10708441 / 500000000) ≤ -Real.log (39152433231 / 40000000000) ∧
    -Real.log (39152433231 / 40000000000) ≤ (21416883 / 1000000000) := by
  have h := checkLog_sound (w := (847566769 / 79152433231)) (n := 12)
    (lo := (10708441 / 500000000)) (hi := (21416883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39152433231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39152433231) = 1/(39152433231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9379 : Bounds (-21416883 / 1000000000) (-10708441 / 500000000) (Real.log (39152433231 / 40000000000)) := by
  have h := reflection_log_9379_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9380_neg : (10627549 / 500000000) ≤ -Real.log (2447422999 / 2500000000) ∧
    -Real.log (2447422999 / 2500000000) ≤ (21255099 / 1000000000) := by
  have h := checkLog_sound (w := (52577001 / 4947422999)) (n := 12)
    (lo := (10627549 / 500000000)) (hi := (21255099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2447422999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2447422999) = 1/(2447422999 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9380 : Bounds (-21255099 / 1000000000) (-10627549 / 500000000) (Real.log (2447422999 / 2500000000)) := by
  have h := reflection_log_9380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9381_neg : (146049653 / 500000000) ≤ -Real.log (12500000000 / 16740450069) ∧
    -Real.log (12500000000 / 16740450069) ≤ (292099307 / 1000000000) := by
  have h := checkLog_sound (w := (4240450069 / 29240450069)) (n := 12)
    (lo := (146049653 / 500000000)) (hi := (292099307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16740450069 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16740450069 / 12500000000) = 1/(12500000000 / 16740450069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9381 : Bounds (146049653 / 500000000) (292099307 / 1000000000) (Real.log (16740450069 / 12500000000)) := by
  have h := reflection_log_9381_neg
  have he : Real.log (16740450069 / 12500000000) = -Real.log (12500000000 / 16740450069) := by
    rw [show ((16740450069 / 12500000000) : ℝ) = ((12500000000 / 16740450069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9382_neg : (73303203 / 250000000) ≤ -Real.log (62500000000 / 83795505217) ∧
    -Real.log (62500000000 / 83795505217) ≤ (293212813 / 1000000000) := by
  have h := checkLog_sound (w := (21295505217 / 146295505217)) (n := 12)
    (lo := (73303203 / 250000000)) (hi := (293212813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83795505217 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83795505217 / 62500000000) = 1/(62500000000 / 83795505217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9382 : Bounds (73303203 / 250000000) (293212813 / 1000000000) (Real.log (83795505217 / 62500000000)) := by
  have h := reflection_log_9382_neg
  have he : Real.log (83795505217 / 62500000000) = -Real.log (62500000000 / 83795505217) := by
    rw [show ((83795505217 / 62500000000) : ℝ) = ((62500000000 / 83795505217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9383_neg : (294204471 / 500000000) ≤ -Real.log (500000000000 / 900560224089) ∧
    -Real.log (500000000000 / 900560224089) ≤ (588408943 / 1000000000) := by
  have h := checkLog_sound (w := (400560224089 / 1400560224089)) (n := 12)
    (lo := (294204471 / 500000000)) (hi := (588408943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900560224089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900560224089 / 500000000000) = 1/(500000000000 / 900560224089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9383 : Bounds (294204471 / 500000000) (588408943 / 1000000000) (Real.log (900560224089 / 500000000000)) := by
  have h := reflection_log_9383_neg
  have he : Real.log (900560224089 / 500000000000) = -Real.log (500000000000 / 900560224089) := by
    rw [show ((900560224089 / 500000000000) : ℝ) = ((500000000000 / 900560224089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9384_neg : (294749097 / 500000000) ≤ -Real.log (250000000000 / 450770847933) ∧
    -Real.log (250000000000 / 450770847933) ≤ (117899639 / 200000000) := by
  have h := checkLog_sound (w := (200770847933 / 700770847933)) (n := 12)
    (lo := (294749097 / 500000000)) (hi := (117899639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450770847933 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450770847933 / 250000000000) = 1/(250000000000 / 450770847933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9384 : Bounds (294749097 / 500000000) (117899639 / 200000000) (Real.log (450770847933 / 250000000000)) := by
  have h := reflection_log_9384_neg
  have he : Real.log (450770847933 / 250000000000) = -Real.log (250000000000 / 450770847933) := by
    rw [show ((450770847933 / 250000000000) : ℝ) = ((250000000000 / 450770847933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9385_neg : (31539241 / 125000000) ≤ -Real.log (1000 / 1287) ∧
    -Real.log (1000 / 1287) ≤ (252313929 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 2287)) (n := 12)
    (lo := (31539241 / 125000000)) (hi := (252313929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287 / 1000) = 1/(1000 / 1287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9385 : Bounds (31539241 / 125000000) (252313929 / 1000000000) (Real.log (1287 / 1000)) := by
  have h := reflection_log_9385_neg
  have he : Real.log (1287 / 1000) = -Real.log (1000 / 1287) := by
    rw [show ((1287 / 1000) : ℝ) = ((1000 / 1287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9386_neg : (169136929 / 500000000) ≤ -Real.log (713 / 1000) ∧
    -Real.log (713 / 1000) ≤ (338273859 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 1713)) (n := 12)
    (lo := (169136929 / 500000000)) (hi := (338273859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 713) = 1/(713 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9386 : Bounds (-338273859 / 1000000000) (-169136929 / 500000000) (Real.log (713 / 1000)) := by
  have h := reflection_log_9386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9387_neg : (143479 / 500000000) ≤ -Real.log (1000000 / 1000287) ∧
    -Real.log (1000000 / 1000287) ≤ (286959 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 2000287)) (n := 12)
    (lo := (143479 / 500000000)) (hi := (286959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000287 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000287 / 1000000) = 1/(1000000 / 1000287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9387 : Bounds (143479 / 500000000) (286959 / 1000000000) (Real.log (1000287 / 1000000)) := by
  have h := reflection_log_9387_neg
  have he : Real.log (1000287 / 1000000) = -Real.log (1000000 / 1000287) := by
    rw [show ((1000287 / 1000000) : ℝ) = ((1000000 / 1000287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9388_neg : (287041 / 1000000000) ≤ -Real.log (999713 / 1000000) ∧
    -Real.log (999713 / 1000000) ≤ (143521 / 500000000) := by
  have h := checkLog_sound (w := (287 / 1999713)) (n := 12)
    (lo := (287041 / 1000000000)) (hi := (143521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999713) = 1/(999713 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9388 : Bounds (-143521 / 500000000) (-287041 / 1000000000) (Real.log (999713 / 1000000)) := by
  have h := reflection_log_9388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9389_neg : (67825447 / 500000000) ≤ -Real.log (500000 / 572641) ∧
    -Real.log (500000 / 572641) ≤ (27130179 / 200000000) := by
  have h := checkLog_sound (w := (72641 / 1072641)) (n := 12)
    (lo := (67825447 / 500000000)) (hi := (27130179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572641 / 500000) = 1/(500000 / 572641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9389 : Bounds (67825447 / 500000000) (27130179 / 200000000) (Real.log (572641 / 500000)) := by
  have h := reflection_log_9389_neg
  have he : Real.log (572641 / 500000) = -Real.log (500000 / 572641) := by
    rw [show ((572641 / 500000) : ℝ) = ((500000 / 572641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9390_neg : (156983689 / 1000000000) ≤ -Real.log (427359 / 500000) ∧
    -Real.log (427359 / 500000) ≤ (15698369 / 100000000) := by
  have h := checkLog_sound (w := (72641 / 927359)) (n := 12)
    (lo := (156983689 / 1000000000)) (hi := (15698369 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427359) = 1/(427359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9390 : Bounds (-15698369 / 100000000) (-156983689 / 1000000000) (Real.log (427359 / 500000)) := by
  have h := reflection_log_9390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9391_neg : (68062887 / 500000000) ≤ -Real.log (500000 / 572913) ∧
    -Real.log (500000 / 572913) ≤ (5445031 / 40000000) := by
  have h := checkLog_sound (w := (72913 / 1072913)) (n := 12)
    (lo := (68062887 / 500000000)) (hi := (5445031 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572913 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572913 / 500000) = 1/(500000 / 572913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9391 : Bounds (68062887 / 500000000) (5445031 / 40000000) (Real.log (572913 / 500000)) := by
  have h := reflection_log_9391_neg
  have he : Real.log (572913 / 500000) = -Real.log (500000 / 572913) := by
    rw [show ((572913 / 500000) : ℝ) = ((500000 / 572913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9392_neg : (78810179 / 500000000) ≤ -Real.log (427087 / 500000) ∧
    -Real.log (427087 / 500000) ≤ (157620359 / 1000000000) := by
  have h := checkLog_sound (w := (72913 / 927087)) (n := 12)
    (lo := (78810179 / 500000000)) (hi := (157620359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427087) = 1/(427087 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9392 : Bounds (-157620359 / 1000000000) (-78810179 / 500000000) (Real.log (427087 / 500000)) := by
  have h := reflection_log_9392_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9393_neg : (2686823 / 125000000) ≤ -Real.log (244683694431 / 250000000000) ∧
    -Real.log (244683694431 / 250000000000) ≤ (4298917 / 200000000) := by
  have h := checkLog_sound (w := (5316305569 / 494683694431)) (n := 12)
    (lo := (2686823 / 125000000)) (hi := (4298917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244683694431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244683694431) = 1/(244683694431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9393 : Bounds (-4298917 / 200000000) (-2686823 / 125000000) (Real.log (244683694431 / 250000000000)) := by
  have h := reflection_log_9393_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9394_neg : (10666397 / 500000000) ≤ -Real.log (244723285119 / 250000000000) ∧
    -Real.log (244723285119 / 250000000000) ≤ (4266559 / 200000000) := by
  have h := checkLog_sound (w := (5276714881 / 494723285119)) (n := 12)
    (lo := (10666397 / 500000000)) (hi := (4266559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244723285119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244723285119) = 1/(244723285119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9394 : Bounds (-4266559 / 200000000) (-10666397 / 500000000) (Real.log (244723285119 / 250000000000)) := by
  have h := reflection_log_9394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9395_neg : (292634583 / 1000000000) ≤ -Real.log (50000000000 / 66997653027) ∧
    -Real.log (50000000000 / 66997653027) ≤ (36579323 / 125000000) := by
  have h := checkLog_sound (w := (16997653027 / 116997653027)) (n := 12)
    (lo := (292634583 / 1000000000)) (hi := (36579323 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66997653027 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66997653027 / 50000000000) = 1/(50000000000 / 66997653027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9395 : Bounds (292634583 / 1000000000) (36579323 / 125000000) (Real.log (66997653027 / 50000000000)) := by
  have h := reflection_log_9395_neg
  have he : Real.log (66997653027 / 50000000000) = -Real.log (50000000000 / 66997653027) := by
    rw [show ((66997653027 / 50000000000) : ℝ) = ((50000000000 / 66997653027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9396_neg : (293746133 / 1000000000) ≤ -Real.log (125000000000 / 167680414061) ∧
    -Real.log (125000000000 / 167680414061) ≤ (146873067 / 500000000) := by
  have h := checkLog_sound (w := (42680414061 / 292680414061)) (n := 12)
    (lo := (293746133 / 1000000000)) (hi := (146873067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167680414061 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167680414061 / 125000000000) = 1/(125000000000 / 167680414061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9396 : Bounds (293746133 / 1000000000) (146873067 / 500000000) (Real.log (167680414061 / 125000000000)) := by
  have h := reflection_log_9396_neg
  have he : Real.log (167680414061 / 125000000000) = -Real.log (125000000000 / 167680414061) := by
    rw [show ((167680414061 / 125000000000) : ℝ) = ((125000000000 / 167680414061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9397_neg : (294749097 / 500000000) ≤ -Real.log (100000000000 / 180308339173) ∧
    -Real.log (100000000000 / 180308339173) ≤ (117899639 / 200000000) := by
  have h := checkLog_sound (w := (80308339173 / 280308339173)) (n := 12)
    (lo := (294749097 / 500000000)) (hi := (117899639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180308339173 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180308339173 / 100000000000) = 1/(100000000000 / 180308339173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9397 : Bounds (294749097 / 500000000) (117899639 / 200000000) (Real.log (180308339173 / 100000000000)) := by
  have h := reflection_log_9397_neg
  have he : Real.log (180308339173 / 100000000000) = -Real.log (100000000000 / 180308339173) := by
    rw [show ((180308339173 / 100000000000) : ℝ) = ((100000000000 / 180308339173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9398_neg : (590587787 / 1000000000) ≤ -Real.log (25000000000 / 45126227209) ∧
    -Real.log (25000000000 / 45126227209) ≤ (147646947 / 250000000) := by
  have h := checkLog_sound (w := (20126227209 / 70126227209)) (n := 12)
    (lo := (590587787 / 1000000000)) (hi := (147646947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45126227209 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45126227209 / 25000000000) = 1/(25000000000 / 45126227209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9398 : Bounds (590587787 / 1000000000) (147646947 / 250000000) (Real.log (45126227209 / 25000000000)) := by
  have h := reflection_log_9398_neg
  have he : Real.log (45126227209 / 25000000000) = -Real.log (25000000000 / 45126227209) := by
    rw [show ((45126227209 / 25000000000) : ℝ) = ((25000000000 / 45126227209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9399_neg : (252702353 / 1000000000) ≤ -Real.log (80 / 103) ∧
    -Real.log (80 / 103) ≤ (126351177 / 500000000) := by
  have h := checkLog_sound (w := (23 / 183)) (n := 12)
    (lo := (252702353 / 1000000000)) (hi := (126351177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(103 / 80) = 1/(80 / 103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9399 : Bounds (252702353 / 1000000000) (126351177 / 500000000) (Real.log (103 / 80)) := by
  have h := reflection_log_9399_neg
  have he : Real.log (103 / 80) = -Real.log (80 / 103) := by
    rw [show ((103 / 80) : ℝ) = ((80 / 103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9400_neg : (169487683 / 500000000) ≤ -Real.log (57 / 80) ∧
    -Real.log (57 / 80) ≤ (338975367 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 57) = 1/(57 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9400 : Bounds (-338975367 / 1000000000) (-169487683 / 500000000) (Real.log (57 / 80)) := by
  have h := reflection_log_9400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9401_neg : (143729 / 500000000) ≤ -Real.log (80000 / 80023) ∧
    -Real.log (80000 / 80023) ≤ (287459 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 160023)) (n := 12)
    (lo := (143729 / 500000000)) (hi := (287459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80023 / 80000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80023 / 80000) = 1/(80000 / 80023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9401 : Bounds (143729 / 500000000) (287459 / 1000000000) (Real.log (80023 / 80000)) := by
  have h := reflection_log_9401_neg
  have he : Real.log (80023 / 80000) = -Real.log (80000 / 80023) := by
    rw [show ((80023 / 80000) : ℝ) = ((80000 / 80023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9402_neg : (287541 / 1000000000) ≤ -Real.log (79977 / 80000) ∧
    -Real.log (79977 / 80000) ≤ (143771 / 500000000) := by
  have h := checkLog_sound (w := (23 / 159977)) (n := 12)
    (lo := (287541 / 1000000000)) (hi := (143771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80000 / 79977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80000 / 79977) = 1/(79977 / 80000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9402 : Bounds (-143771 / 500000000) (-287541 / 1000000000) (Real.log (79977 / 80000)) := by
  have h := reflection_log_9402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9403_neg : (3396969 / 25000000) ≤ -Real.log (1000000 / 1145543) ∧
    -Real.log (1000000 / 1145543) ≤ (135878761 / 1000000000) := by
  have h := checkLog_sound (w := (145543 / 2145543)) (n := 12)
    (lo := (3396969 / 25000000)) (hi := (135878761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145543 / 1000000) = 1/(1000000 / 1145543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9403 : Bounds (3396969 / 25000000) (135878761 / 1000000000) (Real.log (1145543 / 1000000)) := by
  have h := reflection_log_9403_neg
  have he : Real.log (1145543 / 1000000) = -Real.log (1000000 / 1145543) := by
    rw [show ((1145543 / 1000000) : ℝ) = ((1000000 / 1145543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9404_neg : (157289099 / 1000000000) ≤ -Real.log (854457 / 1000000) ∧
    -Real.log (854457 / 1000000) ≤ (1572891 / 10000000) := by
  have h := checkLog_sound (w := (145543 / 1854457)) (n := 12)
    (lo := (157289099 / 1000000000)) (hi := (1572891 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854457) = 1/(854457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9404 : Bounds (-1572891 / 10000000) (-157289099 / 1000000000) (Real.log (854457 / 1000000)) := by
  have h := reflection_log_9404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9405_neg : (34088601 / 250000000) ≤ -Real.log (125000 / 143261) ∧
    -Real.log (125000 / 143261) ≤ (27270881 / 200000000) := by
  have h := checkLog_sound (w := (18261 / 268261)) (n := 12)
    (lo := (34088601 / 250000000)) (hi := (27270881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143261 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143261 / 125000) = 1/(125000 / 143261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9405 : Bounds (34088601 / 250000000) (27270881 / 200000000) (Real.log (143261 / 125000)) := by
  have h := reflection_log_9405_neg
  have he : Real.log (143261 / 125000) = -Real.log (125000 / 143261) := by
    rw [show ((143261 / 125000) : ℝ) = ((125000 / 143261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9406_neg : (78963567 / 500000000) ≤ -Real.log (106739 / 125000) ∧
    -Real.log (106739 / 125000) ≤ (31585427 / 200000000) := by
  have h := checkLog_sound (w := (18261 / 231739)) (n := 12)
    (lo := (78963567 / 500000000)) (hi := (31585427 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106739) = 1/(106739 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9406 : Bounds (-31585427 / 200000000) (-78963567 / 500000000) (Real.log (106739 / 125000)) := by
  have h := reflection_log_9406_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9407_neg : (2157273 / 100000000) ≤ -Real.log (15291535879 / 15625000000) ∧
    -Real.log (15291535879 / 15625000000) ≤ (21572731 / 1000000000) := by
  have h := checkLog_sound (w := (333464121 / 30916535879)) (n := 12)
    (lo := (2157273 / 100000000)) (hi := (21572731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15291535879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15291535879) = 1/(15291535879 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9407 : Bounds (-21572731 / 1000000000) (-2157273 / 100000000) (Real.log (15291535879 / 15625000000)) := by
  have h := reflection_log_9407_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


