-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0055Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0055Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:27:54.708684+00:00
-- url     : https://prove2.me/theorems/1685bc1b-33ea-4ae9-9902-9c7e9efc01bd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0055Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0056Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0055Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0056Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0057Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0058Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0059Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0055Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0056Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0057Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0058Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0059Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0055Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0056Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0057Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0058Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0059Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0055Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0056Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0057Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0058Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0059Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0055Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0055
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

theorem reflection_log_1_neg : (370485389 / 1000000000) ≤ -Real.log (640 / 927) ∧
    -Real.log (640 / 927) ≤ (37048539 / 100000000) := by
  have h := checkLog_sound (w := (287 / 1567)) (n := 12)
    (lo := (370485389 / 1000000000)) (hi := (37048539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927 / 640) = 1/(640 / 927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (370485389 / 1000000000) (37048539 / 100000000) (Real.log (927 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (927 / 640) = -Real.log (640 / 927) := by
    rw [show ((927 / 640) : ℝ) = ((640 / 927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (595000119 / 1000000000) ≤ -Real.log (353 / 640) ∧
    -Real.log (353 / 640) ≤ (14875003 / 25000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 353) = 1/(353 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14875003 / 25000000) (-595000119 / 1000000000) (Real.log (353 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (92419 / 250000) ≤ -Real.log (512 / 741) ∧
    -Real.log (512 / 741) ≤ (369676001 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1253)) (n := 12)
    (lo := (92419 / 250000)) (hi := (369676001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741 / 512) = 1/(512 / 741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (92419 / 250000) (369676001 / 1000000000) (Real.log (741 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (741 / 512) = -Real.log (512 / 741) := by
    rw [show ((741 / 512) : ℝ) = ((512 / 741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (592877727 / 1000000000) ≤ -Real.log (283 / 512) ∧
    -Real.log (283 / 512) ≤ (18527429 / 31250000) := by
  have h := checkLog_sound (w := (229 / 795)) (n := 12)
    (lo := (592877727 / 1000000000)) (hi := (18527429 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 283) = 1/(283 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18527429 / 31250000) (-592877727 / 1000000000) (Real.log (283 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (128041559 / 200000000) ≤ -Real.log (320 / 607) ∧
    -Real.log (320 / 607) ≤ (160051949 / 250000000) := by
  have h := checkLog_sound (w := (287 / 927)) (n := 12)
    (lo := (128041559 / 200000000)) (hi := (160051949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607 / 320) = 1/(320 / 607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (128041559 / 200000000) (160051949 / 250000000) (Real.log (607 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (607 / 320) = -Real.log (320 / 607) := by
    rw [show ((607 / 320) : ℝ) = ((320 / 607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (283976679 / 125000000) ≤ -Real.log (33 / 320) ∧
    -Real.log (33 / 320) ≤ (567953359 / 250000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 33) = 1/(33 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-567953359 / 250000000) (-283976679 / 125000000) (Real.log (33 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (319485723 / 500000000) ≤ -Real.log (256 / 485) ∧
    -Real.log (256 / 485) ≤ (638971447 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 741)) (n := 12)
    (lo := (319485723 / 500000000)) (hi := (638971447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((485 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(485 / 256) = 1/(256 / 485) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (319485723 / 500000000) (638971447 / 1000000000) (Real.log (485 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (485 / 256) = -Real.log (256 / 485) := by
    rw [show ((485 / 256) : ℝ) = ((256 / 485) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (70291893 / 31250000) ≤ -Real.log (27 / 256) ∧
    -Real.log (27 / 256) ≤ (112467029 / 50000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(32 / 27) = 1/(27 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-112467029 / 50000000) (-70291893 / 31250000) (Real.log (27 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (51137887 / 100000000) ≤ -Real.log (1000000 / 1667589) ∧
    -Real.log (1000000 / 1667589) ≤ (511378871 / 1000000000) := by
  have h := checkLog_sound (w := (667589 / 2667589)) (n := 12)
    (lo := (51137887 / 100000000)) (hi := (511378871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1667589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1667589 / 1000000) = 1/(1000000 / 1667589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (51137887 / 100000000) (511378871 / 1000000000) (Real.log (1667589 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1667589 / 1000000) = -Real.log (1000000 / 1667589) := by
    rw [show ((1667589 / 1000000) : ℝ) = ((1000000 / 1667589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1101383123 / 1000000000) ≤ -Real.log (332411 / 1000000) ∧
    -Real.log (332411 / 1000000) ≤ (1762213 / 1600000) := by
  have h := checkLog_sound (w := (167589 / 832411)) (n := 12)
    (lo := (408235943 / 1000000000)) (hi := (51029493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 332411) = 1/(332411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1762213 / 1600000) (-1101383123 / 1000000000) (Real.log (332411 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256319589 / 500000000) ≤ -Real.log (250000 / 417423) ∧
    -Real.log (250000 / 417423) ≤ (512639179 / 1000000000) := by
  have h := checkLog_sound (w := (167423 / 667423)) (n := 12)
    (lo := (256319589 / 500000000)) (hi := (512639179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417423 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417423 / 250000) = 1/(250000 / 417423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256319589 / 500000000) (512639179 / 1000000000) (Real.log (417423 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (417423 / 250000) = -Real.log (250000 / 417423) := by
    rw [show ((417423 / 250000) : ℝ) = ((250000 / 417423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (44309189 / 40000000) ≤ -Real.log (82577 / 250000) ∧
    -Real.log (82577 / 250000) ≤ (1107729727 / 1000000000) := by
  have h := checkLog_sound (w := (42423 / 207577)) (n := 12)
    (lo := (82916509 / 200000000)) (hi := (207291273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82577) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 82577) = 1/(82577 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1107729727 / 1000000000) (-44309189 / 40000000) (Real.log (82577 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (430244221 / 1000000000) ≤ -Real.log (1000000 / 1537633) ∧
    -Real.log (1000000 / 1537633) ≤ (215122111 / 500000000) := by
  have h := checkLog_sound (w := (537633 / 2537633)) (n := 12)
    (lo := (430244221 / 1000000000)) (hi := (215122111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1537633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1537633 / 1000000) = 1/(1000000 / 1537633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (430244221 / 1000000000) (215122111 / 500000000) (Real.log (1537633 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1537633 / 1000000) = -Real.log (1000000 / 1537633) := by
    rw [show ((1537633 / 1000000) : ℝ) = ((1000000 / 1537633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (77139633 / 100000000) ≤ -Real.log (462367 / 1000000) ∧
    -Real.log (462367 / 1000000) ≤ (192849083 / 250000000) := by
  have h := checkLog_sound (w := (37633 / 962367)) (n := 12)
    (lo := (1564983 / 20000000)) (hi := (78249151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462367) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 462367) = 1/(462367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-192849083 / 250000000) (-77139633 / 100000000) (Real.log (462367 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53955593 / 125000000) ≤ -Real.log (250000 / 384947) ∧
    -Real.log (250000 / 384947) ≤ (86328949 / 200000000) := by
  have h := checkLog_sound (w := (134947 / 634947)) (n := 12)
    (lo := (53955593 / 125000000)) (hi := (86328949 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384947 / 250000) = 1/(250000 / 384947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53955593 / 125000000) (86328949 / 200000000) (Real.log (384947 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (384947 / 250000) = -Real.log (250000 / 384947) := by
    rw [show ((384947 / 250000) : ℝ) = ((250000 / 384947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31042721 / 40000000) ≤ -Real.log (115053 / 250000) ∧
    -Real.log (115053 / 250000) ≤ (776068027 / 1000000000) := by
  have h := checkLog_sound (w := (9947 / 240053)) (n := 12)
    (lo := (16584169 / 200000000)) (hi := (41460423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115053) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 115053) = 1/(115053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-776068027 / 1000000000) (-31042721 / 40000000) (Real.log (115053 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1612761993 / 1000000000) ≤ -Real.log (250000000000 / 1254162016299) ∧
    -Real.log (250000000000 / 1254162016299) ≤ (403190499 / 250000000) := by
  have h := checkLog_sound (w := (254162016299 / 2254162016299)) (n := 12)
    (lo := (226467633 / 1000000000)) (hi := (113233817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254162016299 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1254162016299 / 1000000000000) = 1/(250000000000 / 1254162016299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1612761993 / 1000000000) (403190499 / 250000000) (Real.log (1254162016299 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1254162016299 / 250000000000) = -Real.log (250000000000 / 1254162016299) := by
    rw [show ((1254162016299 / 250000000000) : ℝ) = ((250000000000 / 1254162016299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1620368903 / 1000000000) ≤ -Real.log (62500000000 / 315934673093) ∧
    -Real.log (62500000000 / 315934673093) ≤ (810184453 / 500000000) := by
  have h := checkLog_sound (w := (65934673093 / 565934673093)) (n := 12)
    (lo := (234074543 / 1000000000)) (hi := (14629659 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315934673093 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(315934673093 / 250000000000) = 1/(62500000000 / 315934673093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1620368903 / 1000000000) (810184453 / 500000000) (Real.log (315934673093 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (315934673093 / 62500000000) = -Real.log (62500000000 / 315934673093) := by
    rw [show ((315934673093 / 62500000000) : ℝ) = ((62500000000 / 315934673093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1201640551 / 1000000000) ≤ -Real.log (500000000000 / 1662784108727) ∧
    -Real.log (500000000000 / 1662784108727) ≤ (1201640553 / 1000000000) := by
  have h := checkLog_sound (w := (662784108727 / 2662784108727)) (n := 12)
    (lo := (508493371 / 1000000000)) (hi := (127123343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1662784108727 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1662784108727 / 1000000000000) = 1/(500000000000 / 1662784108727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1201640551 / 1000000000) (1201640553 / 1000000000) (Real.log (1662784108727 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1662784108727 / 500000000000) = -Real.log (500000000000 / 1662784108727) := by
    rw [show ((1662784108727 / 500000000000) : ℝ) = ((500000000000 / 1662784108727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (120771277 / 100000000) ≤ -Real.log (62500000000 / 209113951831) ∧
    -Real.log (62500000000 / 209113951831) ≤ (301928193 / 250000000) := by
  have h := checkLog_sound (w := (84113951831 / 334113951831)) (n := 12)
    (lo := (51456559 / 100000000)) (hi := (514565591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209113951831 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209113951831 / 125000000000) = 1/(62500000000 / 209113951831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (120771277 / 100000000) (301928193 / 250000000) (Real.log (209113951831 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (209113951831 / 62500000000) = -Real.log (62500000000 / 209113951831) := by
    rw [show ((209113951831 / 62500000000) : ℝ) = ((62500000000 / 209113951831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0055

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0056Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0056
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

theorem reflection_log_1_neg : (92419 / 250000) ≤ -Real.log (512 / 741) ∧
    -Real.log (512 / 741) ≤ (369676001 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1253)) (n := 12)
    (lo := (92419 / 250000)) (hi := (369676001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741 / 512) = 1/(512 / 741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (92419 / 250000) (369676001 / 1000000000) (Real.log (741 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (741 / 512) = -Real.log (512 / 741) := by
    rw [show ((741 / 512) : ℝ) = ((512 / 741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (592877727 / 1000000000) ≤ -Real.log (283 / 512) ∧
    -Real.log (283 / 512) ≤ (18527429 / 31250000) := by
  have h := checkLog_sound (w := (229 / 795)) (n := 12)
    (lo := (592877727 / 1000000000)) (hi := (18527429 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 283) = 1/(283 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18527429 / 31250000) (-592877727 / 1000000000) (Real.log (283 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73773191 / 200000000) ≤ -Real.log (1280 / 1851) ∧
    -Real.log (1280 / 1851) ≤ (92216489 / 250000000) := by
  have h := checkLog_sound (w := (571 / 3131)) (n := 12)
    (lo := (73773191 / 200000000)) (hi := (92216489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1851 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1851 / 1280) = 1/(1280 / 1851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73773191 / 200000000) (92216489 / 250000000) (Real.log (1851 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1851 / 1280) = -Real.log (1280 / 1851) := by
    rw [show ((1851 / 1280) : ℝ) = ((1280 / 1851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (59075983 / 100000000) ≤ -Real.log (709 / 1280) ∧
    -Real.log (709 / 1280) ≤ (590759831 / 1000000000) := by
  have h := checkLog_sound (w := (571 / 1989)) (n := 12)
    (lo := (59075983 / 100000000)) (hi := (590759831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 709) = 1/(709 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-590759831 / 1000000000) (-59075983 / 100000000) (Real.log (709 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (319485723 / 500000000) ≤ -Real.log (256 / 485) ∧
    -Real.log (256 / 485) ≤ (638971447 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 741)) (n := 12)
    (lo := (319485723 / 500000000)) (hi := (638971447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((485 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(485 / 256) = 1/(256 / 485) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (319485723 / 500000000) (638971447 / 1000000000) (Real.log (485 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (485 / 256) = -Real.log (256 / 485) := by
    rw [show ((485 / 256) : ℝ) = ((256 / 485) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70291893 / 31250000) ≤ -Real.log (27 / 256) ∧
    -Real.log (27 / 256) ≤ (112467029 / 50000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(32 / 27) = 1/(27 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-112467029 / 50000000) (-70291893 / 31250000) (Real.log (27 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (637733567 / 1000000000) ≤ -Real.log (640 / 1211) ∧
    -Real.log (640 / 1211) ≤ (9964587 / 15625000) := by
  have h := checkLog_sound (w := (571 / 1851)) (n := 12)
    (lo := (637733567 / 1000000000)) (hi := (9964587 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211 / 640) = 1/(640 / 1211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (637733567 / 1000000000) (9964587 / 15625000) (Real.log (1211 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1211 / 640) = -Real.log (640 / 1211) := by
    rw [show ((1211 / 640) : ℝ) = ((640 / 1211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (222736167 / 100000000) ≤ -Real.log (69 / 640) ∧
    -Real.log (69 / 640) ≤ (1113680837 / 500000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 69) = 1/(69 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1113680837 / 500000000) (-222736167 / 100000000) (Real.log (69 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (20404847 / 40000000) ≤ -Real.log (1000000 / 1665493) ∧
    -Real.log (1000000 / 1665493) ≤ (63765147 / 125000000) := by
  have h := checkLog_sound (w := (665493 / 2665493)) (n := 12)
    (lo := (20404847 / 40000000)) (hi := (63765147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1665493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1665493 / 1000000) = 1/(1000000 / 1665493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (20404847 / 40000000) (63765147 / 125000000) (Real.log (1665493 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1665493 / 1000000) = -Real.log (1000000 / 1665493) := by
    rw [show ((1665493 / 1000000) : ℝ) = ((1000000 / 1665493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8555449 / 7812500) ≤ -Real.log (334507 / 1000000) ∧
    -Real.log (334507 / 1000000) ≤ (547548737 / 500000000) := by
  have h := checkLog_sound (w := (165493 / 834507)) (n := 12)
    (lo := (100487573 / 250000000)) (hi := (401950293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 334507) = 1/(334507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-547548737 / 500000000) (-8555449 / 7812500) (Real.log (334507 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51137947 / 100000000) ≤ -Real.log (100000 / 166759) ∧
    -Real.log (100000 / 166759) ≤ (511379471 / 1000000000) := by
  have h := checkLog_sound (w := (66759 / 266759)) (n := 12)
    (lo := (51137947 / 100000000)) (hi := (511379471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166759 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166759 / 100000) = 1/(100000 / 166759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51137947 / 100000000) (511379471 / 1000000000) (Real.log (166759 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (166759 / 100000) = -Real.log (100000 / 166759) := by
    rw [show ((166759 / 100000) : ℝ) = ((100000 / 166759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1101386131 / 1000000000) ≤ -Real.log (33241 / 100000) ∧
    -Real.log (33241 / 100000) ≤ (1101386133 / 1000000000) := by
  have h := checkLog_sound (w := (16759 / 83241)) (n := 12)
    (lo := (408238951 / 1000000000)) (hi := (51029869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33241) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 33241) = 1/(33241 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1101386133 / 1000000000) (-1101386131 / 1000000000) (Real.log (33241 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (428850199 / 1000000000) ≤ -Real.log (1000000 / 1535491) ∧
    -Real.log (1000000 / 1535491) ≤ (2144251 / 5000000) := by
  have h := checkLog_sound (w := (535491 / 2535491)) (n := 12)
    (lo := (428850199 / 1000000000)) (hi := (2144251 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1535491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1535491 / 1000000) = 1/(1000000 / 1535491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (428850199 / 1000000000) (2144251 / 5000000) (Real.log (1535491 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1535491 / 1000000) = -Real.log (1000000 / 1535491) := by
    rw [show ((1535491 / 1000000) : ℝ) = ((1000000 / 1535491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (95846793 / 125000000) ≤ -Real.log (464509 / 1000000) ∧
    -Real.log (464509 / 1000000) ≤ (383387173 / 500000000) := by
  have h := checkLog_sound (w := (35491 / 964509)) (n := 12)
    (lo := (18406791 / 250000000)) (hi := (14725433 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 464509) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 464509) = 1/(464509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-383387173 / 500000000) (-95846793 / 125000000) (Real.log (464509 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (430244871 / 1000000000) ≤ -Real.log (500000 / 768817) ∧
    -Real.log (500000 / 768817) ≤ (53780609 / 125000000) := by
  have h := checkLog_sound (w := (268817 / 1268817)) (n := 12)
    (lo := (430244871 / 1000000000)) (hi := (53780609 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768817 / 500000) = 1/(500000 / 768817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (430244871 / 1000000000) (53780609 / 125000000) (Real.log (768817 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (768817 / 500000) = -Real.log (500000 / 768817) := by
    rw [show ((768817 / 500000) : ℝ) = ((500000 / 768817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (771398493 / 1000000000) ≤ -Real.log (231183 / 500000) ∧
    -Real.log (231183 / 500000) ≤ (154279699 / 200000000) := by
  have h := checkLog_sound (w := (18817 / 481183)) (n := 12)
    (lo := (78251313 / 1000000000)) (hi := (39125657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 231183) = 1/(231183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-154279699 / 200000000) (-771398493 / 1000000000) (Real.log (231183 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1605218647 / 1000000000) ≤ -Real.log (125000000000 / 622368515457) ∧
    -Real.log (125000000000 / 622368515457) ≤ (32104373 / 20000000) := by
  have h := checkLog_sound (w := (122368515457 / 1122368515457)) (n := 12)
    (lo := (218924287 / 1000000000)) (hi := (855173 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622368515457 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(622368515457 / 500000000000) = 1/(125000000000 / 622368515457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1605218647 / 1000000000) (32104373 / 20000000) (Real.log (622368515457 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (622368515457 / 125000000000) = -Real.log (125000000000 / 622368515457) := by
    rw [show ((622368515457 / 125000000000) : ℝ) = ((125000000000 / 622368515457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1612765601 / 1000000000) ≤ -Real.log (500000000000 / 2508333082639) ∧
    -Real.log (500000000000 / 2508333082639) ≤ (403191401 / 250000000) := by
  have h := checkLog_sound (w := (508333082639 / 4508333082639)) (n := 12)
    (lo := (226471241 / 1000000000)) (hi := (113235621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2508333082639 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2508333082639 / 2000000000000) = 1/(500000000000 / 2508333082639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1612765601 / 1000000000) (403191401 / 250000000) (Real.log (2508333082639 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2508333082639 / 500000000000) = -Real.log (500000000000 / 2508333082639) := by
    rw [show ((2508333082639 / 500000000000) : ℝ) = ((500000000000 / 2508333082639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (37363267 / 31250000) ≤ -Real.log (500000000000 / 1652810817443) ∧
    -Real.log (500000000000 / 1652810817443) ≤ (597812273 / 500000000) := by
  have h := checkLog_sound (w := (652810817443 / 2652810817443)) (n := 12)
    (lo := (125619341 / 250000000)) (hi := (100495473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652810817443 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1652810817443 / 1000000000000) = 1/(500000000000 / 1652810817443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (37363267 / 31250000) (597812273 / 500000000) (Real.log (1652810817443 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1652810817443 / 500000000000) = -Real.log (500000000000 / 1652810817443) := by
    rw [show ((1652810817443 / 500000000000) : ℝ) = ((500000000000 / 1652810817443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (300410841 / 250000000) ≤ -Real.log (500000000000 / 1662788786373) ∧
    -Real.log (500000000000 / 1662788786373) ≤ (600821683 / 500000000) := by
  have h := checkLog_sound (w := (662788786373 / 2662788786373)) (n := 12)
    (lo := (63562023 / 125000000)) (hi := (101699237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1662788786373 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1662788786373 / 1000000000000) = 1/(500000000000 / 1662788786373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (300410841 / 250000000) (600821683 / 500000000) (Real.log (1662788786373 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1662788786373 / 500000000000) = -Real.log (500000000000 / 1662788786373) := by
    rw [show ((1662788786373 / 500000000000) : ℝ) = ((500000000000 / 1662788786373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0056

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0057Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0057
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

theorem reflection_log_1_neg : (73773191 / 200000000) ≤ -Real.log (1280 / 1851) ∧
    -Real.log (1280 / 1851) ≤ (92216489 / 250000000) := by
  have h := checkLog_sound (w := (571 / 3131)) (n := 12)
    (lo := (73773191 / 200000000)) (hi := (92216489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1851 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1851 / 1280) = 1/(1280 / 1851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73773191 / 200000000) (92216489 / 250000000) (Real.log (1851 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1851 / 1280) = -Real.log (1280 / 1851) := by
    rw [show ((1851 / 1280) : ℝ) = ((1280 / 1851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (59075983 / 100000000) ≤ -Real.log (709 / 1280) ∧
    -Real.log (709 / 1280) ≤ (590759831 / 1000000000) := by
  have h := checkLog_sound (w := (571 / 1989)) (n := 12)
    (lo := (59075983 / 100000000)) (hi := (590759831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 709) = 1/(709 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-590759831 / 1000000000) (-59075983 / 100000000) (Real.log (709 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (184027627 / 500000000) ≤ -Real.log (2560 / 3699) ∧
    -Real.log (2560 / 3699) ≤ (73611051 / 200000000) := by
  have h := checkLog_sound (w := (1139 / 6259)) (n := 12)
    (lo := (184027627 / 500000000)) (hi := (73611051 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3699 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3699 / 2560) = 1/(2560 / 3699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (184027627 / 500000000) (73611051 / 200000000) (Real.log (3699 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3699 / 2560) = -Real.log (2560 / 3699) := by
    rw [show ((3699 / 2560) : ℝ) = ((2560 / 3699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (588646409 / 1000000000) ≤ -Real.log (1421 / 2560) ∧
    -Real.log (1421 / 2560) ≤ (58864641 / 100000000) := by
  have h := checkLog_sound (w := (1139 / 3981)) (n := 12)
    (lo := (588646409 / 1000000000)) (hi := (58864641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1421) = 1/(1421 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58864641 / 100000000) (-588646409 / 1000000000) (Real.log (1421 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (637733567 / 1000000000) ≤ -Real.log (640 / 1211) ∧
    -Real.log (640 / 1211) ≤ (9964587 / 15625000) := by
  have h := checkLog_sound (w := (571 / 1851)) (n := 12)
    (lo := (637733567 / 1000000000)) (hi := (9964587 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211 / 640) = 1/(640 / 1211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (637733567 / 1000000000) (9964587 / 15625000) (Real.log (1211 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1211 / 640) = -Real.log (640 / 1211) := by
    rw [show ((1211 / 640) : ℝ) = ((640 / 1211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (222736167 / 100000000) ≤ -Real.log (69 / 640) ∧
    -Real.log (69 / 640) ≤ (1113680837 / 500000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 69) = 1/(69 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1113680837 / 500000000) (-222736167 / 100000000) (Real.log (69 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (636494153 / 1000000000) ≤ -Real.log (1280 / 2419) ∧
    -Real.log (1280 / 2419) ≤ (318247077 / 500000000) := by
  have h := checkLog_sound (w := (1139 / 3699)) (n := 12)
    (lo := (636494153 / 1000000000)) (hi := (318247077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2419 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2419 / 1280) = 1/(1280 / 2419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (636494153 / 1000000000) (318247077 / 500000000) (Real.log (2419 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2419 / 1280) = -Real.log (1280 / 2419) := by
    rw [show ((2419 / 1280) : ℝ) = ((1280 / 2419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (275731933 / 125000000) ≤ -Real.log (141 / 1280) ∧
    -Real.log (141 / 1280) ≤ (551463867 / 250000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 141) = 1/(141 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-551463867 / 250000000) (-275731933 / 125000000) (Real.log (141 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (254433353 / 500000000) ≤ -Real.log (200000 / 332681) ∧
    -Real.log (200000 / 332681) ≤ (508866707 / 1000000000) := by
  have h := checkLog_sound (w := (132681 / 532681)) (n := 12)
    (lo := (254433353 / 500000000)) (hi := (508866707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332681 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332681 / 200000) = 1/(200000 / 332681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (254433353 / 500000000) (508866707 / 1000000000) (Real.log (332681 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (332681 / 200000) = -Real.log (200000 / 332681) := by
    rw [show ((332681 / 200000) : ℝ) = ((200000 / 332681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1088874851 / 1000000000) ≤ -Real.log (67319 / 200000) ∧
    -Real.log (67319 / 200000) ≤ (1088874853 / 1000000000) := by
  have h := checkLog_sound (w := (32681 / 167319)) (n := 12)
    (lo := (395727671 / 1000000000)) (hi := (49465959 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 67319) = 1/(67319 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1088874853 / 1000000000) (-1088874851 / 1000000000) (Real.log (67319 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (63765297 / 125000000) ≤ -Real.log (200000 / 333099) ∧
    -Real.log (200000 / 333099) ≤ (510122377 / 1000000000) := by
  have h := checkLog_sound (w := (133099 / 533099)) (n := 12)
    (lo := (63765297 / 125000000)) (hi := (510122377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333099 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333099 / 200000) = 1/(200000 / 333099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (63765297 / 125000000) (510122377 / 1000000000) (Real.log (333099 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (333099 / 200000) = -Real.log (200000 / 333099) := by
    rw [show ((333099 / 200000) : ℝ) = ((200000 / 333099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1095103451 / 1000000000) ≤ -Real.log (66901 / 200000) ∧
    -Real.log (66901 / 200000) ≤ (1095103453 / 1000000000) := by
  have h := checkLog_sound (w := (33099 / 166901)) (n := 12)
    (lo := (401956271 / 1000000000)) (hi := (25122267 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66901) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 66901) = 1/(66901 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1095103453 / 1000000000) (-1095103451 / 1000000000) (Real.log (66901 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (213731029 / 500000000) ≤ -Real.log (1000000 / 1533361) ∧
    -Real.log (1000000 / 1533361) ≤ (427462059 / 1000000000) := by
  have h := checkLog_sound (w := (533361 / 2533361)) (n := 12)
    (lo := (213731029 / 500000000)) (hi := (427462059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1533361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1533361 / 1000000) = 1/(1000000 / 1533361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (213731029 / 500000000) (427462059 / 1000000000) (Real.log (1533361 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1533361 / 1000000) = -Real.log (1000000 / 1533361) := by
    rw [show ((1533361 / 1000000) : ℝ) = ((1000000 / 1533361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (381099669 / 500000000) ≤ -Real.log (466639 / 1000000) ∧
    -Real.log (466639 / 1000000) ≤ (38109967 / 50000000) := by
  have h := checkLog_sound (w := (33361 / 966639)) (n := 12)
    (lo := (34526079 / 500000000)) (hi := (69052159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 466639) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 466639) = 1/(466639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38109967 / 50000000) (-381099669 / 500000000) (Real.log (466639 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (8577017 / 20000000) ≤ -Real.log (250000 / 383873) ∧
    -Real.log (250000 / 383873) ≤ (428850851 / 1000000000) := by
  have h := checkLog_sound (w := (133873 / 633873)) (n := 12)
    (lo := (8577017 / 20000000)) (hi := (428850851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383873 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383873 / 250000) = 1/(250000 / 383873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (8577017 / 20000000) (428850851 / 1000000000) (Real.log (383873 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (383873 / 250000) = -Real.log (250000 / 383873) := by
    rw [show ((383873 / 250000) : ℝ) = ((250000 / 383873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (766776497 / 1000000000) ≤ -Real.log (116127 / 250000) ∧
    -Real.log (116127 / 250000) ≤ (766776499 / 1000000000) := by
  have h := checkLog_sound (w := (8873 / 241127)) (n := 12)
    (lo := (73629317 / 1000000000)) (hi := (36814659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 116127) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 116127) = 1/(116127 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-766776499 / 1000000000) (-766776497 / 1000000000) (Real.log (116127 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (399435389 / 250000000) ≤ -Real.log (6250000000 / 30886618191) ∧
    -Real.log (6250000000 / 30886618191) ≤ (1597741559 / 1000000000) := by
  have h := checkLog_sound (w := (5886618191 / 55886618191)) (n := 12)
    (lo := (52861799 / 250000000)) (hi := (211447197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30886618191 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(30886618191 / 25000000000) = 1/(6250000000 / 30886618191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (399435389 / 250000000) (1597741559 / 1000000000) (Real.log (30886618191 / 6250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (30886618191 / 6250000000) = -Real.log (6250000000 / 30886618191) := by
    rw [show ((30886618191 / 6250000000) : ℝ) = ((6250000000 / 30886618191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1605225827 / 1000000000) ≤ -Real.log (250000000000 / 1244745967923) ∧
    -Real.log (250000000000 / 1244745967923) ≤ (160522583 / 100000000) := by
  have h := checkLog_sound (w := (244745967923 / 2244745967923)) (n := 12)
    (lo := (218931467 / 1000000000)) (hi := (54732867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244745967923 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1244745967923 / 1000000000000) = 1/(250000000000 / 1244745967923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1605225827 / 1000000000) (160522583 / 100000000) (Real.log (1244745967923 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1244745967923 / 250000000000) = -Real.log (250000000000 / 1244745967923) := by
    rw [show ((1244745967923 / 250000000000) : ℝ) = ((250000000000 / 1244745967923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1189661397 / 1000000000) ≤ -Real.log (100000000000 / 328596838241) ∧
    -Real.log (100000000000 / 328596838241) ≤ (1189661399 / 1000000000) := by
  have h := checkLog_sound (w := (128596838241 / 528596838241)) (n := 12)
    (lo := (496514217 / 1000000000)) (hi := (248257109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328596838241 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(328596838241 / 200000000000) = 1/(100000000000 / 328596838241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1189661397 / 1000000000) (1189661399 / 1000000000) (Real.log (328596838241 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (328596838241 / 100000000000) = -Real.log (100000000000 / 328596838241) := by
    rw [show ((328596838241 / 100000000000) : ℝ) = ((100000000000 / 328596838241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (298906837 / 250000000) ≤ -Real.log (500000000000 / 1652815452049) ∧
    -Real.log (500000000000 / 1652815452049) ≤ (23912547 / 20000000) := by
  have h := checkLog_sound (w := (652815452049 / 2652815452049)) (n := 12)
    (lo := (62810021 / 125000000)) (hi := (502480169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652815452049 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1652815452049 / 1000000000000) = 1/(500000000000 / 1652815452049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (298906837 / 250000000) (23912547 / 20000000) (Real.log (1652815452049 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1652815452049 / 500000000000) = -Real.log (500000000000 / 1652815452049) := by
    rw [show ((1652815452049 / 500000000000) : ℝ) = ((500000000000 / 1652815452049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0057

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0058Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0058
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

theorem reflection_log_1_neg : (184027627 / 500000000) ≤ -Real.log (2560 / 3699) ∧
    -Real.log (2560 / 3699) ≤ (73611051 / 200000000) := by
  have h := checkLog_sound (w := (1139 / 6259)) (n := 12)
    (lo := (184027627 / 500000000)) (hi := (73611051 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3699 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3699 / 2560) = 1/(2560 / 3699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (184027627 / 500000000) (73611051 / 200000000) (Real.log (3699 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3699 / 2560) = -Real.log (2560 / 3699) := by
    rw [show ((3699 / 2560) : ℝ) = ((2560 / 3699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (588646409 / 1000000000) ≤ -Real.log (1421 / 2560) ∧
    -Real.log (1421 / 2560) ≤ (58864641 / 100000000) := by
  have h := checkLog_sound (w := (1139 / 3981)) (n := 12)
    (lo := (588646409 / 1000000000)) (hi := (58864641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1421) = 1/(1421 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58864641 / 100000000) (-588646409 / 1000000000) (Real.log (1421 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73448779 / 200000000) ≤ -Real.log (160 / 231) ∧
    -Real.log (160 / 231) ≤ (45905487 / 125000000) := by
  have h := checkLog_sound (w := (71 / 391)) (n := 12)
    (lo := (73448779 / 200000000)) (hi := (45905487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231 / 160) = 1/(160 / 231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73448779 / 200000000) (45905487 / 125000000) (Real.log (231 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (231 / 160) = -Real.log (160 / 231) := by
    rw [show ((231 / 160) : ℝ) = ((160 / 231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (117307489 / 200000000) ≤ -Real.log (89 / 160) ∧
    -Real.log (89 / 160) ≤ (293268723 / 500000000) := by
  have h := checkLog_sound (w := (71 / 249)) (n := 12)
    (lo := (117307489 / 200000000)) (hi := (293268723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 89) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 89) = 1/(89 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-293268723 / 500000000) (-117307489 / 200000000) (Real.log (89 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (636494153 / 1000000000) ≤ -Real.log (1280 / 2419) ∧
    -Real.log (1280 / 2419) ≤ (318247077 / 500000000) := by
  have h := checkLog_sound (w := (1139 / 3699)) (n := 12)
    (lo := (636494153 / 1000000000)) (hi := (318247077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2419 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2419 / 1280) = 1/(1280 / 2419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (636494153 / 1000000000) (318247077 / 500000000) (Real.log (2419 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2419 / 1280) = -Real.log (1280 / 2419) := by
    rw [show ((2419 / 1280) : ℝ) = ((1280 / 2419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (275731933 / 125000000) ≤ -Real.log (141 / 1280) ∧
    -Real.log (141 / 1280) ≤ (551463867 / 250000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 141) = 1/(141 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-551463867 / 250000000) (-275731933 / 125000000) (Real.log (141 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (317626601 / 500000000) ≤ -Real.log (80 / 151) ∧
    -Real.log (80 / 151) ≤ (635253203 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 231)) (n := 12)
    (lo := (317626601 / 500000000)) (hi := (635253203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151 / 80) = 1/(80 / 151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (317626601 / 500000000) (635253203 / 1000000000) (Real.log (151 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (151 / 80) = -Real.log (80 / 151) := by
    rw [show ((151 / 80) : ℝ) = ((80 / 151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (436960411 / 200000000) ≤ -Real.log (9 / 80) ∧
    -Real.log (9 / 80) ≤ (2184802059 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(10 / 9) = 1/(9 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2184802059 / 1000000000) (-436960411 / 200000000) (Real.log (9 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (253807437 / 500000000) ≤ -Real.log (250000 / 415331) ∧
    -Real.log (250000 / 415331) ≤ (4060919 / 8000000) := by
  have h := checkLog_sound (w := (165331 / 665331)) (n := 12)
    (lo := (253807437 / 500000000)) (hi := (4060919 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415331 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415331 / 250000) = 1/(250000 / 415331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (253807437 / 500000000) (4060919 / 8000000) (Real.log (415331 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (415331 / 250000) = -Real.log (250000 / 415331) := by
    rw [show ((415331 / 250000) : ℝ) = ((250000 / 415331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (54135569 / 50000000) ≤ -Real.log (84669 / 250000) ∧
    -Real.log (84669 / 250000) ≤ (541355691 / 500000000) := by
  have h := checkLog_sound (w := (40331 / 209669)) (n := 12)
    (lo := (1947821 / 5000000)) (hi := (389564201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84669) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 84669) = 1/(84669 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-541355691 / 500000000) (-54135569 / 50000000) (Real.log (84669 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (508867307 / 1000000000) ≤ -Real.log (500000 / 831703) ∧
    -Real.log (500000 / 831703) ≤ (127216827 / 250000000) := by
  have h := checkLog_sound (w := (331703 / 1331703)) (n := 12)
    (lo := (508867307 / 1000000000)) (hi := (127216827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831703 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831703 / 500000) = 1/(500000 / 831703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (508867307 / 1000000000) (127216827 / 250000000) (Real.log (831703 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (831703 / 500000) = -Real.log (500000 / 831703) := by
    rw [show ((831703 / 500000) : ℝ) = ((500000 / 831703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (544438911 / 500000000) ≤ -Real.log (168297 / 500000) ∧
    -Real.log (168297 / 500000) ≤ (4253429 / 3906250) := by
  have h := checkLog_sound (w := (81703 / 418297)) (n := 12)
    (lo := (197865321 / 500000000)) (hi := (395730643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 168297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 168297) = 1/(168297 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4253429 / 3906250) (-544438911 / 500000000) (Real.log (168297 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (42607917 / 100000000) ≤ -Real.log (500000 / 765621) ∧
    -Real.log (500000 / 765621) ≤ (426079171 / 1000000000) := by
  have h := checkLog_sound (w := (265621 / 1265621)) (n := 12)
    (lo := (42607917 / 100000000)) (hi := (426079171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765621 / 500000) = 1/(500000 / 765621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (42607917 / 100000000) (426079171 / 1000000000) (Real.log (765621 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (765621 / 500000) = -Real.log (500000 / 765621) := by
    rw [show ((765621 / 500000) : ℝ) = ((500000 / 765621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (378834317 / 500000000) ≤ -Real.log (234379 / 500000) ∧
    -Real.log (234379 / 500000) ≤ (189417159 / 250000000) := by
  have h := checkLog_sound (w := (15621 / 484379)) (n := 12)
    (lo := (32260727 / 500000000)) (hi := (12904291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 234379) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 234379) = 1/(234379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-189417159 / 250000000) (-378834317 / 500000000) (Real.log (234379 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42746271 / 100000000) ≤ -Real.log (500000 / 766681) ∧
    -Real.log (500000 / 766681) ≤ (427462711 / 1000000000) := by
  have h := checkLog_sound (w := (266681 / 1266681)) (n := 12)
    (lo := (42746271 / 100000000)) (hi := (427462711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766681 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(766681 / 500000) = 1/(500000 / 766681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42746271 / 100000000) (427462711 / 1000000000) (Real.log (766681 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (766681 / 500000) = -Real.log (500000 / 766681) := by
    rw [show ((766681 / 500000) : ℝ) = ((500000 / 766681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (762201481 / 1000000000) ≤ -Real.log (233319 / 500000) ∧
    -Real.log (233319 / 500000) ≤ (762201483 / 1000000000) := by
  have h := checkLog_sound (w := (16681 / 483319)) (n := 12)
    (lo := (69054301 / 1000000000)) (hi := (34527151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 233319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 233319) = 1/(233319 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-762201483 / 1000000000) (-762201481 / 1000000000) (Real.log (233319 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (795163127 / 500000000) ≤ -Real.log (500000000000 / 2452674532591) ∧
    -Real.log (500000000000 / 2452674532591) ≤ (1590326257 / 1000000000) := by
  have h := checkLog_sound (w := (452674532591 / 4452674532591)) (n := 12)
    (lo := (102015947 / 500000000)) (hi := (40806379 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2452674532591 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2452674532591 / 2000000000000) = 1/(500000000000 / 2452674532591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (795163127 / 500000000) (1590326257 / 1000000000) (Real.log (2452674532591 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2452674532591 / 500000000000) = -Real.log (500000000000 / 2452674532591) := by
    rw [show ((2452674532591 / 500000000000) : ℝ) = ((500000000000 / 2452674532591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1597745129 / 1000000000) ≤ -Real.log (500000000000 / 2470938281729) ∧
    -Real.log (500000000000 / 2470938281729) ≤ (399436283 / 250000000) := by
  have h := checkLog_sound (w := (470938281729 / 4470938281729)) (n := 12)
    (lo := (211450769 / 1000000000)) (hi := (21145077 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2470938281729 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2470938281729 / 2000000000000) = 1/(500000000000 / 2470938281729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1597745129 / 1000000000) (399436283 / 250000000) (Real.log (2470938281729 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2470938281729 / 500000000000) = -Real.log (500000000000 / 2470938281729) := by
    rw [show ((2470938281729 / 500000000000) : ℝ) = ((500000000000 / 2470938281729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (236749561 / 200000000) ≤ -Real.log (100000000000 / 326659385013) ∧
    -Real.log (100000000000 / 326659385013) ≤ (1183747807 / 1000000000) := by
  have h := checkLog_sound (w := (126659385013 / 526659385013)) (n := 12)
    (lo := (784961 / 1600000)) (hi := (245300313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326659385013 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(326659385013 / 200000000000) = 1/(100000000000 / 326659385013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (236749561 / 200000000) (1183747807 / 1000000000) (Real.log (326659385013 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (326659385013 / 100000000000) = -Real.log (100000000000 / 326659385013) := by
    rw [show ((326659385013 / 100000000000) : ℝ) = ((100000000000 / 326659385013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18588503 / 15625000) ≤ -Real.log (500000000000 / 1642988783597) ∧
    -Real.log (500000000000 / 1642988783597) ≤ (594832097 / 500000000) := by
  have h := checkLog_sound (w := (642988783597 / 2642988783597)) (n := 12)
    (lo := (124129253 / 250000000)) (hi := (496517013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642988783597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1642988783597 / 1000000000000) = 1/(500000000000 / 1642988783597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18588503 / 15625000) (594832097 / 500000000) (Real.log (1642988783597 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1642988783597 / 500000000000) = -Real.log (500000000000 / 1642988783597) := by
    rw [show ((1642988783597 / 500000000000) : ℝ) = ((500000000000 / 1642988783597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0058

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0059Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0059
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

theorem reflection_log_1_neg : (73448779 / 200000000) ≤ -Real.log (160 / 231) ∧
    -Real.log (160 / 231) ≤ (45905487 / 125000000) := by
  have h := checkLog_sound (w := (71 / 391)) (n := 12)
    (lo := (73448779 / 200000000)) (hi := (45905487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231 / 160) = 1/(160 / 231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73448779 / 200000000) (45905487 / 125000000) (Real.log (231 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (231 / 160) = -Real.log (160 / 231) := by
    rw [show ((231 / 160) : ℝ) = ((160 / 231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (117307489 / 200000000) ≤ -Real.log (89 / 160) ∧
    -Real.log (89 / 160) ≤ (293268723 / 500000000) := by
  have h := checkLog_sound (w := (71 / 249)) (n := 12)
    (lo := (117307489 / 200000000)) (hi := (293268723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 89) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 89) = 1/(89 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-293268723 / 500000000) (-117307489 / 200000000) (Real.log (89 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (366431877 / 1000000000) ≤ -Real.log (2560 / 3693) ∧
    -Real.log (2560 / 3693) ≤ (183215939 / 500000000) := by
  have h := checkLog_sound (w := (1133 / 6253)) (n := 12)
    (lo := (366431877 / 1000000000)) (hi := (183215939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3693 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3693 / 2560) = 1/(2560 / 3693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (366431877 / 1000000000) (183215939 / 500000000) (Real.log (3693 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3693 / 2560) = -Real.log (2560 / 3693) := by
    rw [show ((3693 / 2560) : ℝ) = ((2560 / 3693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (584432919 / 1000000000) ≤ -Real.log (1427 / 2560) ∧
    -Real.log (1427 / 2560) ≤ (14610823 / 25000000) := by
  have h := checkLog_sound (w := (1133 / 3987)) (n := 12)
    (lo := (584432919 / 1000000000)) (hi := (14610823 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1427) = 1/(1427 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14610823 / 25000000) (-584432919 / 1000000000) (Real.log (1427 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (317626601 / 500000000) ≤ -Real.log (80 / 151) ∧
    -Real.log (80 / 151) ≤ (635253203 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 231)) (n := 12)
    (lo := (317626601 / 500000000)) (hi := (635253203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151 / 80) = 1/(80 / 151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (317626601 / 500000000) (635253203 / 1000000000) (Real.log (151 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (151 / 80) = -Real.log (80 / 151) := by
    rw [show ((151 / 80) : ℝ) = ((80 / 151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (436960411 / 200000000) ≤ -Real.log (9 / 80) ∧
    -Real.log (9 / 80) ≤ (2184802059 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(10 / 9) = 1/(9 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2184802059 / 1000000000) (-436960411 / 200000000) (Real.log (9 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (158502677 / 250000000) ≤ -Real.log (1280 / 2413) ∧
    -Real.log (1280 / 2413) ≤ (634010709 / 1000000000) := by
  have h := checkLog_sound (w := (1133 / 3693)) (n := 12)
    (lo := (158502677 / 250000000)) (hi := (634010709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2413 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2413 / 1280) = 1/(1280 / 2413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (158502677 / 250000000) (634010709 / 1000000000) (Real.log (2413 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2413 / 1280) = -Real.log (1280 / 2413) := by
    rw [show ((2413 / 1280) : ℝ) = ((1280 / 2413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (135261423 / 62500000) ≤ -Real.log (147 / 1280) ∧
    -Real.log (147 / 1280) ≤ (541045693 / 250000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 147) = 1/(147 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-541045693 / 250000000) (-135261423 / 62500000) (Real.log (147 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (50636509 / 100000000) ≤ -Real.log (1000000 / 1659249) ∧
    -Real.log (1000000 / 1659249) ≤ (506365091 / 1000000000) := by
  have h := checkLog_sound (w := (659249 / 2659249)) (n := 12)
    (lo := (50636509 / 100000000)) (hi := (506365091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1659249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1659249 / 1000000) = 1/(1000000 / 1659249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (50636509 / 100000000) (506365091 / 1000000000) (Real.log (1659249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1659249 / 1000000) = -Real.log (1000000 / 1659249) := by
    rw [show ((1659249 / 1000000) : ℝ) = ((1000000 / 1659249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1076603273 / 1000000000) ≤ -Real.log (340751 / 1000000) ∧
    -Real.log (340751 / 1000000) ≤ (43064131 / 40000000) := by
  have h := checkLog_sound (w := (159249 / 840751)) (n := 12)
    (lo := (383456093 / 1000000000)) (hi := (191728047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340751) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 340751) = 1/(340751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43064131 / 40000000) (-1076603273 / 1000000000) (Real.log (340751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126903869 / 250000000) ≤ -Real.log (40000 / 66453) ∧
    -Real.log (40000 / 66453) ≤ (507615477 / 1000000000) := by
  have h := checkLog_sound (w := (26453 / 106453)) (n := 12)
    (lo := (126903869 / 250000000)) (hi := (507615477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66453 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66453 / 40000) = 1/(40000 / 66453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126903869 / 250000000) (507615477 / 1000000000) (Real.log (66453 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (66453 / 40000) = -Real.log (40000 / 66453) := by
    rw [show ((66453 / 40000) : ℝ) = ((40000 / 66453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (270678583 / 250000000) ≤ -Real.log (13547 / 40000) ∧
    -Real.log (13547 / 40000) ≤ (541357167 / 500000000) := by
  have h := checkLog_sound (w := (6453 / 33547)) (n := 12)
    (lo := (24347947 / 62500000)) (hi := (389567153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13547) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 13547) = 1/(13547 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-541357167 / 500000000) (-270678583 / 250000000) (Real.log (13547 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (53087777 / 125000000) ≤ -Real.log (200000 / 305827) ∧
    -Real.log (200000 / 305827) ≤ (424702217 / 1000000000) := by
  have h := checkLog_sound (w := (105827 / 505827)) (n := 12)
    (lo := (53087777 / 125000000)) (hi := (424702217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305827 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305827 / 200000) = 1/(200000 / 305827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (53087777 / 125000000) (424702217 / 1000000000) (Real.log (305827 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (305827 / 200000) = -Real.log (200000 / 305827) := by
    rw [show ((305827 / 200000) : ℝ) = ((200000 / 305827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (753183849 / 1000000000) ≤ -Real.log (94173 / 200000) ∧
    -Real.log (94173 / 200000) ≤ (753183851 / 1000000000) := by
  have h := checkLog_sound (w := (5827 / 194173)) (n := 12)
    (lo := (60036669 / 1000000000)) (hi := (6003667 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 94173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 94173) = 1/(94173 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-753183851 / 1000000000) (-753183849 / 1000000000) (Real.log (94173 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (426079823 / 1000000000) ≤ -Real.log (1000000 / 1531243) ∧
    -Real.log (1000000 / 1531243) ≤ (26629989 / 62500000) := by
  have h := checkLog_sound (w := (531243 / 2531243)) (n := 12)
    (lo := (426079823 / 1000000000)) (hi := (26629989 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1531243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1531243 / 1000000) = 1/(1000000 / 1531243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (426079823 / 1000000000) (26629989 / 62500000) (Real.log (1531243 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1531243 / 1000000) = -Real.log (1000000 / 1531243) := by
    rw [show ((1531243 / 1000000) : ℝ) = ((1000000 / 1531243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (757670767 / 1000000000) ≤ -Real.log (468757 / 1000000) ∧
    -Real.log (468757 / 1000000) ≤ (757670769 / 1000000000) := by
  have h := checkLog_sound (w := (31243 / 968757)) (n := 12)
    (lo := (64523587 / 1000000000)) (hi := (16130897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 468757) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 468757) = 1/(468757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-757670769 / 1000000000) (-757670767 / 1000000000) (Real.log (468757 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (791484181 / 500000000) ≤ -Real.log (500000000000 / 2434694248879) ∧
    -Real.log (500000000000 / 2434694248879) ≤ (316593673 / 200000000) := by
  have h := checkLog_sound (w := (434694248879 / 4434694248879)) (n := 12)
    (lo := (98337001 / 500000000)) (hi := (196674003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2434694248879 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2434694248879 / 2000000000000) = 1/(500000000000 / 2434694248879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (791484181 / 500000000) (316593673 / 200000000) (Real.log (2434694248879 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2434694248879 / 500000000000) = -Real.log (500000000000 / 2434694248879) := by
    rw [show ((2434694248879 / 500000000000) : ℝ) = ((500000000000 / 2434694248879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1590329809 / 1000000000) ≤ -Real.log (100000000000 / 490536650181) ∧
    -Real.log (100000000000 / 490536650181) ≤ (397582453 / 250000000) := by
  have h := checkLog_sound (w := (90536650181 / 890536650181)) (n := 12)
    (lo := (204035449 / 1000000000)) (hi := (4080709 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490536650181 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(490536650181 / 400000000000) = 1/(100000000000 / 490536650181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1590329809 / 1000000000) (397582453 / 250000000) (Real.log (490536650181 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (490536650181 / 100000000000) = -Real.log (100000000000 / 490536650181) := by
    rw [show ((490536650181 / 100000000000) : ℝ) = ((100000000000 / 490536650181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (235577213 / 200000000) ≤ -Real.log (500000000000 / 1623750968961) ∧
    -Real.log (500000000000 / 1623750968961) ≤ (1177886067 / 1000000000) := by
  have h := checkLog_sound (w := (623750968961 / 2623750968961)) (n := 12)
    (lo := (96947777 / 200000000)) (hi := (242369443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1623750968961 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1623750968961 / 1000000000000) = 1/(500000000000 / 1623750968961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (235577213 / 200000000) (1177886067 / 1000000000) (Real.log (1623750968961 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1623750968961 / 500000000000) = -Real.log (500000000000 / 1623750968961) := by
    rw [show ((1623750968961 / 500000000000) : ℝ) = ((500000000000 / 1623750968961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1183750591 / 1000000000) ≤ -Real.log (7812500000 / 25520335563) ∧
    -Real.log (7812500000 / 25520335563) ≤ (1183750593 / 1000000000) := by
  have h := checkLog_sound (w := (9895335563 / 41145335563)) (n := 12)
    (lo := (490603411 / 1000000000)) (hi := (122650853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25520335563 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25520335563 / 15625000000) = 1/(7812500000 / 25520335563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1183750591 / 1000000000) (1183750593 / 1000000000) (Real.log (25520335563 / 7812500000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (25520335563 / 7812500000) = -Real.log (7812500000 / 25520335563) := by
    rw [show ((25520335563 / 7812500000) : ℝ) = ((7812500000 / 25520335563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0059

end


