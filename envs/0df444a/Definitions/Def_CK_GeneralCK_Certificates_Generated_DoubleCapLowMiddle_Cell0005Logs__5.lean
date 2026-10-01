-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0005Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0005Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:54:59.710497+00:00
-- url     : https://prove2.me/theorems/8933cd80-4365-4a9d-9779-913b31c55766
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0005Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0006Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0005Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0006Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0007Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0008Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0009Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0005Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0006Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0007Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0008Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0009Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0005Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0006Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0007Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0008Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0009Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0005Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0006Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0007Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0008Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0009Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0005Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0005
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

theorem reflection_log_1_neg : (34143127 / 50000000) ≤ -Real.log (1000000000000 / 1979536132813) ∧
    -Real.log (1000000000000 / 1979536132813) ≤ (682862541 / 1000000000) := by
  have h := checkLog_sound (w := (979536132813 / 2979536132813)) (n := 12)
    (lo := (34143127 / 50000000)) (hi := (682862541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979536132813 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979536132813 / 1000000000000) = 1/(1000000000000 / 1979536132813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (34143127 / 50000000) (682862541 / 1000000000) (Real.log (1979536132813 / 1000000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1979536132813 / 1000000000000) = -Real.log (1000000000000 / 1979536132813) := by
    rw [show ((1979536132813 / 1000000000000) : ℝ) = ((1000000000000 / 1979536132813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3889094521 / 1000000000) ≤ -Real.log (20463867187 / 1000000000000) ∧
    -Real.log (20463867187 / 1000000000000) ≤ (3889094527 / 1000000000) := by
  have h := checkLog_sound (w := (10786132813 / 51713867187)) (n := 12)
    (lo := (423358621 / 1000000000)) (hi := (211679311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20463867187) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20463867187) = 1/(20463867187 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3889094527 / 1000000000) (-3889094521 / 1000000000) (Real.log (20463867187 / 1000000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682815673 / 1000000000) ≤ -Real.log (20480 / 40539) ∧
    -Real.log (20480 / 40539) ≤ (341407837 / 500000000) := by
  have h := checkLog_sound (w := (20059 / 61019)) (n := 12)
    (lo := (682815673 / 1000000000)) (hi := (341407837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40539 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40539 / 20480) = 1/(20480 / 40539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682815673 / 1000000000) (341407837 / 500000000) (Real.log (40539 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40539 / 20480) = -Real.log (20480 / 40539) := by
    rw [show ((40539 / 20480) : ℝ) = ((20480 / 40539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1942285621 / 500000000) ≤ -Real.log (421 / 20480) ∧
    -Real.log (421 / 20480) ≤ (242785703 / 62500000) := by
  have h := checkLog_sound (w := (219 / 1061)) (n := 12)
    (lo := (209417671 / 500000000)) (hi := (418835343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 421) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 421) = 1/(421 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-242785703 / 62500000) (-1942285621 / 500000000) (Real.log (421 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672471027 / 1000000000) ≤ -Real.log (102400 / 200609) ∧
    -Real.log (102400 / 200609) ≤ (168117757 / 250000000) := by
  have h := checkLog_sound (w := (98209 / 303009)) (n := 12)
    (lo := (672471027 / 1000000000)) (hi := (168117757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200609 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200609 / 102400) = 1/(102400 / 200609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672471027 / 1000000000) (168117757 / 250000000) (Real.log (200609 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200609 / 102400) = -Real.log (102400 / 200609) := by
    rw [show ((200609 / 102400) : ℝ) = ((102400 / 200609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3195947341 / 1000000000) ≤ -Real.log (4191 / 102400) ∧
    -Real.log (4191 / 102400) ≤ (1597973673 / 500000000) := by
  have h := checkLog_sound (w := (2209 / 10591)) (n := 12)
    (lo := (423358621 / 1000000000)) (hi := (211679311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4191) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4191) = 1/(4191 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1597973673 / 500000000) (-3195947341 / 1000000000) (Real.log (4191 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672376311 / 1000000000) ≤ -Real.log (10240 / 20059) ∧
    -Real.log (10240 / 20059) ≤ (84047039 / 125000000) := by
  have h := checkLog_sound (w := (9819 / 30299)) (n := 12)
    (lo := (672376311 / 1000000000)) (hi := (84047039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20059 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20059 / 10240) = 1/(10240 / 20059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672376311 / 1000000000) (84047039 / 125000000) (Real.log (20059 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (20059 / 10240) = -Real.log (10240 / 20059) := by
    rw [show ((20059 / 10240) : ℝ) = ((10240 / 20059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1595712031 / 500000000) ≤ -Real.log (421 / 10240) ∧
    -Real.log (421 / 10240) ≤ (3191424067 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 1061)) (n := 12)
    (lo := (209417671 / 500000000)) (hi := (418835343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 421) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 421) = 1/(421 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3191424067 / 1000000000) (-1595712031 / 500000000) (Real.log (421 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136874963 / 200000000) ≤ -Real.log (250000 / 495633) ∧
    -Real.log (250000 / 495633) ≤ (21386713 / 31250000) := by
  have h := checkLog_sound (w := (245633 / 745633)) (n := 12)
    (lo := (136874963 / 200000000)) (hi := (21386713 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495633 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495633 / 250000) = 1/(250000 / 495633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136874963 / 200000000) (21386713 / 31250000) (Real.log (495633 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (495633 / 250000) = -Real.log (250000 / 495633) := by
    rw [show ((495633 / 250000) : ℝ) = ((250000 / 495633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (12648077 / 3125000) ≤ -Real.log (4367 / 250000) ∧
    -Real.log (4367 / 250000) ≤ (2023692323 / 500000000) := by
  have h := checkLog_sound (w := (6891 / 24359)) (n := 12)
    (lo := (29082437 / 50000000)) (hi := (581648741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8734) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8734) = 1/(4367 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2023692323 / 500000000) (-12648077 / 3125000) (Real.log (4367 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (342206827 / 500000000) ≤ -Real.log (1000000 / 1982609) ∧
    -Real.log (1000000 / 1982609) ≤ (136882731 / 200000000) := by
  have h := checkLog_sound (w := (982609 / 2982609)) (n := 12)
    (lo := (342206827 / 500000000)) (hi := (136882731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982609 / 1000000) = 1/(1000000 / 1982609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (342206827 / 500000000) (136882731 / 200000000) (Real.log (1982609 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982609 / 1000000) = -Real.log (1000000 / 1982609) := by
    rw [show ((1982609 / 1000000) : ℝ) = ((1000000 / 1982609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (810360489 / 200000000) ≤ -Real.log (17391 / 1000000) ∧
    -Real.log (17391 / 1000000) ≤ (4051802451 / 1000000000) := by
  have h := checkLog_sound (w := (13859 / 48641)) (n := 12)
    (lo := (117213309 / 200000000)) (hi := (293033273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17391) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17391) = 1/(17391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4051802451 / 1000000000) (-810360489 / 200000000) (Real.log (17391 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (171085381 / 250000000) ≤ -Real.log (500000 / 991233) ∧
    -Real.log (500000 / 991233) ≤ (27373661 / 40000000) := by
  have h := checkLog_sound (w := (491233 / 1491233)) (n := 12)
    (lo := (171085381 / 250000000)) (hi := (27373661 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991233 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991233 / 500000) = 1/(500000 / 991233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (171085381 / 250000000) (27373661 / 40000000) (Real.log (991233 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (991233 / 500000) = -Real.log (500000 / 991233) := by
    rw [show ((991233 / 500000) : ℝ) = ((500000 / 991233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4043613423 / 1000000000) ≤ -Real.log (8767 / 500000) ∧
    -Real.log (8767 / 500000) ≤ (4043613429 / 1000000000) := by
  have h := checkLog_sound (w := (3429 / 12196)) (n := 12)
    (lo := (577877523 / 1000000000)) (hi := (144469381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8767) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8767) = 1/(8767 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4043613429 / 1000000000) (-4043613423 / 1000000000) (Real.log (8767 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (171095217 / 250000000) ≤ -Real.log (62500 / 123909) ∧
    -Real.log (62500 / 123909) ≤ (684380869 / 1000000000) := by
  have h := checkLog_sound (w := (61409 / 186409)) (n := 12)
    (lo := (171095217 / 250000000)) (hi := (684380869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123909 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123909 / 62500) = 1/(62500 / 123909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (171095217 / 250000000) (684380869 / 1000000000) (Real.log (123909 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (123909 / 62500) = -Real.log (62500 / 123909) := by
    rw [show ((123909 / 62500) : ℝ) = ((62500 / 123909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4048071847 / 1000000000) ≤ -Real.log (1091 / 62500) ∧
    -Real.log (1091 / 62500) ≤ (4048071853 / 1000000000) := by
  have h := checkLog_sound (w := (6897 / 24353)) (n := 12)
    (lo := (582335947 / 1000000000)) (hi := (145583987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8728) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8728) = 1/(1091 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4048071853 / 1000000000) (-4048071847 / 1000000000) (Real.log (1091 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (946351891 / 200000000) ≤ -Real.log (10000000000 / 1134950767117) ∧
    -Real.log (10000000000 / 1134950767117) ≤ (2365879731 / 500000000) := by
  have h := checkLog_sound (w := (494950767117 / 1774950767117)) (n := 12)
    (lo := (4583011 / 8000000)) (hi := (71609547 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134950767117 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1134950767117 / 640000000000) = 1/(10000000000 / 1134950767117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (946351891 / 200000000) (2365879731 / 500000000) (Real.log (1134950767117 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1134950767117 / 10000000000) = -Real.log (10000000000 / 1134950767117) := by
    rw [show ((1134950767117 / 10000000000) : ℝ) = ((10000000000 / 1134950767117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2368108049 / 500000000) ≤ -Real.log (50000000000 / 5700100626761) ∧
    -Real.log (50000000000 / 5700100626761) ≤ (947243221 / 200000000) := by
  have h := checkLog_sound (w := (2500100626761 / 8900100626761)) (n := 12)
    (lo := (288666509 / 500000000)) (hi := (577333019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5700100626761 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5700100626761 / 3200000000000) = 1/(50000000000 / 5700100626761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2368108049 / 500000000) (947243221 / 200000000) (Real.log (5700100626761 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5700100626761 / 50000000000) = -Real.log (50000000000 / 5700100626761) := by
    rw [show ((5700100626761 / 50000000000) : ℝ) = ((50000000000 / 5700100626761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2363977473 / 500000000) ≤ -Real.log (500000000000 / 56532052013231) ∧
    -Real.log (500000000000 / 56532052013231) ≤ (4727954953 / 1000000000) := by
  have h := checkLog_sound (w := (24532052013231 / 88532052013231)) (n := 12)
    (lo := (284535933 / 500000000)) (hi := (569071867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56532052013231 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56532052013231 / 32000000000000) = 1/(500000000000 / 56532052013231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2363977473 / 500000000) (4727954953 / 1000000000) (Real.log (56532052013231 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56532052013231 / 500000000000) = -Real.log (500000000000 / 56532052013231) := by
    rw [show ((56532052013231 / 500000000000) : ℝ) = ((500000000000 / 56532052013231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (946490543 / 200000000) ≤ -Real.log (500000000000 / 56786892758937) ∧
    -Real.log (500000000000 / 56786892758937) ≤ (2366226361 / 500000000) := by
  have h := checkLog_sound (w := (24786892758937 / 88786892758937)) (n := 12)
    (lo := (114713927 / 200000000)) (hi := (143392409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56786892758937 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56786892758937 / 32000000000000) = 1/(500000000000 / 56786892758937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (946490543 / 200000000) (2366226361 / 500000000) (Real.log (56786892758937 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (56786892758937 / 500000000000) = -Real.log (500000000000 / 56786892758937) := by
    rw [show ((56786892758937 / 500000000000) : ℝ) = ((500000000000 / 56786892758937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0005

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0006Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0006
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

theorem reflection_log_1_neg : (682815673 / 1000000000) ≤ -Real.log (20480 / 40539) ∧
    -Real.log (20480 / 40539) ≤ (341407837 / 500000000) := by
  have h := checkLog_sound (w := (20059 / 61019)) (n := 12)
    (lo := (682815673 / 1000000000)) (hi := (341407837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40539 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40539 / 20480) = 1/(20480 / 40539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682815673 / 1000000000) (341407837 / 500000000) (Real.log (40539 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40539 / 20480) = -Real.log (20480 / 40539) := by
    rw [show ((40539 / 20480) : ℝ) = ((20480 / 40539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1942285621 / 500000000) ≤ -Real.log (421 / 20480) ∧
    -Real.log (421 / 20480) ≤ (242785703 / 62500000) := by
  have h := checkLog_sound (w := (219 / 1061)) (n := 12)
    (lo := (209417671 / 500000000)) (hi := (418835343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 421) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 421) = 1/(421 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-242785703 / 62500000) (-1942285621 / 500000000) (Real.log (421 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170692201 / 250000000) ≤ -Real.log (1000000000000 / 1979350585937) ∧
    -Real.log (1000000000000 / 1979350585937) ≤ (136553761 / 200000000) := by
  have h := checkLog_sound (w := (979350585937 / 2979350585937)) (n := 12)
    (lo := (170692201 / 250000000)) (hi := (136553761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979350585937 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979350585937 / 1000000000000) = 1/(1000000000000 / 1979350585937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170692201 / 250000000) (136553761 / 200000000) (Real.log (1979350585937 / 1000000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1979350585937 / 1000000000000) = -Real.log (1000000000000 / 1979350585937) := by
    rw [show ((1979350585937 / 1000000000000) : ℝ) = ((1000000000000 / 1979350585937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3880068331 / 1000000000) ≤ -Real.log (20649414063 / 1000000000000) ∧
    -Real.log (20649414063 / 1000000000000) ≤ (3880068337 / 1000000000) := by
  have h := checkLog_sound (w := (10600585937 / 51899414063)) (n := 12)
    (lo := (414332431 / 1000000000)) (hi := (25895777 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20649414063) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20649414063) = 1/(20649414063 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3880068337 / 1000000000) (-3880068331 / 1000000000) (Real.log (20649414063 / 1000000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672376311 / 1000000000) ≤ -Real.log (10240 / 20059) ∧
    -Real.log (10240 / 20059) ≤ (84047039 / 125000000) := by
  have h := checkLog_sound (w := (9819 / 30299)) (n := 12)
    (lo := (672376311 / 1000000000)) (hi := (84047039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20059 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20059 / 10240) = 1/(10240 / 20059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672376311 / 1000000000) (84047039 / 125000000) (Real.log (20059 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (20059 / 10240) = -Real.log (10240 / 20059) := by
    rw [show ((20059 / 10240) : ℝ) = ((10240 / 20059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1595712031 / 500000000) ≤ -Real.log (421 / 10240) ∧
    -Real.log (421 / 10240) ≤ (3191424067 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 1061)) (n := 12)
    (lo := (209417671 / 500000000)) (hi := (418835343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 421) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 421) = 1/(421 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3191424067 / 1000000000) (-1595712031 / 500000000) (Real.log (421 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (336140793 / 500000000) ≤ -Real.log (102400 / 200571) ∧
    -Real.log (102400 / 200571) ≤ (672281587 / 1000000000) := by
  have h := checkLog_sound (w := (98171 / 302971)) (n := 12)
    (lo := (336140793 / 500000000)) (hi := (672281587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200571 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200571 / 102400) = 1/(102400 / 200571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (336140793 / 500000000) (672281587 / 1000000000) (Real.log (200571 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200571 / 102400) = -Real.log (102400 / 200571) := by
    rw [show ((200571 / 102400) : ℝ) = ((102400 / 200571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3186921151 / 1000000000) ≤ -Real.log (4229 / 102400) ∧
    -Real.log (4229 / 102400) ≤ (796730289 / 250000000) := by
  have h := checkLog_sound (w := (2171 / 10629)) (n := 12)
    (lo := (414332431 / 1000000000)) (hi := (25895777 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4229) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4229) = 1/(4229 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-796730289 / 250000000) (-3186921151 / 1000000000) (Real.log (4229 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4277103 / 6250000) ≤ -Real.log (125000 / 247807) ∧
    -Real.log (125000 / 247807) ≤ (684336481 / 1000000000) := by
  have h := checkLog_sound (w := (122807 / 372807)) (n := 12)
    (lo := (4277103 / 6250000)) (hi := (684336481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247807 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247807 / 125000) = 1/(125000 / 247807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4277103 / 6250000) (684336481 / 1000000000) (Real.log (247807 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247807 / 125000) = -Real.log (125000 / 247807) := by
    rw [show ((247807 / 125000) : ℝ) = ((125000 / 247807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (808608653 / 200000000) ≤ -Real.log (2193 / 125000) ∧
    -Real.log (2193 / 125000) ≤ (4043043271 / 1000000000) := by
  have h := checkLog_sound (w := (6853 / 24397)) (n := 12)
    (lo := (115461473 / 200000000)) (hi := (288653683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8772) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8772) = 1/(2193 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4043043271 / 1000000000) (-808608653 / 200000000) (Real.log (2193 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17109383 / 25000000) ≤ -Real.log (1000000 / 1982533) ∧
    -Real.log (1000000 / 1982533) ≤ (684375321 / 1000000000) := by
  have h := checkLog_sound (w := (982533 / 2982533)) (n := 12)
    (lo := (17109383 / 25000000)) (hi := (684375321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982533 / 1000000) = 1/(1000000 / 1982533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17109383 / 25000000) (684375321 / 1000000000) (Real.log (1982533 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982533 / 1000000) = -Real.log (1000000 / 1982533) := by
    rw [show ((1982533 / 1000000) : ℝ) = ((1000000 / 1982533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4047441889 / 1000000000) ≤ -Real.log (17467 / 1000000) ∧
    -Real.log (17467 / 1000000) ≤ (809488379 / 200000000) := by
  have h := checkLog_sound (w := (13783 / 48717)) (n := 12)
    (lo := (581705989 / 1000000000)) (hi := (58170599 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17467) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17467) = 1/(17467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-809488379 / 200000000) (-4047441889 / 1000000000) (Real.log (17467 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684303187 / 1000000000) ≤ -Real.log (100000 / 198239) ∧
    -Real.log (100000 / 198239) ≤ (171075797 / 250000000) := by
  have h := checkLog_sound (w := (98239 / 298239)) (n := 12)
    (lo := (684303187 / 1000000000)) (hi := (171075797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198239 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198239 / 100000) = 1/(100000 / 198239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684303187 / 1000000000) (171075797 / 250000000) (Real.log (198239 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (198239 / 100000) = -Real.log (100000 / 198239) := by
    rw [show ((198239 / 100000) : ℝ) = ((100000 / 198239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4039288353 / 1000000000) ≤ -Real.log (1761 / 100000) ∧
    -Real.log (1761 / 100000) ≤ (4039288359 / 1000000000) := by
  have h := checkLog_sound (w := (682 / 2443)) (n := 12)
    (lo := (573552453 / 1000000000)) (hi := (286776227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1761) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1761) = 1/(1761 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4039288359 / 1000000000) (-4039288353 / 1000000000) (Real.log (1761 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (171085507 / 250000000) ≤ -Real.log (1000000 / 1982467) ∧
    -Real.log (1000000 / 1982467) ≤ (684342029 / 1000000000) := by
  have h := checkLog_sound (w := (982467 / 2982467)) (n := 12)
    (lo := (171085507 / 250000000)) (hi := (684342029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982467 / 1000000) = 1/(1000000 / 1982467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (171085507 / 250000000) (684342029 / 1000000000) (Real.log (1982467 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982467 / 1000000) = -Real.log (1000000 / 1982467) := by
    rw [show ((1982467 / 1000000) : ℝ) = ((1000000 / 1982467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (505458807 / 125000000) ≤ -Real.log (17533 / 1000000) ∧
    -Real.log (17533 / 1000000) ≤ (2021835231 / 500000000) := by
  have h := checkLog_sound (w := (13717 / 48783)) (n := 12)
    (lo := (144483639 / 250000000)) (hi := (577934557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17533) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17533) = 1/(17533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2021835231 / 500000000) (-505458807 / 125000000) (Real.log (17533 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (147730617 / 31250000) ≤ -Real.log (500000000000 / 56499544003647) ∧
    -Real.log (500000000000 / 56499544003647) ≤ (4727379751 / 1000000000) := by
  have h := checkLog_sound (w := (24499544003647 / 88499544003647)) (n := 12)
    (lo := (71062083 / 125000000)) (hi := (113699333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56499544003647 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56499544003647 / 32000000000000) = 1/(500000000000 / 56499544003647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (147730617 / 31250000) (4727379751 / 1000000000) (Real.log (56499544003647 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (56499544003647 / 500000000000) = -Real.log (500000000000 / 56499544003647) := by
    rw [show ((56499544003647 / 500000000000) : ℝ) = ((500000000000 / 56499544003647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4731817209 / 1000000000) ≤ -Real.log (250000000000 / 28375407912063) ∧
    -Real.log (250000000000 / 28375407912063) ≤ (18483661 / 3906250) := by
  have h := checkLog_sound (w := (12375407912063 / 44375407912063)) (n := 12)
    (lo := (572934129 / 1000000000)) (hi := (57293413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28375407912063 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28375407912063 / 16000000000000) = 1/(250000000000 / 28375407912063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4731817209 / 1000000000) (18483661 / 3906250) (Real.log (28375407912063 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28375407912063 / 250000000000) = -Real.log (250000000000 / 28375407912063) := by
    rw [show ((28375407912063 / 250000000000) : ℝ) = ((250000000000 / 28375407912063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (236179577 / 50000000) ≤ -Real.log (500000000000 / 56285917092561) ∧
    -Real.log (500000000000 / 56285917092561) ≤ (4723591547 / 1000000000) := by
  have h := checkLog_sound (w := (24285917092561 / 88285917092561)) (n := 12)
    (lo := (28235423 / 50000000)) (hi := (564708461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56285917092561 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56285917092561 / 32000000000000) = 1/(500000000000 / 56285917092561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (236179577 / 50000000) (4723591547 / 1000000000) (Real.log (56285917092561 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56285917092561 / 500000000000) = -Real.log (500000000000 / 56285917092561) := by
    rw [show ((56285917092561 / 500000000000) : ℝ) = ((500000000000 / 56285917092561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1182003121 / 250000000) ≤ -Real.log (100000000000 / 11307060970741) ∧
    -Real.log (100000000000 / 11307060970741) ≤ (4728012491 / 1000000000) := by
  have h := checkLog_sound (w := (4907060970741 / 17707060970741)) (n := 12)
    (lo := (142282351 / 250000000)) (hi := (113825881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11307060970741 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11307060970741 / 6400000000000) = 1/(100000000000 / 11307060970741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1182003121 / 250000000) (4728012491 / 1000000000) (Real.log (11307060970741 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11307060970741 / 100000000000) = -Real.log (100000000000 / 11307060970741) := by
    rw [show ((11307060970741 / 100000000000) : ℝ) = ((100000000000 / 11307060970741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0006

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0007Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0007
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

theorem reflection_log_1_neg : (170692201 / 250000000) ≤ -Real.log (500000000000 / 989675292969) ∧
    -Real.log (500000000000 / 989675292969) ≤ (136553761 / 200000000) := by
  have h := checkLog_sound (w := (489675292969 / 1489675292969)) (n := 12)
    (lo := (170692201 / 250000000)) (hi := (136553761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989675292969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989675292969 / 500000000000) = 1/(500000000000 / 989675292969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170692201 / 250000000) (136553761 / 200000000) (Real.log (989675292969 / 500000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (989675292969 / 500000000000) = -Real.log (500000000000 / 989675292969) := by
    rw [show ((989675292969 / 500000000000) : ℝ) = ((500000000000 / 989675292969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3880068331 / 1000000000) ≤ -Real.log (10324707031 / 500000000000) ∧
    -Real.log (10324707031 / 500000000000) ≤ (3880068337 / 1000000000) := by
  have h := checkLog_sound (w := (5300292969 / 25949707031)) (n := 12)
    (lo := (414332431 / 1000000000)) (hi := (25895777 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10324707031) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625000000 / 10324707031) = 1/(10324707031 / 500000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3880068337 / 1000000000) (-3880068331 / 1000000000) (Real.log (10324707031 / 500000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170680483 / 250000000) ≤ -Real.log (25600 / 50669) ∧
    -Real.log (25600 / 50669) ≤ (682721933 / 1000000000) := by
  have h := checkLog_sound (w := (25069 / 76269)) (n := 12)
    (lo := (170680483 / 250000000)) (hi := (682721933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50669 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50669 / 25600) = 1/(25600 / 50669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170680483 / 250000000) (682721933 / 1000000000) (Real.log (50669 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50669 / 25600) = -Real.log (25600 / 50669) := by
    rw [show ((50669 / 25600) : ℝ) = ((25600 / 50669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1937792803 / 500000000) ≤ -Real.log (531 / 25600) ∧
    -Real.log (531 / 25600) ≤ (968896403 / 250000000) := by
  have h := checkLog_sound (w := (269 / 1331)) (n := 12)
    (lo := (204924853 / 500000000)) (hi := (409849707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 531) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 531) = 1/(531 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-968896403 / 250000000) (-1937792803 / 500000000) (Real.log (531 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (336140793 / 500000000) ≤ -Real.log (102400 / 200571) ∧
    -Real.log (102400 / 200571) ≤ (672281587 / 1000000000) := by
  have h := checkLog_sound (w := (98171 / 302971)) (n := 12)
    (lo := (336140793 / 500000000)) (hi := (672281587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200571 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200571 / 102400) = 1/(102400 / 200571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (336140793 / 500000000) (672281587 / 1000000000) (Real.log (200571 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200571 / 102400) = -Real.log (102400 / 200571) := by
    rw [show ((200571 / 102400) : ℝ) = ((102400 / 200571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3186921151 / 1000000000) ≤ -Real.log (4229 / 102400) ∧
    -Real.log (4229 / 102400) ≤ (796730289 / 250000000) := by
  have h := checkLog_sound (w := (2171 / 10629)) (n := 12)
    (lo := (414332431 / 1000000000)) (hi := (25895777 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4229) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4229) = 1/(4229 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-796730289 / 250000000) (-3186921151 / 1000000000) (Real.log (4229 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168046713 / 250000000) ≤ -Real.log (12800 / 25069) ∧
    -Real.log (12800 / 25069) ≤ (672186853 / 1000000000) := by
  have h := checkLog_sound (w := (12269 / 37869)) (n := 12)
    (lo := (168046713 / 250000000)) (hi := (672186853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25069 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25069 / 12800) = 1/(12800 / 25069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168046713 / 250000000) (672186853 / 1000000000) (Real.log (25069 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (25069 / 12800) = -Real.log (12800 / 25069) := by
    rw [show ((25069 / 12800) : ℝ) = ((12800 / 25069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1591219213 / 500000000) ≤ -Real.log (531 / 12800) ∧
    -Real.log (531 / 12800) ≤ (3182438431 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1331)) (n := 12)
    (lo := (204924853 / 500000000)) (hi := (409849707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 531) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 531) = 1/(531 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3182438431 / 1000000000) (-1591219213 / 500000000) (Real.log (531 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684298143 / 1000000000) ≤ -Real.log (50000 / 99119) ∧
    -Real.log (50000 / 99119) ≤ (21384317 / 31250000) := by
  have h := checkLog_sound (w := (49119 / 149119)) (n := 12)
    (lo := (684298143 / 1000000000)) (hi := (21384317 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99119 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99119 / 50000) = 1/(50000 / 99119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684298143 / 1000000000) (21384317 / 31250000) (Real.log (99119 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (99119 / 50000) = -Real.log (50000 / 99119) := by
    rw [show ((99119 / 50000) : ℝ) = ((50000 / 99119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (807744131 / 200000000) ≤ -Real.log (881 / 50000) ∧
    -Real.log (881 / 50000) ≤ (4038720661 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 4887)) (n := 12)
    (lo := (114596951 / 200000000)) (hi := (143246189 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1762) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1762) = 1/(881 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4038720661 / 1000000000) (-807744131 / 200000000) (Real.log (881 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (85542123 / 125000000) ≤ -Real.log (1000000 / 1982457) ∧
    -Real.log (1000000 / 1982457) ≤ (136867397 / 200000000) := by
  have h := checkLog_sound (w := (982457 / 2982457)) (n := 12)
    (lo := (85542123 / 125000000)) (hi := (136867397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982457 / 1000000) = 1/(1000000 / 1982457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (85542123 / 125000000) (136867397 / 200000000) (Real.log (1982457 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982457 / 1000000) = -Real.log (1000000 / 1982457) := by
    rw [show ((1982457 / 1000000) : ℝ) = ((1000000 / 1982457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2021550133 / 500000000) ≤ -Real.log (17543 / 1000000) ∧
    -Real.log (17543 / 1000000) ≤ (252693767 / 62500000) := by
  have h := checkLog_sound (w := (13707 / 48793)) (n := 12)
    (lo := (288682183 / 500000000)) (hi := (577364367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17543) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17543) = 1/(17543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-252693767 / 62500000) (-2021550133 / 500000000) (Real.log (17543 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684264849 / 1000000000) ≤ -Real.log (500000 / 991157) ∧
    -Real.log (500000 / 991157) ≤ (13685297 / 20000000) := by
  have h := checkLog_sound (w := (491157 / 1491157)) (n := 12)
    (lo := (684264849 / 1000000000)) (hi := (13685297 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991157 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991157 / 500000) = 1/(500000 / 991157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684264849 / 1000000000) (13685297 / 20000000) (Real.log (991157 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (991157 / 500000) = -Real.log (500000 / 991157) := by
    rw [show ((991157 / 500000) : ℝ) = ((500000 / 991157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (403498191 / 100000000) ≤ -Real.log (8843 / 500000) ∧
    -Real.log (8843 / 500000) ≤ (1008745479 / 250000000) := by
  have h := checkLog_sound (w := (3391 / 12234)) (n := 12)
    (lo := (56924601 / 100000000)) (hi := (569246011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8843) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8843) = 1/(8843 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1008745479 / 250000000) (-403498191 / 100000000) (Real.log (8843 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684303691 / 1000000000) ≤ -Real.log (1000000 / 1982391) ∧
    -Real.log (1000000 / 1982391) ≤ (171075923 / 250000000) := by
  have h := checkLog_sound (w := (982391 / 2982391)) (n := 12)
    (lo := (684303691 / 1000000000)) (hi := (171075923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982391 / 1000000) = 1/(1000000 / 1982391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684303691 / 1000000000) (171075923 / 250000000) (Real.log (1982391 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982391 / 1000000) = -Real.log (1000000 / 1982391) := by
    rw [show ((1982391 / 1000000) : ℝ) = ((1000000 / 1982391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4039345141 / 1000000000) ≤ -Real.log (17609 / 1000000) ∧
    -Real.log (17609 / 1000000) ≤ (4039345147 / 1000000000) := by
  have h := checkLog_sound (w := (13641 / 48859)) (n := 12)
    (lo := (573609241 / 1000000000)) (hi := (286804621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17609) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17609) = 1/(17609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4039345147 / 1000000000) (-4039345141 / 1000000000) (Real.log (17609 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2361509399 / 500000000) ≤ -Real.log (62500000000 / 7031711123723) ∧
    -Real.log (62500000000 / 7031711123723) ≤ (944603761 / 200000000) := by
  have h := checkLog_sound (w := (3031711123723 / 11031711123723)) (n := 12)
    (lo := (282067859 / 500000000)) (hi := (564135719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7031711123723 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7031711123723 / 4000000000000) = 1/(62500000000 / 7031711123723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2361509399 / 500000000) (944603761 / 200000000) (Real.log (7031711123723 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7031711123723 / 62500000000) = -Real.log (62500000000 / 7031711123723) := by
    rw [show ((7031711123723 / 62500000000) : ℝ) = ((62500000000 / 7031711123723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18909749 / 4000000) ≤ -Real.log (15625000000 / 1765712285527) ∧
    -Real.log (15625000000 / 1765712285527) ≤ (4727437257 / 1000000000) := by
  have h := checkLog_sound (w := (765712285527 / 2765712285527)) (n := 12)
    (lo := (56855417 / 100000000)) (hi := (568554171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1765712285527 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1765712285527 / 1000000000000) = 1/(15625000000 / 1765712285527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18909749 / 4000000) (4727437257 / 1000000000) (Real.log (1765712285527 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1765712285527 / 15625000000) = -Real.log (15625000000 / 1765712285527) := by
    rw [show ((1765712285527 / 15625000000) : ℝ) = ((15625000000 / 1765712285527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2359623379 / 500000000) ≤ -Real.log (500000000000 / 56041897546081) ∧
    -Real.log (500000000000 / 56041897546081) ≤ (943849353 / 200000000) := by
  have h := checkLog_sound (w := (24041897546081 / 88041897546081)) (n := 12)
    (lo := (280181839 / 500000000)) (hi := (560363679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56041897546081 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56041897546081 / 32000000000000) = 1/(500000000000 / 56041897546081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2359623379 / 500000000) (943849353 / 200000000) (Real.log (56041897546081 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56041897546081 / 500000000000) = -Real.log (500000000000 / 56041897546081) := by
    rw [show ((56041897546081 / 500000000000) : ℝ) = ((500000000000 / 56041897546081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (73807013 / 15625000) ≤ -Real.log (250000000000 / 28144570958033) ∧
    -Real.log (250000000000 / 28144570958033) ≤ (4723648839 / 1000000000) := by
  have h := checkLog_sound (w := (12144570958033 / 44144570958033)) (n := 12)
    (lo := (70595719 / 125000000)) (hi := (564765753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28144570958033 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28144570958033 / 16000000000000) = 1/(250000000000 / 28144570958033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (73807013 / 15625000) (4723648839 / 1000000000) (Real.log (28144570958033 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28144570958033 / 250000000000) = -Real.log (250000000000 / 28144570958033) := by
    rw [show ((28144570958033 / 250000000000) : ℝ) = ((250000000000 / 28144570958033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0007

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0008Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0008
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

theorem reflection_log_1_neg : (170680483 / 250000000) ≤ -Real.log (25600 / 50669) ∧
    -Real.log (25600 / 50669) ≤ (682721933 / 1000000000) := by
  have h := checkLog_sound (w := (25069 / 76269)) (n := 12)
    (lo := (170680483 / 250000000)) (hi := (682721933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50669 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50669 / 25600) = 1/(25600 / 50669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170680483 / 250000000) (682721933 / 1000000000) (Real.log (50669 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50669 / 25600) = -Real.log (25600 / 50669) := by
    rw [show ((50669 / 25600) : ℝ) = ((25600 / 50669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1937792803 / 500000000) ≤ -Real.log (531 / 25600) ∧
    -Real.log (531 / 25600) ≤ (968896403 / 250000000) := by
  have h := checkLog_sound (w := (269 / 1331)) (n := 12)
    (lo := (204924853 / 500000000)) (hi := (409849707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 531) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 531) = 1/(531 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-968896403 / 250000000) (-1937792803 / 500000000) (Real.log (531 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341337529 / 500000000) ≤ -Real.log (500000000000 / 989582519531) ∧
    -Real.log (500000000000 / 989582519531) ≤ (682675059 / 1000000000) := by
  have h := checkLog_sound (w := (489582519531 / 1489582519531)) (n := 12)
    (lo := (341337529 / 500000000)) (hi := (682675059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989582519531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989582519531 / 500000000000) = 1/(500000000000 / 989582519531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (341337529 / 500000000) (682675059 / 1000000000) (Real.log (989582519531 / 500000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (989582519531 / 500000000000) = -Real.log (500000000000 / 989582519531) := by
    rw [show ((989582519531 / 500000000000) : ℝ) = ((500000000000 / 989582519531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1935561443 / 500000000) ≤ -Real.log (10417480469 / 500000000000) ∧
    -Real.log (10417480469 / 500000000000) ≤ (967780723 / 250000000) := by
  have h := checkLog_sound (w := (5207519531 / 26042480469)) (n := 12)
    (lo := (202693493 / 500000000)) (hi := (405386987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10417480469) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625000000 / 10417480469) = 1/(10417480469 / 500000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-967780723 / 250000000) (-1935561443 / 500000000) (Real.log (10417480469 / 500000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168046713 / 250000000) ≤ -Real.log (12800 / 25069) ∧
    -Real.log (12800 / 25069) ≤ (672186853 / 1000000000) := by
  have h := checkLog_sound (w := (12269 / 37869)) (n := 12)
    (lo := (168046713 / 250000000)) (hi := (672186853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25069 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25069 / 12800) = 1/(12800 / 25069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168046713 / 250000000) (672186853 / 1000000000) (Real.log (25069 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (25069 / 12800) = -Real.log (12800 / 25069) := by
    rw [show ((25069 / 12800) : ℝ) = ((12800 / 25069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1591219213 / 500000000) ≤ -Real.log (531 / 12800) ∧
    -Real.log (531 / 12800) ≤ (3182438431 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1331)) (n := 12)
    (lo := (204924853 / 500000000)) (hi := (409849707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 531) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 531) = 1/(531 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3182438431 / 1000000000) (-1591219213 / 500000000) (Real.log (531 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672092109 / 1000000000) ≤ -Real.log (102400 / 200533) ∧
    -Real.log (102400 / 200533) ≤ (67209211 / 100000000) := by
  have h := checkLog_sound (w := (98133 / 302933)) (n := 12)
    (lo := (672092109 / 1000000000)) (hi := (67209211 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200533 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200533 / 102400) = 1/(102400 / 200533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672092109 / 1000000000) (67209211 / 100000000) (Real.log (200533 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200533 / 102400) = -Real.log (102400 / 200533) := by
    rw [show ((200533 / 102400) : ℝ) = ((102400 / 200533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1588987853 / 500000000) ≤ -Real.log (4267 / 102400) ∧
    -Real.log (4267 / 102400) ≤ (3177975711 / 1000000000) := by
  have h := checkLog_sound (w := (2133 / 10667)) (n := 12)
    (lo := (202693493 / 500000000)) (hi := (405386987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4267) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4267) = 1/(4267 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3177975711 / 1000000000) (-1588987853 / 500000000) (Real.log (4267 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684260309 / 1000000000) ≤ -Real.log (200000 / 396461) ∧
    -Real.log (200000 / 396461) ≤ (68426031 / 100000000) := by
  have h := checkLog_sound (w := (196461 / 596461)) (n := 12)
    (lo := (684260309 / 1000000000)) (hi := (68426031 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396461 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396461 / 200000) = 1/(200000 / 396461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684260309 / 1000000000) (68426031 / 100000000) (Real.log (396461 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (396461 / 200000) = -Real.log (200000 / 396461) := by
    rw [show ((396461 / 200000) : ℝ) = ((200000 / 396461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2017236581 / 500000000) ≤ -Real.log (3539 / 200000) ∧
    -Real.log (3539 / 200000) ≤ (252154573 / 62500000) := by
  have h := checkLog_sound (w := (2711 / 9789)) (n := 12)
    (lo := (284368631 / 500000000)) (hi := (568737263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3539) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3539) = 1/(3539 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-252154573 / 62500000) (-2017236581 / 500000000) (Real.log (3539 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684298647 / 1000000000) ≤ -Real.log (1000000 / 1982381) ∧
    -Real.log (1000000 / 1982381) ≤ (85537331 / 125000000) := by
  have h := checkLog_sound (w := (982381 / 2982381)) (n := 12)
    (lo := (684298647 / 1000000000)) (hi := (85537331 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982381 / 1000000) = 1/(1000000 / 1982381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684298647 / 1000000000) (85537331 / 125000000) (Real.log (1982381 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982381 / 1000000) = -Real.log (1000000 / 1982381) := by
    rw [show ((1982381 / 1000000) : ℝ) = ((1000000 / 1982381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (403877741 / 100000000) ≤ -Real.log (17619 / 1000000) ∧
    -Real.log (17619 / 1000000) ≤ (504847177 / 125000000) := by
  have h := checkLog_sound (w := (13631 / 48869)) (n := 12)
    (lo := (57304151 / 100000000)) (hi := (573041511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17619) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17619) = 1/(17619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-504847177 / 125000000) (-403877741 / 100000000) (Real.log (17619 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (171056501 / 250000000) ≤ -Real.log (1000000 / 1982237) ∧
    -Real.log (1000000 / 1982237) ≤ (136845201 / 200000000) := by
  have h := checkLog_sound (w := (982237 / 2982237)) (n := 12)
    (lo := (171056501 / 250000000)) (hi := (136845201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982237 / 1000000) = 1/(1000000 / 1982237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (171056501 / 250000000) (136845201 / 200000000) (Real.log (1982237 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982237 / 1000000) = -Real.log (1000000 / 1982237) := by
    rw [show ((1982237 / 1000000) : ℝ) = ((1000000 / 1982237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4030637633 / 1000000000) ≤ -Real.log (17763 / 1000000) ∧
    -Real.log (17763 / 1000000) ≤ (4030637639 / 1000000000) := by
  have h := checkLog_sound (w := (13487 / 49013)) (n := 12)
    (lo := (564901733 / 1000000000)) (hi := (282450867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17763) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17763) = 1/(17763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4030637639 / 1000000000) (-4030637633 / 1000000000) (Real.log (17763 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684265353 / 1000000000) ≤ -Real.log (200000 / 396463) ∧
    -Real.log (200000 / 396463) ≤ (342132677 / 500000000) := by
  have h := checkLog_sound (w := (196463 / 596463)) (n := 12)
    (lo := (684265353 / 1000000000)) (hi := (342132677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396463 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396463 / 200000) = 1/(200000 / 396463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684265353 / 1000000000) (342132677 / 500000000) (Real.log (396463 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (396463 / 200000) = -Real.log (200000 / 396463) := by
    rw [show ((396463 / 200000) : ℝ) = ((200000 / 396463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4035038453 / 1000000000) ≤ -Real.log (3537 / 200000) ∧
    -Real.log (3537 / 200000) ≤ (4035038459 / 1000000000) := by
  have h := checkLog_sound (w := (2713 / 9787)) (n := 12)
    (lo := (569302553 / 1000000000)) (hi := (284651277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3537) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3537) = 1/(3537 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4035038459 / 1000000000) (-4035038453 / 1000000000) (Real.log (3537 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (471873347 / 100000000) ≤ -Real.log (62500000000 / 7001642413111) ∧
    -Real.log (62500000000 / 7001642413111) ≤ (4718733477 / 1000000000) := by
  have h := checkLog_sound (w := (3001642413111 / 11001642413111)) (n := 12)
    (lo := (55985039 / 100000000)) (hi := (559850391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7001642413111 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7001642413111 / 4000000000000) = 1/(62500000000 / 7001642413111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (471873347 / 100000000) (4718733477 / 1000000000) (Real.log (7001642413111 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7001642413111 / 62500000000) = -Real.log (62500000000 / 7001642413111) := by
    rw [show ((7001642413111 / 62500000000) : ℝ) = ((62500000000 / 7001642413111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4723076057 / 1000000000) ≤ -Real.log (125000000000 / 14064227538453) ∧
    -Real.log (125000000000 / 14064227538453) ≤ (147596127 / 31250000) := by
  have h := checkLog_sound (w := (6064227538453 / 22064227538453)) (n := 12)
    (lo := (564192977 / 1000000000)) (hi := (282096489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14064227538453 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14064227538453 / 8000000000000) = 1/(125000000000 / 14064227538453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4723076057 / 1000000000) (147596127 / 31250000) (Real.log (14064227538453 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14064227538453 / 125000000000) = -Real.log (125000000000 / 14064227538453) := by
    rw [show ((14064227538453 / 125000000000) : ℝ) = ((125000000000 / 14064227538453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2357431819 / 500000000) ≤ -Real.log (500000000000 / 55796796712267) ∧
    -Real.log (500000000000 / 55796796712267) ≤ (942972729 / 200000000) := by
  have h := checkLog_sound (w := (23796796712267 / 87796796712267)) (n := 12)
    (lo := (277990279 / 500000000)) (hi := (555980559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55796796712267 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55796796712267 / 32000000000000) = 1/(500000000000 / 55796796712267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2357431819 / 500000000) (942972729 / 200000000) (Real.log (55796796712267 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (55796796712267 / 500000000000) = -Real.log (500000000000 / 55796796712267) := by
    rw [show ((55796796712267 / 500000000000) : ℝ) = ((500000000000 / 55796796712267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2359651903 / 500000000) ≤ -Real.log (250000000000 / 28022547356517) ∧
    -Real.log (250000000000 / 28022547356517) ≤ (4719303813 / 1000000000) := by
  have h := checkLog_sound (w := (12022547356517 / 44022547356517)) (n := 12)
    (lo := (280210363 / 500000000)) (hi := (560420727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28022547356517 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28022547356517 / 16000000000000) = 1/(250000000000 / 28022547356517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2359651903 / 500000000) (4719303813 / 1000000000) (Real.log (28022547356517 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28022547356517 / 250000000000) = -Real.log (250000000000 / 28022547356517) := by
    rw [show ((28022547356517 / 250000000000) : ℝ) = ((250000000000 / 28022547356517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0008

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0009Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0009
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

theorem reflection_log_1_neg : (341337529 / 500000000) ≤ -Real.log (1000000000000 / 1979165039063) ∧
    -Real.log (1000000000000 / 1979165039063) ≤ (682675059 / 1000000000) := by
  have h := checkLog_sound (w := (979165039063 / 2979165039063)) (n := 12)
    (lo := (341337529 / 500000000)) (hi := (682675059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979165039063 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979165039063 / 1000000000000) = 1/(1000000000000 / 1979165039063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341337529 / 500000000) (682675059 / 1000000000) (Real.log (1979165039063 / 1000000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1979165039063 / 1000000000000) = -Real.log (1000000000000 / 1979165039063) := by
    rw [show ((1979165039063 / 1000000000000) : ℝ) = ((1000000000000 / 1979165039063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1935561443 / 500000000) ≤ -Real.log (20834960937 / 1000000000000) ∧
    -Real.log (20834960937 / 1000000000000) ≤ (967780723 / 250000000) := by
  have h := checkLog_sound (w := (10415039063 / 52084960937)) (n := 12)
    (lo := (202693493 / 500000000)) (hi := (405386987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20834960937) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20834960937) = 1/(20834960937 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-967780723 / 250000000) (-1935561443 / 500000000) (Real.log (20834960937 / 1000000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341314091 / 500000000) ≤ -Real.log (102400 / 202657) ∧
    -Real.log (102400 / 202657) ≤ (682628183 / 1000000000) := by
  have h := checkLog_sound (w := (100257 / 305057)) (n := 12)
    (lo := (341314091 / 500000000)) (hi := (682628183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202657 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202657 / 102400) = 1/(102400 / 202657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (341314091 / 500000000) (682628183 / 1000000000) (Real.log (202657 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202657 / 102400) = -Real.log (102400 / 202657) := by
    rw [show ((202657 / 102400) : ℝ) = ((102400 / 202657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3866679993 / 1000000000) ≤ -Real.log (2143 / 102400) ∧
    -Real.log (2143 / 102400) ≤ (3866679999 / 1000000000) := by
  have h := checkLog_sound (w := (1057 / 5343)) (n := 12)
    (lo := (400944093 / 1000000000)) (hi := (200472047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2143) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2143) = 1/(2143 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3866679999 / 1000000000) (-3866679993 / 1000000000) (Real.log (2143 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672092109 / 1000000000) ≤ -Real.log (102400 / 200533) ∧
    -Real.log (102400 / 200533) ≤ (67209211 / 100000000) := by
  have h := checkLog_sound (w := (98133 / 302933)) (n := 12)
    (lo := (672092109 / 1000000000)) (hi := (67209211 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200533 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200533 / 102400) = 1/(102400 / 200533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672092109 / 1000000000) (67209211 / 100000000) (Real.log (200533 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200533 / 102400) = -Real.log (102400 / 200533) := by
    rw [show ((200533 / 102400) : ℝ) = ((102400 / 200533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1588987853 / 500000000) ≤ -Real.log (4267 / 102400) ∧
    -Real.log (4267 / 102400) ≤ (3177975711 / 1000000000) := by
  have h := checkLog_sound (w := (2133 / 10667)) (n := 12)
    (lo := (202693493 / 500000000)) (hi := (405386987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4267) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4267) = 1/(4267 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3177975711 / 1000000000) (-1588987853 / 500000000) (Real.log (4267 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671997357 / 1000000000) ≤ -Real.log (51200 / 100257) ∧
    -Real.log (51200 / 100257) ≤ (335998679 / 500000000) := by
  have h := checkLog_sound (w := (49057 / 151457)) (n := 12)
    (lo := (671997357 / 1000000000)) (hi := (335998679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100257 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100257 / 51200) = 1/(51200 / 100257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (671997357 / 1000000000) (335998679 / 500000000) (Real.log (100257 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100257 / 51200) = -Real.log (51200 / 100257) := by
    rw [show ((100257 / 51200) : ℝ) = ((51200 / 100257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3173532813 / 1000000000) ≤ -Real.log (2143 / 51200) ∧
    -Real.log (2143 / 51200) ≤ (1586766409 / 500000000) := by
  have h := checkLog_sound (w := (1057 / 5343)) (n := 12)
    (lo := (400944093 / 1000000000)) (hi := (200472047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2143) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2143) = 1/(2143 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1586766409 / 500000000) (-3173532813 / 1000000000) (Real.log (2143 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684221969 / 1000000000) ≤ -Real.log (1000000 / 1982229) ∧
    -Real.log (1000000 / 1982229) ≤ (68422197 / 100000000) := by
  have h := checkLog_sound (w := (982229 / 2982229)) (n := 12)
    (lo := (684221969 / 1000000000)) (hi := (68422197 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982229 / 1000000) = 1/(1000000 / 1982229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684221969 / 1000000000) (68422197 / 100000000) (Real.log (1982229 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982229 / 1000000) = -Real.log (1000000 / 1982229) := by
    rw [show ((1982229 / 1000000) : ℝ) = ((1000000 / 1982229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (25188671 / 6250000) ≤ -Real.log (17771 / 1000000) ∧
    -Real.log (17771 / 1000000) ≤ (2015093683 / 500000000) := by
  have h := checkLog_sound (w := (13479 / 49021)) (n := 12)
    (lo := (28222573 / 50000000)) (hi := (564451461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17771) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17771) = 1/(17771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2015093683 / 500000000) (-25188671 / 6250000) (Real.log (17771 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684260813 / 1000000000) ≤ -Real.log (500000 / 991153) ∧
    -Real.log (500000 / 991153) ≤ (342130407 / 500000000) := by
  have h := checkLog_sound (w := (491153 / 1491153)) (n := 12)
    (lo := (684260813 / 1000000000)) (hi := (342130407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991153 / 500000) = 1/(500000 / 991153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684260813 / 1000000000) (342130407 / 500000000) (Real.log (991153 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (991153 / 500000) = -Real.log (500000 / 991153) := by
    rw [show ((991153 / 500000) : ℝ) = ((500000 / 991153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4034529677 / 1000000000) ≤ -Real.log (8847 / 500000) ∧
    -Real.log (8847 / 500000) ≤ (4034529683 / 1000000000) := by
  have h := checkLog_sound (w := (3389 / 12236)) (n := 12)
    (lo := (568793777 / 1000000000)) (hi := (284396889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8847) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8847) = 1/(8847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4034529683 / 1000000000) (-4034529677 / 1000000000) (Real.log (8847 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684187663 / 1000000000) ≤ -Real.log (1000000 / 1982161) ∧
    -Real.log (1000000 / 1982161) ≤ (42761729 / 62500000) := by
  have h := checkLog_sound (w := (982161 / 2982161)) (n := 12)
    (lo := (684187663 / 1000000000)) (hi := (42761729 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982161 / 1000000) = 1/(1000000 / 1982161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684187663 / 1000000000) (42761729 / 62500000) (Real.log (1982161 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982161 / 1000000) = -Real.log (1000000 / 1982161) := by
    rw [show ((1982161 / 1000000) : ℝ) = ((1000000 / 1982161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1006592051 / 250000000) ≤ -Real.log (17839 / 1000000) ∧
    -Real.log (17839 / 1000000) ≤ (402636821 / 100000000) := by
  have h := checkLog_sound (w := (13411 / 49089)) (n := 12)
    (lo := (35039519 / 62500000)) (hi := (112126461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17839) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17839) = 1/(17839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-402636821 / 100000000) (-1006592051 / 250000000) (Real.log (17839 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684226509 / 1000000000) ≤ -Real.log (500000 / 991119) ∧
    -Real.log (500000 / 991119) ≤ (68422651 / 100000000) := by
  have h := checkLog_sound (w := (491119 / 1491119)) (n := 12)
    (lo := (684226509 / 1000000000)) (hi := (68422651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991119 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991119 / 500000) = 1/(500000 / 991119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684226509 / 1000000000) (68422651 / 100000000) (Real.log (991119 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (991119 / 500000) = -Real.log (500000 / 991119) := by
    rw [show ((991119 / 500000) : ℝ) = ((500000 / 991119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1007673483 / 250000000) ≤ -Real.log (8881 / 500000) ∧
    -Real.log (8881 / 500000) ≤ (2015346969 / 500000000) := by
  have h := checkLog_sound (w := (3372 / 12253)) (n := 12)
    (lo := (35309877 / 62500000)) (hi := (564958033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8881) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8881) = 1/(8881 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2015346969 / 500000000) (-1007673483 / 250000000) (Real.log (8881 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4714409329 / 1000000000) ≤ -Real.log (500000000000 / 55771453491643) ∧
    -Real.log (500000000000 / 55771453491643) ≤ (589301167 / 125000000) := by
  have h := checkLog_sound (w := (23771453491643 / 87771453491643)) (n := 12)
    (lo := (555526249 / 1000000000)) (hi := (444421 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55771453491643 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55771453491643 / 32000000000000) = 1/(500000000000 / 55771453491643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4714409329 / 1000000000) (589301167 / 125000000) (Real.log (55771453491643 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (55771453491643 / 500000000000) = -Real.log (500000000000 / 55771453491643) := by
    rw [show ((55771453491643 / 500000000000) : ℝ) = ((500000000000 / 55771453491643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (471879049 / 100000000) ≤ -Real.log (500000000000 / 56016333220301) ∧
    -Real.log (500000000000 / 56016333220301) ≤ (4718790497 / 1000000000) := by
  have h := checkLog_sound (w := (24016333220301 / 88016333220301)) (n := 12)
    (lo := (55990741 / 100000000)) (hi := (559907411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56016333220301 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56016333220301 / 32000000000000) = 1/(500000000000 / 56016333220301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (471879049 / 100000000) (4718790497 / 1000000000) (Real.log (56016333220301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (56016333220301 / 500000000000) = -Real.log (500000000000 / 56016333220301) := by
    rw [show ((56016333220301 / 500000000000) : ℝ) = ((500000000000 / 56016333220301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4710555867 / 1000000000) ≤ -Real.log (250000000000 / 27778476932563) ∧
    -Real.log (250000000000 / 27778476932563) ≤ (2355277937 / 500000000) := by
  have h := checkLog_sound (w := (11778476932563 / 43778476932563)) (n := 12)
    (lo := (551672787 / 1000000000)) (hi := (137918197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27778476932563 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27778476932563 / 16000000000000) = 1/(250000000000 / 27778476932563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4710555867 / 1000000000) (2355277937 / 500000000) (Real.log (27778476932563 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (27778476932563 / 250000000000) = -Real.log (250000000000 / 27778476932563) := by
    rw [show ((27778476932563 / 250000000000) : ℝ) = ((250000000000 / 27778476932563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4714920441 / 1000000000) ≤ -Real.log (500000000000 / 55799966220021) ∧
    -Real.log (500000000000 / 55799966220021) ≤ (9208829 / 1953125) := by
  have h := checkLog_sound (w := (23799966220021 / 87799966220021)) (n := 12)
    (lo := (556037361 / 1000000000)) (hi := (278018681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55799966220021 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55799966220021 / 32000000000000) = 1/(500000000000 / 55799966220021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4714920441 / 1000000000) (9208829 / 1953125) (Real.log (55799966220021 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (55799966220021 / 500000000000) = -Real.log (500000000000 / 55799966220021) := by
    rw [show ((55799966220021 / 500000000000) : ℝ) = ((500000000000 / 55799966220021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0009

end


