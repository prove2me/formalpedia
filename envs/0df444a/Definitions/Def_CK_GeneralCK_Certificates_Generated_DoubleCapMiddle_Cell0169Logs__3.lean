-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0169Logs__3
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0169Logs__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:39:03.340449+00:00
-- url     : https://prove2.me/theorems/13f7d6fa-781d-459e-94d4-4760e392c497
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0169Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0170Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0169Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0170Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0171Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0169Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0170Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0171Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0169Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0170Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0171Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0169Logs (+2 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0170Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0171Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0169Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0169
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

theorem reflection_log_1_neg : (279494347 / 1000000000) ≤ -Real.log (5120 / 6771) ∧
    -Real.log (5120 / 6771) ≤ (69873587 / 250000000) := by
  have h := checkLog_sound (w := (1651 / 11891)) (n := 12)
    (lo := (279494347 / 1000000000)) (hi := (69873587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6771 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6771 / 5120) = 1/(5120 / 6771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (279494347 / 1000000000) (69873587 / 250000000) (Real.log (6771 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6771 / 5120) = -Real.log (5120 / 6771) := by
    rw [show ((6771 / 5120) : ℝ) = ((5120 / 6771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (389288071 / 1000000000) ≤ -Real.log (3469 / 5120) ∧
    -Real.log (3469 / 5120) ≤ (48661009 / 125000000) := by
  have h := checkLog_sound (w := (1651 / 8589)) (n := 12)
    (lo := (389288071 / 1000000000)) (hi := (48661009 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3469) = 1/(3469 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-48661009 / 125000000) (-389288071 / 1000000000) (Real.log (3469 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (279051183 / 1000000000) ≤ -Real.log (320 / 423) ∧
    -Real.log (320 / 423) ≤ (17440699 / 62500000) := by
  have h := checkLog_sound (w := (103 / 743)) (n := 12)
    (lo := (279051183 / 1000000000)) (hi := (17440699 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((423 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(423 / 320) = 1/(320 / 423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (279051183 / 1000000000) (17440699 / 62500000) (Real.log (423 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (423 / 320) = -Real.log (320 / 423) := by
    rw [show ((423 / 320) : ℝ) = ((320 / 423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (194211821 / 500000000) ≤ -Real.log (217 / 320) ∧
    -Real.log (217 / 320) ≤ (388423643 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 537)) (n := 12)
    (lo := (194211821 / 500000000)) (hi := (388423643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 217) = 1/(217 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-388423643 / 1000000000) (-194211821 / 500000000) (Real.log (217 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49769289 / 100000000) ≤ -Real.log (2560 / 4211) ∧
    -Real.log (2560 / 4211) ≤ (497692891 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 6771)) (n := 12)
    (lo := (49769289 / 100000000)) (hi := (497692891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4211 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4211 / 2560) = 1/(2560 / 4211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49769289 / 100000000) (497692891 / 1000000000) (Real.log (4211 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4211 / 2560) = -Real.log (2560 / 4211) := by
    rw [show ((4211 / 2560) : ℝ) = ((2560 / 4211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (517708721 / 500000000) ≤ -Real.log (909 / 2560) ∧
    -Real.log (909 / 2560) ≤ (258854361 / 250000000) := by
  have h := checkLog_sound (w := (371 / 2189)) (n := 12)
    (lo := (171135131 / 500000000)) (hi := (342270263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 909) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 909) = 1/(909 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-258854361 / 250000000) (-517708721 / 500000000) (Real.log (909 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (62122527 / 125000000) ≤ -Real.log (160 / 263) ∧
    -Real.log (160 / 263) ≤ (496980217 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 423)) (n := 12)
    (lo := (62122527 / 125000000)) (hi := (496980217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263 / 160) = 1/(160 / 263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (62122527 / 125000000) (496980217 / 1000000000) (Real.log (263 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (263 / 160) = -Real.log (160 / 263) := by
    rw [show ((263 / 160) : ℝ) = ((160 / 263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (516061273 / 500000000) ≤ -Real.log (57 / 160) ∧
    -Real.log (57 / 160) ≤ (258030637 / 250000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 57) = 1/(57 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-258030637 / 250000000) (-516061273 / 500000000) (Real.log (57 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (381737829 / 1000000000) ≤ -Real.log (250000 / 366207) ∧
    -Real.log (250000 / 366207) ≤ (38173783 / 100000000) := by
  have h := checkLog_sound (w := (116207 / 616207)) (n := 12)
    (lo := (381737829 / 1000000000)) (hi := (38173783 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366207 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366207 / 250000) = 1/(250000 / 366207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (381737829 / 1000000000) (38173783 / 100000000) (Real.log (366207 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (366207 / 250000) = -Real.log (250000 / 366207) := by
    rw [show ((366207 / 250000) : ℝ) = ((250000 / 366207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (39072943 / 62500000) ≤ -Real.log (133793 / 250000) ∧
    -Real.log (133793 / 250000) ≤ (625167089 / 1000000000) := by
  have h := checkLog_sound (w := (116207 / 383793)) (n := 12)
    (lo := (39072943 / 62500000)) (hi := (625167089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 133793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 133793) = 1/(133793 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-625167089 / 1000000000) (-39072943 / 62500000) (Real.log (133793 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (382345907 / 1000000000) ≤ -Real.log (1000000 / 1465719) ∧
    -Real.log (1000000 / 1465719) ≤ (95586477 / 250000000) := by
  have h := checkLog_sound (w := (465719 / 2465719)) (n := 12)
    (lo := (382345907 / 1000000000)) (hi := (95586477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1465719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1465719 / 1000000) = 1/(1000000 / 1465719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (382345907 / 1000000000) (95586477 / 250000000) (Real.log (1465719 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1465719 / 1000000) = -Real.log (1000000 / 1465719) := by
    rw [show ((1465719 / 1000000) : ℝ) = ((1000000 / 1465719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (626833361 / 1000000000) ≤ -Real.log (534281 / 1000000) ∧
    -Real.log (534281 / 1000000) ≤ (313416681 / 500000000) := by
  have h := checkLog_sound (w := (465719 / 1534281)) (n := 12)
    (lo := (626833361 / 1000000000)) (hi := (313416681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 534281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 534281) = 1/(534281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-313416681 / 500000000) (-626833361 / 1000000000) (Real.log (534281 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (59951573 / 200000000) ≤ -Real.log (250000 / 337383) ∧
    -Real.log (250000 / 337383) ≤ (149878933 / 500000000) := by
  have h := checkLog_sound (w := (87383 / 587383)) (n := 12)
    (lo := (59951573 / 200000000)) (hi := (149878933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337383 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337383 / 250000) = 1/(250000 / 337383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (59951573 / 200000000) (149878933 / 500000000) (Real.log (337383 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (337383 / 250000) = -Real.log (250000 / 337383) := by
    rw [show ((337383 / 250000) : ℝ) = ((250000 / 337383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (17202527 / 40000000) ≤ -Real.log (162617 / 250000) ∧
    -Real.log (162617 / 250000) ≤ (53757897 / 125000000) := by
  have h := checkLog_sound (w := (87383 / 412617)) (n := 12)
    (lo := (17202527 / 40000000)) (hi := (53757897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 162617) = 1/(162617 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-53757897 / 125000000) (-17202527 / 40000000) (Real.log (162617 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (150158581 / 500000000) ≤ -Real.log (1000000 / 1350287) ∧
    -Real.log (1000000 / 1350287) ≤ (300317163 / 1000000000) := by
  have h := checkLog_sound (w := (350287 / 2350287)) (n := 12)
    (lo := (150158581 / 500000000)) (hi := (300317163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350287 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350287 / 1000000) = 1/(1000000 / 1350287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (150158581 / 500000000) (300317163 / 1000000000) (Real.log (1350287 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1350287 / 1000000) = -Real.log (1000000 / 1350287) := by
    rw [show ((1350287 / 1000000) : ℝ) = ((1000000 / 1350287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53903069 / 125000000) ≤ -Real.log (649713 / 1000000) ∧
    -Real.log (649713 / 1000000) ≤ (431224553 / 1000000000) := by
  have h := checkLog_sound (w := (350287 / 1649713)) (n := 12)
    (lo := (53903069 / 125000000)) (hi := (431224553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649713) = 1/(649713 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-431224553 / 1000000000) (-53903069 / 125000000) (Real.log (649713 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1006904917 / 1000000000) ≤ -Real.log (1953125000 / 5345930257) ∧
    -Real.log (1953125000 / 5345930257) ≤ (1006904919 / 1000000000) := by
  have h := checkLog_sound (w := (1439680257 / 9252180257)) (n := 12)
    (lo := (313757737 / 1000000000)) (hi := (156878869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5345930257 / 3906250000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5345930257 / 3906250000) = 1/(1953125000 / 5345930257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1006904917 / 1000000000) (1006904919 / 1000000000) (Real.log (5345930257 / 1953125000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5345930257 / 1953125000) = -Real.log (1953125000 / 5345930257) := by
    rw [show ((5345930257 / 1953125000) : ℝ) = ((1953125000 / 5345930257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1009179267 / 1000000000) ≤ -Real.log (31250000000 / 85729641799) ∧
    -Real.log (31250000000 / 85729641799) ≤ (1009179269 / 1000000000) := by
  have h := checkLog_sound (w := (23229641799 / 148229641799)) (n := 12)
    (lo := (316032087 / 1000000000)) (hi := (39504011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85729641799 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(85729641799 / 62500000000) = 1/(31250000000 / 85729641799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1009179267 / 1000000000) (1009179269 / 1000000000) (Real.log (85729641799 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (85729641799 / 31250000000) = -Real.log (31250000000 / 85729641799) := by
    rw [show ((85729641799 / 31250000000) : ℝ) = ((31250000000 / 85729641799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9122763 / 12500000) ≤ -Real.log (250000000000 / 518677321559) ∧
    -Real.log (250000000000 / 518677321559) ≤ (364910521 / 500000000) := by
  have h := checkLog_sound (w := (18677321559 / 1018677321559)) (n := 12)
    (lo := (1833693 / 50000000)) (hi := (36673861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((518677321559 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(518677321559 / 500000000000) = 1/(250000000000 / 518677321559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (9122763 / 12500000) (364910521 / 500000000) (Real.log (518677321559 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (518677321559 / 250000000000) = -Real.log (250000000000 / 518677321559) := by
    rw [show ((518677321559 / 250000000000) : ℝ) = ((250000000000 / 518677321559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (731541713 / 1000000000) ≤ -Real.log (125000000000 / 259785282117) ∧
    -Real.log (125000000000 / 259785282117) ≤ (146308343 / 200000000) := by
  have h := checkLog_sound (w := (9785282117 / 509785282117)) (n := 12)
    (lo := (38394533 / 1000000000)) (hi := (19197267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259785282117 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259785282117 / 250000000000) = 1/(125000000000 / 259785282117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (731541713 / 1000000000) (146308343 / 200000000) (Real.log (259785282117 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (259785282117 / 125000000000) = -Real.log (125000000000 / 259785282117) := by
    rw [show ((259785282117 / 125000000000) : ℝ) = ((125000000000 / 259785282117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0169

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0170Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0170
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

theorem reflection_log_1_neg : (279051183 / 1000000000) ≤ -Real.log (320 / 423) ∧
    -Real.log (320 / 423) ≤ (17440699 / 62500000) := by
  have h := checkLog_sound (w := (103 / 743)) (n := 12)
    (lo := (279051183 / 1000000000)) (hi := (17440699 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((423 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(423 / 320) = 1/(320 / 423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (279051183 / 1000000000) (17440699 / 62500000) (Real.log (423 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (423 / 320) = -Real.log (320 / 423) := by
    rw [show ((423 / 320) : ℝ) = ((320 / 423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (194211821 / 500000000) ≤ -Real.log (217 / 320) ∧
    -Real.log (217 / 320) ≤ (388423643 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 537)) (n := 12)
    (lo := (194211821 / 500000000)) (hi := (388423643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 217) = 1/(217 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-388423643 / 1000000000) (-194211821 / 500000000) (Real.log (217 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (139303911 / 500000000) ≤ -Real.log (1024 / 1353) ∧
    -Real.log (1024 / 1353) ≤ (278607823 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2377)) (n := 12)
    (lo := (139303911 / 500000000)) (hi := (278607823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353 / 1024) = 1/(1024 / 1353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (139303911 / 500000000) (278607823 / 1000000000) (Real.log (1353 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1353 / 1024) = -Real.log (1024 / 1353) := by
    rw [show ((1353 / 1024) : ℝ) = ((1024 / 1353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (9688999 / 25000000) ≤ -Real.log (695 / 1024) ∧
    -Real.log (695 / 1024) ≤ (387559961 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 1719)) (n := 12)
    (lo := (9688999 / 25000000)) (hi := (387559961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 695) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 695) = 1/(695 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-387559961 / 1000000000) (-9688999 / 25000000) (Real.log (695 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (62122527 / 125000000) ≤ -Real.log (160 / 263) ∧
    -Real.log (160 / 263) ≤ (496980217 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 423)) (n := 12)
    (lo := (62122527 / 125000000)) (hi := (496980217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263 / 160) = 1/(160 / 263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (62122527 / 125000000) (496980217 / 1000000000) (Real.log (263 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (263 / 160) = -Real.log (160 / 263) := by
    rw [show ((263 / 160) : ℝ) = ((160 / 263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (516061273 / 500000000) ≤ -Real.log (57 / 160) ∧
    -Real.log (57 / 160) ≤ (258030637 / 250000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 57) = 1/(57 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-258030637 / 250000000) (-516061273 / 500000000) (Real.log (57 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (248133517 / 500000000) ≤ -Real.log (512 / 841) ∧
    -Real.log (512 / 841) ≤ (99253407 / 200000000) := by
  have h := checkLog_sound (w := (329 / 1353)) (n := 12)
    (lo := (248133517 / 500000000)) (hi := (99253407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841 / 512) = 1/(512 / 841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (248133517 / 500000000) (99253407 / 200000000) (Real.log (841 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (841 / 512) = -Real.log (512 / 841) := by
    rw [show ((841 / 512) : ℝ) = ((512 / 841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1028838471 / 1000000000) ≤ -Real.log (183 / 512) ∧
    -Real.log (183 / 512) ≤ (1028838473 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 439)) (n := 12)
    (lo := (335691291 / 1000000000)) (hi := (83922823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 183) = 1/(183 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1028838473 / 1000000000) (-1028838471 / 1000000000) (Real.log (183 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (23820629 / 62500000) ≤ -Real.log (500000 / 731969) ∧
    -Real.log (500000 / 731969) ≤ (76226013 / 200000000) := by
  have h := checkLog_sound (w := (231969 / 1231969)) (n := 12)
    (lo := (23820629 / 62500000)) (hi := (76226013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731969 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731969 / 500000) = 1/(500000 / 731969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (23820629 / 62500000) (76226013 / 200000000) (Real.log (731969 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (731969 / 500000) = -Real.log (500000 / 731969) := by
    rw [show ((731969 / 500000) : ℝ) = ((500000 / 731969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (155876363 / 250000000) ≤ -Real.log (268031 / 500000) ∧
    -Real.log (268031 / 500000) ≤ (623505453 / 1000000000) := by
  have h := checkLog_sound (w := (231969 / 768031)) (n := 12)
    (lo := (155876363 / 250000000)) (hi := (623505453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 268031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 268031) = 1/(268031 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-623505453 / 1000000000) (-155876363 / 250000000) (Real.log (268031 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (23858657 / 62500000) ≤ -Real.log (1000000 / 1464829) ∧
    -Real.log (1000000 / 1464829) ≤ (381738513 / 1000000000) := by
  have h := checkLog_sound (w := (464829 / 2464829)) (n := 12)
    (lo := (23858657 / 62500000)) (hi := (381738513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1464829 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1464829 / 1000000) = 1/(1000000 / 1464829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (23858657 / 62500000) (381738513 / 1000000000) (Real.log (1464829 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1464829 / 1000000) = -Real.log (1000000 / 1464829) := by
    rw [show ((1464829 / 1000000) : ℝ) = ((1000000 / 1464829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (156292239 / 250000000) ≤ -Real.log (535171 / 1000000) ∧
    -Real.log (535171 / 1000000) ≤ (625168957 / 1000000000) := by
  have h := checkLog_sound (w := (464829 / 1535171)) (n := 12)
    (lo := (156292239 / 250000000)) (hi := (625168957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 535171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 535171) = 1/(535171 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-625168957 / 1000000000) (-156292239 / 250000000) (Real.log (535171 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (149599869 / 500000000) ≤ -Real.log (1000000 / 1348779) ∧
    -Real.log (1000000 / 1348779) ≤ (299199739 / 1000000000) := by
  have h := checkLog_sound (w := (348779 / 2348779)) (n := 12)
    (lo := (149599869 / 500000000)) (hi := (299199739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1348779 / 1000000) = 1/(1000000 / 1348779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (149599869 / 500000000) (299199739 / 1000000000) (Real.log (1348779 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1348779 / 1000000) = -Real.log (1000000 / 1348779) := by
    rw [show ((1348779 / 1000000) : ℝ) = ((1000000 / 1348779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (53613277 / 125000000) ≤ -Real.log (651221 / 1000000) ∧
    -Real.log (651221 / 1000000) ≤ (428906217 / 1000000000) := by
  have h := checkLog_sound (w := (348779 / 1651221)) (n := 12)
    (lo := (53613277 / 125000000)) (hi := (428906217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 651221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 651221) = 1/(651221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-428906217 / 1000000000) (-53613277 / 125000000) (Real.log (651221 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (149879303 / 500000000) ≤ -Real.log (1000000 / 1349533) ∧
    -Real.log (1000000 / 1349533) ≤ (299758607 / 1000000000) := by
  have h := checkLog_sound (w := (349533 / 2349533)) (n := 12)
    (lo := (149879303 / 500000000)) (hi := (299758607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349533 / 1000000) = 1/(1000000 / 1349533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (149879303 / 500000000) (299758607 / 1000000000) (Real.log (1349533 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1349533 / 1000000) = -Real.log (1000000 / 1349533) := by
    rw [show ((1349533 / 1000000) : ℝ) = ((1000000 / 1349533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53758089 / 125000000) ≤ -Real.log (650467 / 1000000) ∧
    -Real.log (650467 / 1000000) ≤ (430064713 / 1000000000) := by
  have h := checkLog_sound (w := (349533 / 1650467)) (n := 12)
    (lo := (53758089 / 125000000)) (hi := (430064713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 650467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 650467) = 1/(650467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-430064713 / 1000000000) (-53758089 / 125000000) (Real.log (650467 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1004635517 / 1000000000) ≤ -Real.log (62500000000 / 170681982681) ∧
    -Real.log (62500000000 / 170681982681) ≤ (1004635519 / 1000000000) := by
  have h := checkLog_sound (w := (45681982681 / 295681982681)) (n := 12)
    (lo := (311488337 / 1000000000)) (hi := (155744169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170681982681 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(170681982681 / 125000000000) = 1/(62500000000 / 170681982681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1004635517 / 1000000000) (1004635519 / 1000000000) (Real.log (170681982681 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (170681982681 / 62500000000) = -Real.log (62500000000 / 170681982681) := by
    rw [show ((170681982681 / 62500000000) : ℝ) = ((62500000000 / 170681982681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (251726867 / 250000000) ≤ -Real.log (500000000000 / 1368561637309) ∧
    -Real.log (500000000000 / 1368561637309) ≤ (100690747 / 100000000) := by
  have h := checkLog_sound (w := (368561637309 / 2368561637309)) (n := 12)
    (lo := (9805009 / 31250000)) (hi := (313760289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1368561637309 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1368561637309 / 1000000000000) = 1/(500000000000 / 1368561637309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (251726867 / 250000000) (100690747 / 100000000) (Real.log (1368561637309 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1368561637309 / 500000000000) = -Real.log (500000000000 / 1368561637309) := by
    rw [show ((1368561637309 / 500000000000) : ℝ) = ((500000000000 / 1368561637309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (364052977 / 500000000) ≤ -Real.log (500000000000 / 1035577016097) ∧
    -Real.log (500000000000 / 1035577016097) ≤ (182026489 / 250000000) := by
  have h := checkLog_sound (w := (35577016097 / 2035577016097)) (n := 12)
    (lo := (17479387 / 500000000)) (hi := (1398351 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1035577016097 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1035577016097 / 1000000000000) = 1/(500000000000 / 1035577016097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (364052977 / 500000000) (182026489 / 250000000) (Real.log (1035577016097 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1035577016097 / 500000000000) = -Real.log (500000000000 / 1035577016097) := by
    rw [show ((1035577016097 / 500000000000) : ℝ) = ((500000000000 / 1035577016097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (364911659 / 500000000) ≤ -Real.log (250000000000 / 518678503291) ∧
    -Real.log (250000000000 / 518678503291) ≤ (18245583 / 25000000) := by
  have h := checkLog_sound (w := (18678503291 / 1018678503291)) (n := 12)
    (lo := (18338069 / 500000000)) (hi := (36676139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((518678503291 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(518678503291 / 500000000000) = 1/(250000000000 / 518678503291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (364911659 / 500000000) (18245583 / 25000000) (Real.log (518678503291 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (518678503291 / 250000000000) = -Real.log (250000000000 / 518678503291) := by
    rw [show ((518678503291 / 250000000000) : ℝ) = ((250000000000 / 518678503291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0170

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0171Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0171
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

theorem reflection_log_1_neg : (139303911 / 500000000) ≤ -Real.log (1024 / 1353) ∧
    -Real.log (1024 / 1353) ≤ (278607823 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2377)) (n := 12)
    (lo := (139303911 / 500000000)) (hi := (278607823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353 / 1024) = 1/(1024 / 1353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (139303911 / 500000000) (278607823 / 1000000000) (Real.log (1353 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1353 / 1024) = -Real.log (1024 / 1353) := by
    rw [show ((1353 / 1024) : ℝ) = ((1024 / 1353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (9688999 / 25000000) ≤ -Real.log (695 / 1024) ∧
    -Real.log (695 / 1024) ≤ (387559961 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 1719)) (n := 12)
    (lo := (9688999 / 25000000)) (hi := (387559961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 695) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 695) = 1/(695 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-387559961 / 1000000000) (-9688999 / 25000000) (Real.log (695 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55632853 / 200000000) ≤ -Real.log (2560 / 3381) ∧
    -Real.log (2560 / 3381) ≤ (139082133 / 500000000) := by
  have h := checkLog_sound (w := (821 / 5941)) (n := 12)
    (lo := (55632853 / 200000000)) (hi := (139082133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3381 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3381 / 2560) = 1/(2560 / 3381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55632853 / 200000000) (139082133 / 500000000) (Real.log (3381 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3381 / 2560) = -Real.log (2560 / 3381) := by
    rw [show ((3381 / 2560) : ℝ) = ((2560 / 3381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (386697023 / 1000000000) ≤ -Real.log (1739 / 2560) ∧
    -Real.log (1739 / 2560) ≤ (6042141 / 15625000) := by
  have h := checkLog_sound (w := (821 / 4299)) (n := 12)
    (lo := (386697023 / 1000000000)) (hi := (6042141 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1739) = 1/(1739 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6042141 / 15625000) (-386697023 / 1000000000) (Real.log (1739 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (248133517 / 500000000) ≤ -Real.log (512 / 841) ∧
    -Real.log (512 / 841) ≤ (99253407 / 200000000) := by
  have h := checkLog_sound (w := (329 / 1353)) (n := 12)
    (lo := (248133517 / 500000000)) (hi := (99253407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841 / 512) = 1/(512 / 841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (248133517 / 500000000) (99253407 / 200000000) (Real.log (841 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (841 / 512) = -Real.log (512 / 841) := by
    rw [show ((841 / 512) : ℝ) = ((512 / 841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1028838471 / 1000000000) ≤ -Real.log (183 / 512) ∧
    -Real.log (183 / 512) ≤ (1028838473 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 439)) (n := 12)
    (lo := (335691291 / 1000000000)) (hi := (83922823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 183) = 1/(183 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1028838473 / 1000000000) (-1028838471 / 1000000000) (Real.log (183 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (495553343 / 1000000000) ≤ -Real.log (1280 / 2101) ∧
    -Real.log (1280 / 2101) ≤ (7743021 / 15625000) := by
  have h := checkLog_sound (w := (821 / 3381)) (n := 12)
    (lo := (495553343 / 1000000000)) (hi := (7743021 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2101 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2101 / 1280) = 1/(1280 / 2101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (495553343 / 1000000000) (7743021 / 15625000) (Real.log (2101 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2101 / 1280) = -Real.log (1280 / 2101) := by
    rw [show ((2101 / 1280) : ℝ) = ((1280 / 2101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (512782573 / 500000000) ≤ -Real.log (459 / 1280) ∧
    -Real.log (459 / 1280) ≤ (256391287 / 250000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 459) = 1/(459 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-256391287 / 250000000) (-512782573 / 500000000) (Real.log (459 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (190261307 / 500000000) ≤ -Real.log (1000000 / 1463049) ∧
    -Real.log (1000000 / 1463049) ≤ (76104523 / 200000000) := by
  have h := checkLog_sound (w := (463049 / 2463049)) (n := 12)
    (lo := (190261307 / 500000000)) (hi := (76104523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463049 / 1000000) = 1/(1000000 / 1463049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (190261307 / 500000000) (76104523 / 200000000) (Real.log (1463049 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1463049 / 1000000) = -Real.log (1000000 / 1463049) := by
    rw [show ((1463049 / 1000000) : ℝ) = ((1000000 / 1463049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (155462109 / 250000000) ≤ -Real.log (536951 / 1000000) ∧
    -Real.log (536951 / 1000000) ≤ (621848437 / 1000000000) := by
  have h := checkLog_sound (w := (463049 / 1536951)) (n := 12)
    (lo := (155462109 / 250000000)) (hi := (621848437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 536951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 536951) = 1/(536951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-621848437 / 1000000000) (-155462109 / 250000000) (Real.log (536951 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (95282687 / 250000000) ≤ -Real.log (1000000 / 1463939) ∧
    -Real.log (1000000 / 1463939) ≤ (381130749 / 1000000000) := by
  have h := checkLog_sound (w := (463939 / 2463939)) (n := 12)
    (lo := (95282687 / 250000000)) (hi := (381130749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463939 / 1000000) = 1/(1000000 / 1463939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (95282687 / 250000000) (381130749 / 1000000000) (Real.log (1463939 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1463939 / 1000000) = -Real.log (1000000 / 1463939) := by
    rw [show ((1463939 / 1000000) : ℝ) = ((1000000 / 1463939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (311753659 / 500000000) ≤ -Real.log (536061 / 1000000) ∧
    -Real.log (536061 / 1000000) ≤ (623507319 / 1000000000) := by
  have h := checkLog_sound (w := (463939 / 1536061)) (n := 12)
    (lo := (311753659 / 500000000)) (hi := (623507319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 536061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 536061) = 1/(536061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-623507319 / 1000000000) (-311753659 / 500000000) (Real.log (536061 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2986413 / 10000000) ≤ -Real.log (500000 / 674013) ∧
    -Real.log (500000 / 674013) ≤ (298641301 / 1000000000) := by
  have h := checkLog_sound (w := (174013 / 1174013)) (n := 12)
    (lo := (2986413 / 10000000)) (hi := (298641301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674013 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674013 / 500000) = 1/(500000 / 674013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2986413 / 10000000) (298641301 / 1000000000) (Real.log (674013 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (674013 / 500000) = -Real.log (500000 / 674013) := by
    rw [show ((674013 / 500000) : ℝ) = ((500000 / 674013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (85550119 / 200000000) ≤ -Real.log (325987 / 500000) ∧
    -Real.log (325987 / 500000) ≤ (106937649 / 250000000) := by
  have h := checkLog_sound (w := (174013 / 825987)) (n := 12)
    (lo := (85550119 / 200000000)) (hi := (106937649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 325987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 325987) = 1/(325987 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-106937649 / 250000000) (-85550119 / 200000000) (Real.log (325987 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1870003 / 6250000) ≤ -Real.log (50000 / 67439) ∧
    -Real.log (50000 / 67439) ≤ (299200481 / 1000000000) := by
  have h := checkLog_sound (w := (17439 / 117439)) (n := 12)
    (lo := (1870003 / 6250000)) (hi := (299200481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67439 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67439 / 50000) = 1/(50000 / 67439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1870003 / 6250000) (299200481 / 1000000000) (Real.log (67439 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (67439 / 50000) = -Real.log (50000 / 67439) := by
    rw [show ((67439 / 50000) : ℝ) = ((50000 / 67439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53613469 / 125000000) ≤ -Real.log (32561 / 50000) ∧
    -Real.log (32561 / 50000) ≤ (428907753 / 1000000000) := by
  have h := checkLog_sound (w := (17439 / 82561)) (n := 12)
    (lo := (53613469 / 125000000)) (hi := (428907753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 32561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 32561) = 1/(32561 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-428907753 / 1000000000) (-53613469 / 125000000) (Real.log (32561 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (20047421 / 20000000) ≤ -Real.log (500000000000 / 1362367329607) ∧
    -Real.log (500000000000 / 1362367329607) ≤ (250592763 / 250000000) := by
  have h := checkLog_sound (w := (362367329607 / 2362367329607)) (n := 12)
    (lo := (30922387 / 100000000)) (hi := (309223871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1362367329607 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1362367329607 / 1000000000000) = 1/(500000000000 / 1362367329607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (20047421 / 20000000) (250592763 / 250000000) (Real.log (1362367329607 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1362367329607 / 500000000000) = -Real.log (500000000000 / 1362367329607) := by
    rw [show ((1362367329607 / 500000000000) : ℝ) = ((500000000000 / 1362367329607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (200927613 / 200000000) ≤ -Real.log (500000000000 / 1365459341381) ∧
    -Real.log (500000000000 / 1365459341381) ≤ (1004638067 / 1000000000) := by
  have h := checkLog_sound (w := (365459341381 / 2365459341381)) (n := 12)
    (lo := (62298177 / 200000000)) (hi := (155745443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365459341381 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1365459341381 / 1000000000000) = 1/(500000000000 / 1365459341381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (200927613 / 200000000) (1004638067 / 1000000000) (Real.log (1365459341381 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1365459341381 / 500000000000) = -Real.log (500000000000 / 1365459341381) := by
    rw [show ((1365459341381 / 500000000000) : ℝ) = ((500000000000 / 1365459341381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (363195947 / 500000000) ≤ -Real.log (500000000000 / 1033803495231) ∧
    -Real.log (500000000000 / 1033803495231) ≤ (90798987 / 125000000) := by
  have h := checkLog_sound (w := (33803495231 / 2033803495231)) (n := 12)
    (lo := (16622357 / 500000000)) (hi := (6648943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033803495231 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033803495231 / 1000000000000) = 1/(500000000000 / 1033803495231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (363195947 / 500000000) (90798987 / 125000000) (Real.log (1033803495231 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1033803495231 / 500000000000) = -Real.log (500000000000 / 1033803495231) := by
    rw [show ((1033803495231 / 500000000000) : ℝ) = ((500000000000 / 1033803495231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (728108231 / 1000000000) ≤ -Real.log (250000000000 / 517789687049) ∧
    -Real.log (250000000000 / 517789687049) ≤ (728108233 / 1000000000) := by
  have h := checkLog_sound (w := (17789687049 / 1017789687049)) (n := 12)
    (lo := (34961051 / 1000000000)) (hi := (8740263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517789687049 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(517789687049 / 500000000000) = 1/(250000000000 / 517789687049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (728108231 / 1000000000) (728108233 / 1000000000) (Real.log (517789687049 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (517789687049 / 250000000000) = -Real.log (250000000000 / 517789687049) := by
    rw [show ((517789687049 / 250000000000) : ℝ) = ((250000000000 / 517789687049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0171

end


