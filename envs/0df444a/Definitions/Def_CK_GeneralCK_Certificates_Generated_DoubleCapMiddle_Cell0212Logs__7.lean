-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0212Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0212Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:33:03.074537+00:00
-- url     : https://prove2.me/theorems/970ecaba-8e86-4e6a-98d0-e4d1726c017c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0212Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0213Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0212Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0213Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0214Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0215Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0216Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0217Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0218Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0212Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0213Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0214Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0215Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0216Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0217Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0218Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0212Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0213Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0214Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0215Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0216Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0217Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0218Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0212Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0213Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0214Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0215Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0216Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0217Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0218Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0212Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0212
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

theorem reflection_log_1_neg : (260258683 / 1000000000) ≤ -Real.log (2560 / 3321) ∧
    -Real.log (2560 / 3321) ≤ (65064671 / 250000000) := by
  have h := checkLog_sound (w := (761 / 5881)) (n := 12)
    (lo := (260258683 / 1000000000)) (hi := (65064671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3321 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3321 / 2560) = 1/(2560 / 3321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (260258683 / 1000000000) (65064671 / 250000000) (Real.log (3321 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3321 / 2560) = -Real.log (2560 / 3321) := by
    rw [show ((3321 / 2560) : ℝ) = ((2560 / 3321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (352776303 / 1000000000) ≤ -Real.log (1799 / 2560) ∧
    -Real.log (1799 / 2560) ≤ (22048519 / 62500000) := by
  have h := checkLog_sound (w := (761 / 4359)) (n := 12)
    (lo := (352776303 / 1000000000)) (hi := (22048519 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1799) = 1/(1799 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22048519 / 62500000) (-352776303 / 1000000000) (Real.log (1799 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (25980691 / 100000000) ≤ -Real.log (5120 / 6639) ∧
    -Real.log (5120 / 6639) ≤ (259806911 / 1000000000) := by
  have h := checkLog_sound (w := (1519 / 11759)) (n := 12)
    (lo := (25980691 / 100000000)) (hi := (259806911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6639 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6639 / 5120) = 1/(5120 / 6639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (25980691 / 100000000) (259806911 / 1000000000) (Real.log (6639 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6639 / 5120) = -Real.log (5120 / 6639) := by
    rw [show ((6639 / 5120) : ℝ) = ((5120 / 6639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (175971427 / 500000000) ≤ -Real.log (3601 / 5120) ∧
    -Real.log (3601 / 5120) ≤ (70388571 / 200000000) := by
  have h := checkLog_sound (w := (1519 / 8721)) (n := 12)
    (lo := (175971427 / 500000000)) (hi := (70388571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3601) = 1/(3601 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-70388571 / 200000000) (-175971427 / 500000000) (Real.log (3601 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (93315961 / 200000000) ≤ -Real.log (1280 / 2041) ∧
    -Real.log (1280 / 2041) ≤ (233289903 / 500000000) := by
  have h := checkLog_sound (w := (761 / 3321)) (n := 12)
    (lo := (93315961 / 200000000)) (hi := (233289903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2041 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2041 / 1280) = 1/(1280 / 2041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (93315961 / 200000000) (233289903 / 500000000) (Real.log (2041 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2041 / 1280) = -Real.log (1280 / 2041) := by
    rw [show ((2041 / 1280) : ℝ) = ((1280 / 2041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (902711473 / 1000000000) ≤ -Real.log (519 / 1280) ∧
    -Real.log (519 / 1280) ≤ (36108459 / 40000000) := by
  have h := checkLog_sound (w := (121 / 1159)) (n := 12)
    (lo := (209564293 / 1000000000)) (hi := (104782147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 519) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 519) = 1/(519 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-36108459 / 40000000) (-902711473 / 1000000000) (Real.log (519 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (465844601 / 1000000000) ≤ -Real.log (2560 / 4079) ∧
    -Real.log (2560 / 4079) ≤ (232922301 / 500000000) := by
  have h := checkLog_sound (w := (1519 / 6639)) (n := 12)
    (lo := (465844601 / 1000000000)) (hi := (232922301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4079 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4079 / 2560) = 1/(2560 / 4079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (465844601 / 1000000000) (232922301 / 500000000) (Real.log (4079 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4079 / 2560) = -Real.log (2560 / 4079) := by
    rw [show ((4079 / 2560) : ℝ) = ((2560 / 4079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (224956367 / 250000000) ≤ -Real.log (1041 / 2560) ∧
    -Real.log (1041 / 2560) ≤ (89982547 / 100000000) := by
  have h := checkLog_sound (w := (239 / 2321)) (n := 12)
    (lo := (12917393 / 62500000)) (hi := (206678289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1041) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1041) = 1/(1041 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-89982547 / 100000000) (-224956367 / 250000000) (Real.log (1041 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (88866253 / 250000000) ≤ -Real.log (250000 / 356711) ∧
    -Real.log (250000 / 356711) ≤ (355465013 / 1000000000) := by
  have h := checkLog_sound (w := (106711 / 606711)) (n := 12)
    (lo := (88866253 / 250000000)) (hi := (355465013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356711 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(356711 / 250000) = 1/(250000 / 356711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (88866253 / 250000000) (355465013 / 1000000000) (Real.log (356711 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (356711 / 250000) = -Real.log (250000 / 356711) := by
    rw [show ((356711 / 250000) : ℝ) = ((250000 / 356711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (139149337 / 250000000) ≤ -Real.log (143289 / 250000) ∧
    -Real.log (143289 / 250000) ≤ (556597349 / 1000000000) := by
  have h := checkLog_sound (w := (106711 / 393289)) (n := 12)
    (lo := (139149337 / 250000000)) (hi := (556597349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 143289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 143289) = 1/(143289 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-556597349 / 1000000000) (-139149337 / 250000000) (Real.log (143289 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (356080167 / 1000000000) ≤ -Real.log (500000 / 713861) ∧
    -Real.log (500000 / 713861) ≤ (44510021 / 125000000) := by
  have h := checkLog_sound (w := (213861 / 1213861)) (n := 12)
    (lo := (356080167 / 1000000000)) (hi := (44510021 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713861 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713861 / 500000) = 1/(500000 / 713861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (356080167 / 1000000000) (44510021 / 125000000) (Real.log (713861 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (713861 / 500000) = -Real.log (500000 / 713861) := by
    rw [show ((713861 / 500000) : ℝ) = ((500000 / 713861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (558130391 / 1000000000) ≤ -Real.log (286139 / 500000) ∧
    -Real.log (286139 / 500000) ≤ (69766299 / 125000000) := by
  have h := checkLog_sound (w := (213861 / 786139)) (n := 12)
    (lo := (558130391 / 1000000000)) (hi := (69766299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 286139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 286139) = 1/(286139 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-69766299 / 125000000) (-558130391 / 1000000000) (Real.log (286139 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (275981891 / 1000000000) ≤ -Real.log (15625 / 20591) ∧
    -Real.log (15625 / 20591) ≤ (68995473 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 18108)) (n := 12)
    (lo := (275981891 / 1000000000)) (hi := (68995473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20591 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20591 / 15625) = 1/(15625 / 20591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (275981891 / 1000000000) (68995473 / 250000000) (Real.log (20591 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (20591 / 15625) = -Real.log (15625 / 20591) := by
    rw [show ((20591 / 15625) : ℝ) = ((15625 / 20591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (382467589 / 1000000000) ≤ -Real.log (10659 / 15625) ∧
    -Real.log (10659 / 15625) ≤ (38246759 / 100000000) := by
  have h := checkLog_sound (w := (2483 / 13142)) (n := 12)
    (lo := (382467589 / 1000000000)) (hi := (38246759 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10659) = 1/(10659 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38246759 / 100000000) (-382467589 / 1000000000) (Real.log (10659 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (69132593 / 250000000) ≤ -Real.log (1000000 / 1318547) ∧
    -Real.log (1000000 / 1318547) ≤ (276530373 / 1000000000) := by
  have h := checkLog_sound (w := (318547 / 2318547)) (n := 12)
    (lo := (69132593 / 250000000)) (hi := (276530373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1318547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1318547 / 1000000) = 1/(1000000 / 1318547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (69132593 / 250000000) (276530373 / 1000000000) (Real.log (1318547 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1318547 / 1000000) = -Real.log (1000000 / 1318547) := by
    rw [show ((1318547 / 1000000) : ℝ) = ((1000000 / 1318547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76705599 / 200000000) ≤ -Real.log (681453 / 1000000) ∧
    -Real.log (681453 / 1000000) ≤ (95881999 / 250000000) := by
  have h := checkLog_sound (w := (318547 / 1681453)) (n := 12)
    (lo := (76705599 / 200000000)) (hi := (95881999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 681453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 681453) = 1/(681453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-95881999 / 250000000) (-76705599 / 200000000) (Real.log (681453 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (912062359 / 1000000000) ≤ -Real.log (250000000000 / 622362847113) ∧
    -Real.log (250000000000 / 622362847113) ≤ (912062361 / 1000000000) := by
  have h := checkLog_sound (w := (122362847113 / 1122362847113)) (n := 12)
    (lo := (218915179 / 1000000000)) (hi := (10945759 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622362847113 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(622362847113 / 500000000000) = 1/(250000000000 / 622362847113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (912062359 / 1000000000) (912062361 / 1000000000) (Real.log (622362847113 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (622362847113 / 250000000000) = -Real.log (250000000000 / 622362847113) := by
    rw [show ((622362847113 / 250000000000) : ℝ) = ((250000000000 / 622362847113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (457105279 / 500000000) ≤ -Real.log (100000000000 / 249480497241) ∧
    -Real.log (100000000000 / 249480497241) ≤ (714227 / 781250) := by
  have h := checkLog_sound (w := (49480497241 / 449480497241)) (n := 12)
    (lo := (110531689 / 500000000)) (hi := (221063379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249480497241 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(249480497241 / 200000000000) = 1/(100000000000 / 249480497241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (457105279 / 500000000) (714227 / 781250) (Real.log (249480497241 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (249480497241 / 100000000000) = -Real.log (100000000000 / 249480497241) := by
    rw [show ((249480497241 / 100000000000) : ℝ) = ((100000000000 / 249480497241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (658449481 / 1000000000) ≤ -Real.log (50000000000 / 96589736373) ∧
    -Real.log (50000000000 / 96589736373) ≤ (329224741 / 500000000) := by
  have h := checkLog_sound (w := (46589736373 / 146589736373)) (n := 12)
    (lo := (658449481 / 1000000000)) (hi := (329224741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96589736373 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96589736373 / 50000000000) = 1/(50000000000 / 96589736373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (658449481 / 1000000000) (329224741 / 500000000) (Real.log (96589736373 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (96589736373 / 50000000000) = -Real.log (50000000000 / 96589736373) := by
    rw [show ((96589736373 / 50000000000) : ℝ) = ((50000000000 / 96589736373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2578353 / 3906250) ≤ -Real.log (250000000000 / 483726317149) ∧
    -Real.log (250000000000 / 483726317149) ≤ (660058369 / 1000000000) := by
  have h := checkLog_sound (w := (233726317149 / 733726317149)) (n := 12)
    (lo := (2578353 / 3906250)) (hi := (660058369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483726317149 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483726317149 / 250000000000) = 1/(250000000000 / 483726317149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2578353 / 3906250) (660058369 / 1000000000) (Real.log (483726317149 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (483726317149 / 250000000000) = -Real.log (250000000000 / 483726317149) := by
    rw [show ((483726317149 / 250000000000) : ℝ) = ((250000000000 / 483726317149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0212

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0213Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0213
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

theorem reflection_log_1_neg : (25980691 / 100000000) ≤ -Real.log (5120 / 6639) ∧
    -Real.log (5120 / 6639) ≤ (259806911 / 1000000000) := by
  have h := checkLog_sound (w := (1519 / 11759)) (n := 12)
    (lo := (25980691 / 100000000)) (hi := (259806911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6639 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6639 / 5120) = 1/(5120 / 6639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (25980691 / 100000000) (259806911 / 1000000000) (Real.log (6639 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6639 / 5120) = -Real.log (5120 / 6639) := by
    rw [show ((6639 / 5120) : ℝ) = ((5120 / 6639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (175971427 / 500000000) ≤ -Real.log (3601 / 5120) ∧
    -Real.log (3601 / 5120) ≤ (70388571 / 200000000) := by
  have h := checkLog_sound (w := (1519 / 8721)) (n := 12)
    (lo := (175971427 / 500000000)) (hi := (70388571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3601) = 1/(3601 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-70388571 / 200000000) (-175971427 / 500000000) (Real.log (3601 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (259354933 / 1000000000) ≤ -Real.log (1280 / 1659) ∧
    -Real.log (1280 / 1659) ≤ (129677467 / 500000000) := by
  have h := checkLog_sound (w := (379 / 2939)) (n := 12)
    (lo := (259354933 / 1000000000)) (hi := (129677467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1659 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1659 / 1280) = 1/(1280 / 1659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (259354933 / 1000000000) (129677467 / 500000000) (Real.log (1659 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1659 / 1280) = -Real.log (1280 / 1659) := by
    rw [show ((1659 / 1280) : ℝ) = ((1280 / 1659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (351110099 / 1000000000) ≤ -Real.log (901 / 1280) ∧
    -Real.log (901 / 1280) ≤ (3511101 / 10000000) := by
  have h := checkLog_sound (w := (379 / 2181)) (n := 12)
    (lo := (351110099 / 1000000000)) (hi := (3511101 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 901) = 1/(901 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3511101 / 10000000) (-351110099 / 1000000000) (Real.log (901 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (465844601 / 1000000000) ≤ -Real.log (2560 / 4079) ∧
    -Real.log (2560 / 4079) ≤ (232922301 / 500000000) := by
  have h := checkLog_sound (w := (1519 / 6639)) (n := 12)
    (lo := (465844601 / 1000000000)) (hi := (232922301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4079 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4079 / 2560) = 1/(2560 / 4079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (465844601 / 1000000000) (232922301 / 500000000) (Real.log (4079 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4079 / 2560) = -Real.log (2560 / 4079) := by
    rw [show ((4079 / 2560) : ℝ) = ((2560 / 4079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (224956367 / 250000000) ≤ -Real.log (1041 / 2560) ∧
    -Real.log (1041 / 2560) ≤ (89982547 / 100000000) := by
  have h := checkLog_sound (w := (239 / 2321)) (n := 12)
    (lo := (12917393 / 62500000)) (hi := (206678289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1041) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1041) = 1/(1041 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-89982547 / 100000000) (-224956367 / 250000000) (Real.log (1041 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (58138607 / 125000000) ≤ -Real.log (640 / 1019) ∧
    -Real.log (640 / 1019) ≤ (465108857 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1659)) (n := 12)
    (lo := (58138607 / 125000000)) (hi := (465108857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1019 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1019 / 640) = 1/(640 / 1019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (58138607 / 125000000) (465108857 / 1000000000) (Real.log (1019 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1019 / 640) = -Real.log (640 / 1019) := by
    rw [show ((1019 / 640) : ℝ) = ((640 / 1019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (112118471 / 125000000) ≤ -Real.log (261 / 640) ∧
    -Real.log (261 / 640) ≤ (89694777 / 100000000) := by
  have h := checkLog_sound (w := (59 / 581)) (n := 12)
    (lo := (50950147 / 250000000)) (hi := (203800589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 261) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 261) = 1/(261 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-89694777 / 100000000) (-112118471 / 125000000) (Real.log (261 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (177424739 / 500000000) ≤ -Real.log (500000 / 712983) ∧
    -Real.log (500000 / 712983) ≤ (354849479 / 1000000000) := by
  have h := checkLog_sound (w := (212983 / 1212983)) (n := 12)
    (lo := (177424739 / 500000000)) (hi := (354849479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712983 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712983 / 500000) = 1/(500000 / 712983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (177424739 / 500000000) (354849479 / 1000000000) (Real.log (712983 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (712983 / 500000) = -Real.log (500000 / 712983) := by
    rw [show ((712983 / 500000) : ℝ) = ((500000 / 712983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (11101333 / 20000000) ≤ -Real.log (287017 / 500000) ∧
    -Real.log (287017 / 500000) ≤ (555066651 / 1000000000) := by
  have h := checkLog_sound (w := (212983 / 787017)) (n := 12)
    (lo := (11101333 / 20000000)) (hi := (555066651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 287017) = 1/(287017 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-555066651 / 1000000000) (-11101333 / 20000000) (Real.log (287017 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (355465713 / 1000000000) ≤ -Real.log (200000 / 285369) ∧
    -Real.log (200000 / 285369) ≤ (177732857 / 500000000) := by
  have h := checkLog_sound (w := (85369 / 485369)) (n := 12)
    (lo := (355465713 / 1000000000)) (hi := (177732857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285369 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285369 / 200000) = 1/(200000 / 285369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (355465713 / 1000000000) (177732857 / 500000000) (Real.log (285369 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (285369 / 200000) = -Real.log (200000 / 285369) := by
    rw [show ((285369 / 200000) : ℝ) = ((200000 / 285369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (139149773 / 250000000) ≤ -Real.log (114631 / 200000) ∧
    -Real.log (114631 / 200000) ≤ (556599093 / 1000000000) := by
  have h := checkLog_sound (w := (85369 / 314631)) (n := 12)
    (lo := (139149773 / 250000000)) (hi := (556599093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 114631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 114631) = 1/(114631 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-556599093 / 1000000000) (-139149773 / 250000000) (Real.log (114631 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68858467 / 250000000) ≤ -Real.log (500000 / 658551) ∧
    -Real.log (500000 / 658551) ≤ (275433869 / 1000000000) := by
  have h := checkLog_sound (w := (158551 / 1158551)) (n := 12)
    (lo := (68858467 / 250000000)) (hi := (275433869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658551 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658551 / 500000) = 1/(500000 / 658551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68858467 / 250000000) (275433869 / 1000000000) (Real.log (658551 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (658551 / 500000) = -Real.log (500000 / 658551) := by
    rw [show ((658551 / 500000) : ℝ) = ((500000 / 658551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (381409771 / 1000000000) ≤ -Real.log (341449 / 500000) ∧
    -Real.log (341449 / 500000) ≤ (95352443 / 250000000) := by
  have h := checkLog_sound (w := (158551 / 841449)) (n := 12)
    (lo := (381409771 / 1000000000)) (hi := (95352443 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 341449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 341449) = 1/(341449 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-95352443 / 250000000) (-381409771 / 1000000000) (Real.log (341449 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (5519653 / 20000000) ≤ -Real.log (40000 / 52713) ∧
    -Real.log (40000 / 52713) ≤ (275982651 / 1000000000) := by
  have h := checkLog_sound (w := (12713 / 92713)) (n := 12)
    (lo := (5519653 / 20000000)) (hi := (275982651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52713 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52713 / 40000) = 1/(40000 / 52713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5519653 / 20000000) (275982651 / 1000000000) (Real.log (52713 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (52713 / 40000) = -Real.log (40000 / 52713) := by
    rw [show ((52713 / 40000) : ℝ) = ((40000 / 52713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76493811 / 200000000) ≤ -Real.log (27287 / 40000) ∧
    -Real.log (27287 / 40000) ≤ (5976079 / 15625000) := by
  have h := checkLog_sound (w := (12713 / 67287)) (n := 12)
    (lo := (76493811 / 200000000)) (hi := (5976079 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 27287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 27287) = 1/(27287 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-5976079 / 15625000) (-76493811 / 200000000) (Real.log (27287 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (909916129 / 1000000000) ≤ -Real.log (250000000000 / 621028545347) ∧
    -Real.log (250000000000 / 621028545347) ≤ (909916131 / 1000000000) := by
  have h := checkLog_sound (w := (121028545347 / 1121028545347)) (n := 12)
    (lo := (216768949 / 1000000000)) (hi := (4335379 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621028545347 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(621028545347 / 500000000000) = 1/(250000000000 / 621028545347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (909916129 / 1000000000) (909916131 / 1000000000) (Real.log (621028545347 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (621028545347 / 250000000000) = -Real.log (250000000000 / 621028545347) := by
    rw [show ((621028545347 / 250000000000) : ℝ) = ((250000000000 / 621028545347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (182412961 / 200000000) ≤ -Real.log (5000000000 / 12447287383) ∧
    -Real.log (5000000000 / 12447287383) ≤ (912064807 / 1000000000) := by
  have h := checkLog_sound (w := (2447287383 / 22447287383)) (n := 12)
    (lo := (1751341 / 8000000)) (hi := (109458813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12447287383 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12447287383 / 10000000000) = 1/(5000000000 / 12447287383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (182412961 / 200000000) (912064807 / 1000000000) (Real.log (12447287383 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12447287383 / 5000000000) = -Real.log (5000000000 / 12447287383) := by
    rw [show ((12447287383 / 5000000000) : ℝ) = ((5000000000 / 12447287383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16421091 / 25000000) ≤ -Real.log (50000000000 / 96434753067) ∧
    -Real.log (50000000000 / 96434753067) ≤ (656843641 / 1000000000) := by
  have h := checkLog_sound (w := (46434753067 / 146434753067)) (n := 12)
    (lo := (16421091 / 25000000)) (hi := (656843641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96434753067 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96434753067 / 50000000000) = 1/(50000000000 / 96434753067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16421091 / 25000000) (656843641 / 1000000000) (Real.log (96434753067 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (96434753067 / 50000000000) = -Real.log (50000000000 / 96434753067) := by
    rw [show ((96434753067 / 50000000000) : ℝ) = ((50000000000 / 96434753067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (329225853 / 500000000) ≤ -Real.log (500000000000 / 965899512589) ∧
    -Real.log (500000000000 / 965899512589) ≤ (658451707 / 1000000000) := by
  have h := checkLog_sound (w := (465899512589 / 1465899512589)) (n := 12)
    (lo := (329225853 / 500000000)) (hi := (658451707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((965899512589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(965899512589 / 500000000000) = 1/(500000000000 / 965899512589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (329225853 / 500000000) (658451707 / 1000000000) (Real.log (965899512589 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (965899512589 / 500000000000) = -Real.log (500000000000 / 965899512589) := by
    rw [show ((965899512589 / 500000000000) : ℝ) = ((500000000000 / 965899512589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0213

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0214Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0214
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

theorem reflection_log_1_neg : (259354933 / 1000000000) ≤ -Real.log (1280 / 1659) ∧
    -Real.log (1280 / 1659) ≤ (129677467 / 500000000) := by
  have h := checkLog_sound (w := (379 / 2939)) (n := 12)
    (lo := (259354933 / 1000000000)) (hi := (129677467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1659 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1659 / 1280) = 1/(1280 / 1659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (259354933 / 1000000000) (129677467 / 500000000) (Real.log (1659 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1659 / 1280) = -Real.log (1280 / 1659) := by
    rw [show ((1659 / 1280) : ℝ) = ((1280 / 1659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (351110099 / 1000000000) ≤ -Real.log (901 / 1280) ∧
    -Real.log (901 / 1280) ≤ (3511101 / 10000000) := by
  have h := checkLog_sound (w := (379 / 2181)) (n := 12)
    (lo := (351110099 / 1000000000)) (hi := (3511101 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 901) = 1/(901 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3511101 / 10000000) (-351110099 / 1000000000) (Real.log (901 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (258902751 / 1000000000) ≤ -Real.log (5120 / 6633) ∧
    -Real.log (5120 / 6633) ≤ (8090711 / 31250000) := by
  have h := checkLog_sound (w := (1513 / 11753)) (n := 12)
    (lo := (258902751 / 1000000000)) (hi := (8090711 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6633 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6633 / 5120) = 1/(5120 / 6633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (258902751 / 1000000000) (8090711 / 31250000) (Real.log (6633 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6633 / 5120) = -Real.log (5120 / 6633) := by
    rw [show ((6633 / 5120) : ℝ) = ((5120 / 6633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (350278037 / 1000000000) ≤ -Real.log (3607 / 5120) ∧
    -Real.log (3607 / 5120) ≤ (175139019 / 500000000) := by
  have h := checkLog_sound (w := (1513 / 8727)) (n := 12)
    (lo := (350278037 / 1000000000)) (hi := (175139019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3607) = 1/(3607 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-175139019 / 500000000) (-350278037 / 1000000000) (Real.log (3607 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (58138607 / 125000000) ≤ -Real.log (640 / 1019) ∧
    -Real.log (640 / 1019) ≤ (465108857 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1659)) (n := 12)
    (lo := (58138607 / 125000000)) (hi := (465108857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1019 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1019 / 640) = 1/(640 / 1019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (58138607 / 125000000) (465108857 / 1000000000) (Real.log (1019 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1019 / 640) = -Real.log (640 / 1019) := by
    rw [show ((1019 / 640) : ℝ) = ((640 / 1019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (112118471 / 125000000) ≤ -Real.log (261 / 640) ∧
    -Real.log (261 / 640) ≤ (89694777 / 100000000) := by
  have h := checkLog_sound (w := (59 / 581)) (n := 12)
    (lo := (50950147 / 250000000)) (hi := (203800589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 261) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 261) = 1/(261 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-89694777 / 100000000) (-112118471 / 125000000) (Real.log (261 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46437257 / 100000000) ≤ -Real.log (2560 / 4073) ∧
    -Real.log (2560 / 4073) ≤ (464372571 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 6633)) (n := 12)
    (lo := (46437257 / 100000000)) (hi := (464372571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4073 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4073 / 2560) = 1/(2560 / 4073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46437257 / 100000000) (464372571 / 1000000000) (Real.log (4073 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4073 / 2560) = -Real.log (2560 / 4073) := by
    rw [show ((4073 / 2560) : ℝ) = ((2560 / 4073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (447039163 / 500000000) ≤ -Real.log (1047 / 2560) ∧
    -Real.log (1047 / 2560) ≤ (111759791 / 125000000) := by
  have h := checkLog_sound (w := (233 / 2327)) (n := 12)
    (lo := (100465573 / 500000000)) (hi := (200931147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1047) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1047) = 1/(1047 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-111759791 / 125000000) (-447039163 / 500000000) (Real.log (1047 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (354234267 / 1000000000) ≤ -Real.log (1000000 / 1425089) ∧
    -Real.log (1000000 / 1425089) ≤ (88558567 / 250000000) := by
  have h := checkLog_sound (w := (425089 / 2425089)) (n := 12)
    (lo := (354234267 / 1000000000)) (hi := (88558567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1425089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1425089 / 1000000) = 1/(1000000 / 1425089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (354234267 / 1000000000) (88558567 / 250000000) (Real.log (1425089 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1425089 / 1000000) = -Real.log (1000000 / 1425089) := by
    rw [show ((1425089 / 1000000) : ℝ) = ((1000000 / 1425089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8649063 / 15625000) ≤ -Real.log (574911 / 1000000) ∧
    -Real.log (574911 / 1000000) ≤ (553540033 / 1000000000) := by
  have h := checkLog_sound (w := (425089 / 1574911)) (n := 12)
    (lo := (8649063 / 15625000)) (hi := (553540033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 574911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 574911) = 1/(574911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-553540033 / 1000000000) (-8649063 / 15625000) (Real.log (574911 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17742509 / 50000000) ≤ -Real.log (1000000 / 1425967) ∧
    -Real.log (1000000 / 1425967) ≤ (354850181 / 1000000000) := by
  have h := checkLog_sound (w := (425967 / 2425967)) (n := 12)
    (lo := (17742509 / 50000000)) (hi := (354850181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1425967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1425967 / 1000000) = 1/(1000000 / 1425967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17742509 / 50000000) (354850181 / 1000000000) (Real.log (1425967 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1425967 / 1000000) = -Real.log (1000000 / 1425967) := by
    rw [show ((1425967 / 1000000) : ℝ) = ((1000000 / 1425967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (555068393 / 1000000000) ≤ -Real.log (574033 / 1000000) ∧
    -Real.log (574033 / 1000000) ≤ (277534197 / 500000000) := by
  have h := checkLog_sound (w := (425967 / 1574033)) (n := 12)
    (lo := (555068393 / 1000000000)) (hi := (277534197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 574033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 574033) = 1/(574033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-277534197 / 500000000) (-555068393 / 1000000000) (Real.log (574033 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8590197 / 31250000) ≤ -Real.log (1000000 / 1316381) ∧
    -Real.log (1000000 / 1316381) ≤ (54977261 / 200000000) := by
  have h := checkLog_sound (w := (316381 / 2316381)) (n := 12)
    (lo := (8590197 / 31250000)) (hi := (54977261 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1316381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1316381 / 1000000) = 1/(1000000 / 1316381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8590197 / 31250000) (54977261 / 200000000) (Real.log (1316381 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1316381 / 1000000) = -Real.log (1000000 / 1316381) := by
    rw [show ((1316381 / 1000000) : ℝ) = ((1000000 / 1316381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (190177267 / 500000000) ≤ -Real.log (683619 / 1000000) ∧
    -Real.log (683619 / 1000000) ≤ (76070907 / 200000000) := by
  have h := checkLog_sound (w := (316381 / 1683619)) (n := 12)
    (lo := (190177267 / 500000000)) (hi := (76070907 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 683619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 683619) = 1/(683619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-76070907 / 200000000) (-190177267 / 500000000) (Real.log (683619 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (275434627 / 1000000000) ≤ -Real.log (1000000 / 1317103) ∧
    -Real.log (1000000 / 1317103) ≤ (68858657 / 250000000) := by
  have h := checkLog_sound (w := (317103 / 2317103)) (n := 12)
    (lo := (275434627 / 1000000000)) (hi := (68858657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317103 / 1000000) = 1/(1000000 / 1317103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (275434627 / 1000000000) (68858657 / 250000000) (Real.log (1317103 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1317103 / 1000000) = -Real.log (1000000 / 1317103) := by
    rw [show ((1317103 / 1000000) : ℝ) = ((1000000 / 1317103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (95352809 / 250000000) ≤ -Real.log (682897 / 1000000) ∧
    -Real.log (682897 / 1000000) ≤ (381411237 / 1000000000) := by
  have h := checkLog_sound (w := (317103 / 1682897)) (n := 12)
    (lo := (95352809 / 250000000)) (hi := (381411237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 682897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 682897) = 1/(682897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-381411237 / 1000000000) (-95352809 / 250000000) (Real.log (682897 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (9077743 / 10000000) ≤ -Real.log (1250000000 / 3098499159) ∧
    -Real.log (1250000000 / 3098499159) ≤ (453887151 / 500000000) := by
  have h := checkLog_sound (w := (598499159 / 5598499159)) (n := 12)
    (lo := (2682839 / 12500000)) (hi := (214627121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3098499159 / 2500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3098499159 / 2500000000) = 1/(1250000000 / 3098499159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9077743 / 10000000) (453887151 / 500000000) (Real.log (3098499159 / 1250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3098499159 / 1250000000) = -Real.log (1250000000 / 3098499159) := by
    rw [show ((3098499159 / 1250000000) : ℝ) = ((1250000000 / 3098499159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (227479643 / 250000000) ≤ -Real.log (62500000000 / 155257515683) ∧
    -Real.log (62500000000 / 155257515683) ≤ (454959287 / 500000000) := by
  have h := checkLog_sound (w := (30257515683 / 280257515683)) (n := 12)
    (lo := (3387053 / 15625000)) (hi := (216771393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155257515683 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(155257515683 / 125000000000) = 1/(62500000000 / 155257515683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (227479643 / 250000000) (454959287 / 500000000) (Real.log (155257515683 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (155257515683 / 62500000000) = -Real.log (62500000000 / 155257515683) := by
    rw [show ((155257515683 / 62500000000) : ℝ) = ((62500000000 / 155257515683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (327620419 / 500000000) ≤ -Real.log (500000000000 / 962803111089) ∧
    -Real.log (500000000000 / 962803111089) ≤ (655240839 / 1000000000) := by
  have h := checkLog_sound (w := (462803111089 / 1462803111089)) (n := 12)
    (lo := (327620419 / 500000000)) (hi := (655240839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((962803111089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(962803111089 / 500000000000) = 1/(500000000000 / 962803111089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (327620419 / 500000000) (655240839 / 1000000000) (Real.log (962803111089 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (962803111089 / 500000000000) = -Real.log (500000000000 / 962803111089) := by
    rw [show ((962803111089 / 500000000000) : ℝ) = ((500000000000 / 962803111089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (656845863 / 1000000000) ≤ -Real.log (125000000000 / 241087418747) ∧
    -Real.log (125000000000 / 241087418747) ≤ (82105733 / 125000000) := by
  have h := checkLog_sound (w := (116087418747 / 366087418747)) (n := 12)
    (lo := (656845863 / 1000000000)) (hi := (82105733 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241087418747 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241087418747 / 125000000000) = 1/(125000000000 / 241087418747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (656845863 / 1000000000) (82105733 / 125000000) (Real.log (241087418747 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (241087418747 / 125000000000) = -Real.log (125000000000 / 241087418747) := by
    rw [show ((241087418747 / 125000000000) : ℝ) = ((125000000000 / 241087418747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0214

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0215Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0215
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

theorem reflection_log_1_neg : (258902751 / 1000000000) ≤ -Real.log (5120 / 6633) ∧
    -Real.log (5120 / 6633) ≤ (8090711 / 31250000) := by
  have h := checkLog_sound (w := (1513 / 11753)) (n := 12)
    (lo := (258902751 / 1000000000)) (hi := (8090711 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6633 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6633 / 5120) = 1/(5120 / 6633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (258902751 / 1000000000) (8090711 / 31250000) (Real.log (6633 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6633 / 5120) = -Real.log (5120 / 6633) := by
    rw [show ((6633 / 5120) : ℝ) = ((5120 / 6633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (350278037 / 1000000000) ≤ -Real.log (3607 / 5120) ∧
    -Real.log (3607 / 5120) ≤ (175139019 / 500000000) := by
  have h := checkLog_sound (w := (1513 / 8727)) (n := 12)
    (lo := (350278037 / 1000000000)) (hi := (175139019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3607) = 1/(3607 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-175139019 / 500000000) (-350278037 / 1000000000) (Real.log (3607 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (51690073 / 200000000) ≤ -Real.log (512 / 663) ∧
    -Real.log (512 / 663) ≤ (129225183 / 500000000) := by
  have h := checkLog_sound (w := (151 / 1175)) (n := 12)
    (lo := (51690073 / 200000000)) (hi := (129225183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663 / 512) = 1/(512 / 663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (51690073 / 200000000) (129225183 / 500000000) (Real.log (663 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (663 / 512) = -Real.log (512 / 663) := by
    rw [show ((663 / 512) : ℝ) = ((512 / 663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (174723333 / 500000000) ≤ -Real.log (361 / 512) ∧
    -Real.log (361 / 512) ≤ (349446667 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 873)) (n := 12)
    (lo := (174723333 / 500000000)) (hi := (349446667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 361) = 1/(361 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-349446667 / 1000000000) (-174723333 / 500000000) (Real.log (361 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (46437257 / 100000000) ≤ -Real.log (2560 / 4073) ∧
    -Real.log (2560 / 4073) ≤ (464372571 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 6633)) (n := 12)
    (lo := (46437257 / 100000000)) (hi := (464372571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4073 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4073 / 2560) = 1/(2560 / 4073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (46437257 / 100000000) (464372571 / 1000000000) (Real.log (4073 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4073 / 2560) = -Real.log (2560 / 4073) := by
    rw [show ((4073 / 2560) : ℝ) = ((2560 / 4073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (447039163 / 500000000) ≤ -Real.log (1047 / 2560) ∧
    -Real.log (1047 / 2560) ≤ (111759791 / 125000000) := by
  have h := checkLog_sound (w := (233 / 2327)) (n := 12)
    (lo := (100465573 / 500000000)) (hi := (200931147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1047) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1047) = 1/(1047 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-111759791 / 125000000) (-447039163 / 500000000) (Real.log (1047 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23181787 / 50000000) ≤ -Real.log (256 / 407) ∧
    -Real.log (256 / 407) ≤ (463635741 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 663)) (n := 12)
    (lo := (23181787 / 50000000)) (hi := (463635741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407 / 256) = 1/(256 / 407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23181787 / 50000000) (463635741 / 1000000000) (Real.log (407 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (407 / 256) = -Real.log (256 / 407) := by
    rw [show ((407 / 256) : ℝ) = ((256 / 407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (891217093 / 1000000000) ≤ -Real.log (105 / 256) ∧
    -Real.log (105 / 256) ≤ (178243419 / 200000000) := by
  have h := checkLog_sound (w := (23 / 233)) (n := 12)
    (lo := (198069913 / 1000000000)) (hi := (99034957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 105) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 105) = 1/(105 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-178243419 / 200000000) (-891217093 / 1000000000) (Real.log (105 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17680969 / 50000000) ≤ -Real.log (1000000 / 1424213) ∧
    -Real.log (1000000 / 1424213) ≤ (353619381 / 1000000000) := by
  have h := checkLog_sound (w := (424213 / 2424213)) (n := 12)
    (lo := (17680969 / 50000000)) (hi := (353619381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1424213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1424213 / 1000000) = 1/(1000000 / 1424213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17680969 / 50000000) (353619381 / 1000000000) (Real.log (1424213 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1424213 / 1000000) = -Real.log (1000000 / 1424213) := by
    rw [show ((1424213 / 1000000) : ℝ) = ((1000000 / 1424213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (276008739 / 500000000) ≤ -Real.log (575787 / 1000000) ∧
    -Real.log (575787 / 1000000) ≤ (552017479 / 1000000000) := by
  have h := checkLog_sound (w := (424213 / 1575787)) (n := 12)
    (lo := (276008739 / 500000000)) (hi := (552017479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 575787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 575787) = 1/(575787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-552017479 / 1000000000) (-276008739 / 500000000) (Real.log (575787 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (354234969 / 1000000000) ≤ -Real.log (100000 / 142509) ∧
    -Real.log (100000 / 142509) ≤ (35423497 / 100000000) := by
  have h := checkLog_sound (w := (42509 / 242509)) (n := 12)
    (lo := (354234969 / 1000000000)) (hi := (35423497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142509 / 100000) = 1/(100000 / 142509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (354234969 / 1000000000) (35423497 / 100000000) (Real.log (142509 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (142509 / 100000) = -Real.log (100000 / 142509) := by
    rw [show ((142509 / 100000) : ℝ) = ((100000 / 142509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (138385443 / 250000000) ≤ -Real.log (57491 / 100000) ∧
    -Real.log (57491 / 100000) ≤ (553541773 / 1000000000) := by
  have h := checkLog_sound (w := (42509 / 157491)) (n := 12)
    (lo := (138385443 / 250000000)) (hi := (553541773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 57491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 57491) = 1/(57491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-553541773 / 1000000000) (-138385443 / 250000000) (Real.log (57491 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6858461 / 25000000) ≤ -Real.log (50000 / 65783) ∧
    -Real.log (50000 / 65783) ≤ (274338441 / 1000000000) := by
  have h := checkLog_sound (w := (15783 / 115783)) (n := 12)
    (lo := (6858461 / 25000000)) (hi := (274338441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65783 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65783 / 50000) = 1/(50000 / 65783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6858461 / 25000000) (274338441 / 1000000000) (Real.log (65783 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (65783 / 50000) = -Real.log (50000 / 65783) := by
    rw [show ((65783 / 50000) : ℝ) = ((50000 / 65783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (47412551 / 125000000) ≤ -Real.log (34217 / 50000) ∧
    -Real.log (34217 / 50000) ≤ (379300409 / 1000000000) := by
  have h := checkLog_sound (w := (15783 / 84217)) (n := 12)
    (lo := (47412551 / 125000000)) (hi := (379300409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 34217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 34217) = 1/(34217 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-379300409 / 1000000000) (-47412551 / 125000000) (Real.log (34217 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (34360883 / 125000000) ≤ -Real.log (500000 / 658191) ∧
    -Real.log (500000 / 658191) ≤ (54977413 / 200000000) := by
  have h := checkLog_sound (w := (158191 / 1158191)) (n := 12)
    (lo := (34360883 / 125000000)) (hi := (54977413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658191 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658191 / 500000) = 1/(500000 / 658191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (34360883 / 125000000) (54977413 / 200000000) (Real.log (658191 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (658191 / 500000) = -Real.log (500000 / 658191) := by
    rw [show ((658191 / 500000) : ℝ) = ((500000 / 658191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (95088999 / 250000000) ≤ -Real.log (341809 / 500000) ∧
    -Real.log (341809 / 500000) ≤ (380355997 / 1000000000) := by
  have h := checkLog_sound (w := (158191 / 841809)) (n := 12)
    (lo := (95088999 / 250000000)) (hi := (380355997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 341809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 341809) = 1/(341809 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-380355997 / 1000000000) (-95088999 / 250000000) (Real.log (341809 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (452818429 / 500000000) ≤ -Real.log (250000000000 / 618376674013) ∧
    -Real.log (250000000000 / 618376674013) ≤ (45281843 / 50000000) := by
  have h := checkLog_sound (w := (118376674013 / 1118376674013)) (n := 12)
    (lo := (106244839 / 500000000)) (hi := (212489679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618376674013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(618376674013 / 500000000000) = 1/(250000000000 / 618376674013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (452818429 / 500000000) (45281843 / 50000000) (Real.log (618376674013 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (618376674013 / 250000000000) = -Real.log (250000000000 / 618376674013) := by
    rw [show ((618376674013 / 250000000000) : ℝ) = ((250000000000 / 618376674013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (907776741 / 1000000000) ≤ -Real.log (500000000000 / 1239402689117) ∧
    -Real.log (500000000000 / 1239402689117) ≤ (907776743 / 1000000000) := by
  have h := checkLog_sound (w := (239402689117 / 2239402689117)) (n := 12)
    (lo := (214629561 / 1000000000)) (hi := (107314781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239402689117 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1239402689117 / 1000000000000) = 1/(500000000000 / 1239402689117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (907776741 / 1000000000) (907776743 / 1000000000) (Real.log (1239402689117 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1239402689117 / 500000000000) = -Real.log (500000000000 / 1239402689117) := by
    rw [show ((1239402689117 / 500000000000) : ℝ) = ((500000000000 / 1239402689117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (653638849 / 1000000000) ≤ -Real.log (62500000000 / 120157743227) ∧
    -Real.log (62500000000 / 120157743227) ≤ (13072777 / 20000000) := by
  have h := checkLog_sound (w := (57657743227 / 182657743227)) (n := 12)
    (lo := (653638849 / 1000000000)) (hi := (13072777 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120157743227 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120157743227 / 62500000000) = 1/(62500000000 / 120157743227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (653638849 / 1000000000) (13072777 / 20000000) (Real.log (120157743227 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (120157743227 / 62500000000) = -Real.log (62500000000 / 120157743227) := by
    rw [show ((120157743227 / 62500000000) : ℝ) = ((62500000000 / 120157743227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (655243061 / 1000000000) ≤ -Real.log (250000000000 / 481402625443) ∧
    -Real.log (250000000000 / 481402625443) ≤ (327621531 / 500000000) := by
  have h := checkLog_sound (w := (231402625443 / 731402625443)) (n := 12)
    (lo := (655243061 / 1000000000)) (hi := (327621531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481402625443 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481402625443 / 250000000000) = 1/(250000000000 / 481402625443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (655243061 / 1000000000) (327621531 / 500000000) (Real.log (481402625443 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (481402625443 / 250000000000) = -Real.log (250000000000 / 481402625443) := by
    rw [show ((481402625443 / 250000000000) : ℝ) = ((250000000000 / 481402625443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0215

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0216Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0216
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

theorem reflection_log_1_neg : (51690073 / 200000000) ≤ -Real.log (512 / 663) ∧
    -Real.log (512 / 663) ≤ (129225183 / 500000000) := by
  have h := checkLog_sound (w := (151 / 1175)) (n := 12)
    (lo := (51690073 / 200000000)) (hi := (129225183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663 / 512) = 1/(512 / 663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (51690073 / 200000000) (129225183 / 500000000) (Real.log (663 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (663 / 512) = -Real.log (512 / 663) := by
    rw [show ((663 / 512) : ℝ) = ((512 / 663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (174723333 / 500000000) ≤ -Real.log (361 / 512) ∧
    -Real.log (361 / 512) ≤ (349446667 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 873)) (n := 12)
    (lo := (174723333 / 500000000)) (hi := (349446667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 361) = 1/(361 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-349446667 / 1000000000) (-174723333 / 500000000) (Real.log (361 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128998887 / 500000000) ≤ -Real.log (5120 / 6627) ∧
    -Real.log (5120 / 6627) ≤ (10319911 / 40000000) := by
  have h := checkLog_sound (w := (1507 / 11747)) (n := 12)
    (lo := (128998887 / 500000000)) (hi := (10319911 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6627 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6627 / 5120) = 1/(5120 / 6627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128998887 / 500000000) (10319911 / 40000000) (Real.log (6627 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6627 / 5120) = -Real.log (5120 / 6627) := by
    rw [show ((6627 / 5120) : ℝ) = ((5120 / 6627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (174307993 / 500000000) ≤ -Real.log (3613 / 5120) ∧
    -Real.log (3613 / 5120) ≤ (348615987 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 8733)) (n := 12)
    (lo := (174307993 / 500000000)) (hi := (348615987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3613) = 1/(3613 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-348615987 / 1000000000) (-174307993 / 500000000) (Real.log (3613 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23181787 / 50000000) ≤ -Real.log (256 / 407) ∧
    -Real.log (256 / 407) ≤ (463635741 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 663)) (n := 12)
    (lo := (23181787 / 50000000)) (hi := (463635741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407 / 256) = 1/(256 / 407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23181787 / 50000000) (463635741 / 1000000000) (Real.log (407 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (407 / 256) = -Real.log (256 / 407) := by
    rw [show ((407 / 256) : ℝ) = ((256 / 407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (891217093 / 1000000000) ≤ -Real.log (105 / 256) ∧
    -Real.log (105 / 256) ≤ (178243419 / 200000000) := by
  have h := checkLog_sound (w := (23 / 233)) (n := 12)
    (lo := (198069913 / 1000000000)) (hi := (99034957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 105) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 105) = 1/(105 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-178243419 / 200000000) (-891217093 / 1000000000) (Real.log (105 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7232787 / 15625000) ≤ -Real.log (2560 / 4067) ∧
    -Real.log (2560 / 4067) ≤ (462898369 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 6627)) (n := 12)
    (lo := (7232787 / 15625000)) (hi := (462898369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4067 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4067 / 2560) = 1/(2560 / 4067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7232787 / 15625000) (462898369 / 1000000000) (Real.log (4067 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4067 / 2560) = -Real.log (2560 / 4067) := by
    rw [show ((4067 / 2560) : ℝ) = ((2560 / 4067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (111045503 / 125000000) ≤ -Real.log (1053 / 2560) ∧
    -Real.log (1053 / 2560) ≤ (444182013 / 500000000) := by
  have h := checkLog_sound (w := (227 / 2333)) (n := 12)
    (lo := (48804211 / 250000000)) (hi := (39043369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1053) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1053) = 1/(1053 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-444182013 / 500000000) (-111045503 / 125000000) (Real.log (1053 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (88250853 / 250000000) ≤ -Real.log (125000 / 177917) ∧
    -Real.log (125000 / 177917) ≤ (353003413 / 1000000000) := by
  have h := checkLog_sound (w := (52917 / 302917)) (n := 12)
    (lo := (88250853 / 250000000)) (hi := (353003413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177917 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177917 / 125000) = 1/(125000 / 177917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (88250853 / 250000000) (353003413 / 1000000000) (Real.log (177917 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (177917 / 125000) = -Real.log (125000 / 177917) := by
    rw [show ((177917 / 125000) : ℝ) = ((125000 / 177917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (34405969 / 62500000) ≤ -Real.log (72083 / 125000) ∧
    -Real.log (72083 / 125000) ≤ (110099101 / 200000000) := by
  have h := checkLog_sound (w := (52917 / 197083)) (n := 12)
    (lo := (34405969 / 62500000)) (hi := (110099101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 72083) = 1/(72083 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110099101 / 200000000) (-34405969 / 62500000) (Real.log (72083 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176810041 / 500000000) ≤ -Real.log (500000 / 712107) ∧
    -Real.log (500000 / 712107) ≤ (353620083 / 1000000000) := by
  have h := checkLog_sound (w := (212107 / 1212107)) (n := 12)
    (lo := (176810041 / 500000000)) (hi := (353620083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712107 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712107 / 500000) = 1/(500000 / 712107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176810041 / 500000000) (353620083 / 1000000000) (Real.log (712107 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (712107 / 500000) = -Real.log (500000 / 712107) := by
    rw [show ((712107 / 500000) : ℝ) = ((500000 / 712107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (110403843 / 200000000) ≤ -Real.log (287893 / 500000) ∧
    -Real.log (287893 / 500000) ≤ (34501201 / 62500000) := by
  have h := checkLog_sound (w := (212107 / 787893)) (n := 12)
    (lo := (110403843 / 200000000)) (hi := (34501201 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 287893) = 1/(287893 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-34501201 / 62500000) (-110403843 / 200000000) (Real.log (287893 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (273791037 / 1000000000) ≤ -Real.log (50000 / 65747) ∧
    -Real.log (50000 / 65747) ≤ (136895519 / 500000000) := by
  have h := checkLog_sound (w := (15747 / 115747)) (n := 12)
    (lo := (273791037 / 1000000000)) (hi := (136895519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65747 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65747 / 50000) = 1/(50000 / 65747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (273791037 / 1000000000) (136895519 / 500000000) (Real.log (65747 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (65747 / 50000) = -Real.log (50000 / 65747) := by
    rw [show ((65747 / 50000) : ℝ) = ((50000 / 65747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (378248853 / 1000000000) ≤ -Real.log (34253 / 50000) ∧
    -Real.log (34253 / 50000) ≤ (189124427 / 500000000) := by
  have h := checkLog_sound (w := (15747 / 84253)) (n := 12)
    (lo := (378248853 / 1000000000)) (hi := (189124427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 34253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 34253) = 1/(34253 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-189124427 / 500000000) (-378248853 / 1000000000) (Real.log (34253 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85731 / 312500) ≤ -Real.log (1000000 / 1315661) ∧
    -Real.log (1000000 / 1315661) ≤ (274339201 / 1000000000) := by
  have h := checkLog_sound (w := (315661 / 2315661)) (n := 12)
    (lo := (85731 / 312500)) (hi := (274339201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1315661 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1315661 / 1000000) = 1/(1000000 / 1315661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85731 / 312500) (274339201 / 1000000000) (Real.log (1315661 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1315661 / 1000000) = -Real.log (1000000 / 1315661) := by
    rw [show ((1315661 / 1000000) : ℝ) = ((1000000 / 1315661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37930187 / 100000000) ≤ -Real.log (684339 / 1000000) ∧
    -Real.log (684339 / 1000000) ≤ (379301871 / 1000000000) := by
  have h := checkLog_sound (w := (315661 / 1684339)) (n := 12)
    (lo := (37930187 / 100000000)) (hi := (379301871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 684339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 684339) = 1/(684339 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-379301871 / 1000000000) (-37930187 / 100000000) (Real.log (684339 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (180699783 / 200000000) ≤ -Real.log (250000000000 / 617056032629) ∧
    -Real.log (250000000000 / 617056032629) ≤ (903498917 / 1000000000) := by
  have h := checkLog_sound (w := (117056032629 / 1117056032629)) (n := 12)
    (lo := (42070347 / 200000000)) (hi := (26293967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617056032629 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(617056032629 / 500000000000) = 1/(250000000000 / 617056032629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (180699783 / 200000000) (903498917 / 1000000000) (Real.log (617056032629 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (617056032629 / 250000000000) = -Real.log (250000000000 / 617056032629) := by
    rw [show ((617056032629 / 250000000000) : ℝ) = ((250000000000 / 617056032629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (905639297 / 1000000000) ≤ -Real.log (62500000000 / 154594545543) ∧
    -Real.log (62500000000 / 154594545543) ≤ (905639299 / 1000000000) := by
  have h := checkLog_sound (w := (29594545543 / 279594545543)) (n := 12)
    (lo := (212492117 / 1000000000)) (hi := (106246059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154594545543 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(154594545543 / 125000000000) = 1/(62500000000 / 154594545543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (905639297 / 1000000000) (905639299 / 1000000000) (Real.log (154594545543 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (154594545543 / 62500000000) = -Real.log (62500000000 / 154594545543) := by
    rw [show ((154594545543 / 62500000000) : ℝ) = ((62500000000 / 154594545543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (65203989 / 100000000) ≤ -Real.log (500000000000 / 959726155373) ∧
    -Real.log (500000000000 / 959726155373) ≤ (652039891 / 1000000000) := by
  have h := checkLog_sound (w := (459726155373 / 1459726155373)) (n := 12)
    (lo := (65203989 / 100000000)) (hi := (652039891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959726155373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959726155373 / 500000000000) = 1/(500000000000 / 959726155373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (65203989 / 100000000) (652039891 / 1000000000) (Real.log (959726155373 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (959726155373 / 500000000000) = -Real.log (500000000000 / 959726155373) := by
    rw [show ((959726155373 / 500000000000) : ℝ) = ((500000000000 / 959726155373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (653641071 / 1000000000) ≤ -Real.log (500000000000 / 961264081107) ∧
    -Real.log (500000000000 / 961264081107) ≤ (40852567 / 62500000) := by
  have h := checkLog_sound (w := (461264081107 / 1461264081107)) (n := 12)
    (lo := (653641071 / 1000000000)) (hi := (40852567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961264081107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961264081107 / 500000000000) = 1/(500000000000 / 961264081107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (653641071 / 1000000000) (40852567 / 62500000) (Real.log (961264081107 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (961264081107 / 500000000000) = -Real.log (500000000000 / 961264081107) := by
    rw [show ((961264081107 / 500000000000) : ℝ) = ((500000000000 / 961264081107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0216

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0217Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0217
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

theorem reflection_log_1_neg : (128998887 / 500000000) ≤ -Real.log (5120 / 6627) ∧
    -Real.log (5120 / 6627) ≤ (10319911 / 40000000) := by
  have h := checkLog_sound (w := (1507 / 11747)) (n := 12)
    (lo := (128998887 / 500000000)) (hi := (10319911 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6627 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6627 / 5120) = 1/(5120 / 6627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128998887 / 500000000) (10319911 / 40000000) (Real.log (6627 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6627 / 5120) = -Real.log (5120 / 6627) := by
    rw [show ((6627 / 5120) : ℝ) = ((5120 / 6627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (174307993 / 500000000) ≤ -Real.log (3613 / 5120) ∧
    -Real.log (3613 / 5120) ≤ (348615987 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 8733)) (n := 12)
    (lo := (174307993 / 500000000)) (hi := (348615987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3613) = 1/(3613 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-348615987 / 1000000000) (-174307993 / 500000000) (Real.log (3613 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128772489 / 500000000) ≤ -Real.log (160 / 207) ∧
    -Real.log (160 / 207) ≤ (257544979 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 367)) (n := 12)
    (lo := (128772489 / 500000000)) (hi := (257544979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207 / 160) = 1/(160 / 207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128772489 / 500000000) (257544979 / 1000000000) (Real.log (207 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (207 / 160) = -Real.log (160 / 207) := by
    rw [show ((207 / 160) : ℝ) = ((160 / 207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86946499 / 250000000) ≤ -Real.log (113 / 160) ∧
    -Real.log (113 / 160) ≤ (347785997 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 113) = 1/(113 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-347785997 / 1000000000) (-86946499 / 250000000) (Real.log (113 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7232787 / 15625000) ≤ -Real.log (2560 / 4067) ∧
    -Real.log (2560 / 4067) ≤ (462898369 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 6627)) (n := 12)
    (lo := (7232787 / 15625000)) (hi := (462898369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4067 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4067 / 2560) = 1/(2560 / 4067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7232787 / 15625000) (462898369 / 1000000000) (Real.log (4067 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4067 / 2560) = -Real.log (2560 / 4067) := by
    rw [show ((4067 / 2560) : ℝ) = ((2560 / 4067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (111045503 / 125000000) ≤ -Real.log (1053 / 2560) ∧
    -Real.log (1053 / 2560) ≤ (444182013 / 500000000) := by
  have h := checkLog_sound (w := (227 / 2333)) (n := 12)
    (lo := (48804211 / 250000000)) (hi := (39043369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1053) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1053) = 1/(1053 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-444182013 / 500000000) (-111045503 / 125000000) (Real.log (1053 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (462160451 / 1000000000) ≤ -Real.log (80 / 127) ∧
    -Real.log (80 / 127) ≤ (115540113 / 250000000) := by
  have h := checkLog_sound (w := (47 / 207)) (n := 12)
    (lo := (462160451 / 1000000000)) (hi := (115540113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 80) = 1/(80 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (462160451 / 1000000000) (115540113 / 250000000) (Real.log (127 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (127 / 80) = -Real.log (80 / 127) := by
    rw [show ((127 / 80) : ℝ) = ((80 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (27672471 / 31250000) ≤ -Real.log (33 / 80) ∧
    -Real.log (33 / 80) ≤ (442759537 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 33) = 1/(33 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-442759537 / 500000000) (-27672471 / 31250000) (Real.log (33 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (352387767 / 1000000000) ≤ -Real.log (50000 / 71123) ∧
    -Real.log (50000 / 71123) ≤ (44048471 / 125000000) := by
  have h := checkLog_sound (w := (21123 / 121123)) (n := 12)
    (lo := (352387767 / 1000000000)) (hi := (44048471 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71123 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71123 / 50000) = 1/(50000 / 71123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (352387767 / 1000000000) (44048471 / 125000000) (Real.log (71123 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (71123 / 50000) = -Real.log (50000 / 71123) := by
    rw [show ((71123 / 50000) : ℝ) = ((50000 / 71123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (274488787 / 500000000) ≤ -Real.log (28877 / 50000) ∧
    -Real.log (28877 / 50000) ≤ (21959103 / 40000000) := by
  have h := checkLog_sound (w := (21123 / 78877)) (n := 12)
    (lo := (274488787 / 500000000)) (hi := (21959103 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 28877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 28877) = 1/(28877 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21959103 / 40000000) (-274488787 / 500000000) (Real.log (28877 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176502057 / 500000000) ≤ -Real.log (1000000 / 1423337) ∧
    -Real.log (1000000 / 1423337) ≤ (70600823 / 200000000) := by
  have h := checkLog_sound (w := (423337 / 2423337)) (n := 12)
    (lo := (176502057 / 500000000)) (hi := (70600823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1423337 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1423337 / 1000000) = 1/(1000000 / 1423337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176502057 / 500000000) (70600823 / 200000000) (Real.log (1423337 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1423337 / 1000000) = -Real.log (1000000 / 1423337) := by
    rw [show ((1423337 / 1000000) : ℝ) = ((1000000 / 1423337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (275248619 / 500000000) ≤ -Real.log (576663 / 1000000) ∧
    -Real.log (576663 / 1000000) ≤ (550497239 / 1000000000) := by
  have h := checkLog_sound (w := (423337 / 1576663)) (n := 12)
    (lo := (275248619 / 500000000)) (hi := (550497239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 576663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 576663) = 1/(576663 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-550497239 / 1000000000) (-275248619 / 500000000) (Real.log (576663 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136622047 / 500000000) ≤ -Real.log (1000000 / 1314221) ∧
    -Real.log (1000000 / 1314221) ≤ (54648819 / 200000000) := by
  have h := checkLog_sound (w := (314221 / 2314221)) (n := 12)
    (lo := (136622047 / 500000000)) (hi := (54648819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1314221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1314221 / 1000000) = 1/(1000000 / 1314221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136622047 / 500000000) (54648819 / 200000000) (Real.log (1314221 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1314221 / 1000000) = -Real.log (1000000 / 1314221) := by
    rw [show ((1314221 / 1000000) : ℝ) = ((1000000 / 1314221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (18859993 / 50000000) ≤ -Real.log (685779 / 1000000) ∧
    -Real.log (685779 / 1000000) ≤ (377199861 / 1000000000) := by
  have h := checkLog_sound (w := (314221 / 1685779)) (n := 12)
    (lo := (18859993 / 50000000)) (hi := (377199861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 685779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 685779) = 1/(685779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-377199861 / 1000000000) (-18859993 / 50000000) (Real.log (685779 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (273791797 / 1000000000) ≤ -Real.log (1000000 / 1314941) ∧
    -Real.log (1000000 / 1314941) ≤ (136895899 / 500000000) := by
  have h := checkLog_sound (w := (314941 / 2314941)) (n := 12)
    (lo := (273791797 / 1000000000)) (hi := (136895899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1314941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1314941 / 1000000) = 1/(1000000 / 1314941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (273791797 / 1000000000) (136895899 / 500000000) (Real.log (1314941 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1314941 / 1000000) = -Real.log (1000000 / 1314941) := by
    rw [show ((1314941 / 1000000) : ℝ) = ((1000000 / 1314941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (378250313 / 1000000000) ≤ -Real.log (685059 / 1000000) ∧
    -Real.log (685059 / 1000000) ≤ (189125157 / 500000000) := by
  have h := checkLog_sound (w := (314941 / 1685059)) (n := 12)
    (lo := (378250313 / 1000000000)) (hi := (189125157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 685059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 685059) = 1/(685059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-189125157 / 500000000) (-378250313 / 1000000000) (Real.log (685059 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (901365341 / 1000000000) ≤ -Real.log (250000000000 / 615740901063) ∧
    -Real.log (250000000000 / 615740901063) ≤ (901365343 / 1000000000) := by
  have h := checkLog_sound (w := (115740901063 / 1115740901063)) (n := 12)
    (lo := (208218161 / 1000000000)) (hi := (104109081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615740901063 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(615740901063 / 500000000000) = 1/(250000000000 / 615740901063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (901365341 / 1000000000) (901365343 / 1000000000) (Real.log (615740901063 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (615740901063 / 250000000000) = -Real.log (250000000000 / 615740901063) := by
    rw [show ((615740901063 / 250000000000) : ℝ) = ((250000000000 / 615740901063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (112937669 / 125000000) ≤ -Real.log (62500000000 / 154264384051) ∧
    -Real.log (62500000000 / 154264384051) ≤ (451750677 / 500000000) := by
  have h := checkLog_sound (w := (29264384051 / 279264384051)) (n := 12)
    (lo := (52588543 / 250000000)) (hi := (210354173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154264384051 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(154264384051 / 125000000000) = 1/(62500000000 / 154264384051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (112937669 / 125000000) (451750677 / 500000000) (Real.log (154264384051 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (154264384051 / 62500000000) = -Real.log (62500000000 / 154264384051) := by
    rw [show ((154264384051 / 62500000000) : ℝ) = ((62500000000 / 154264384051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (130088791 / 200000000) ≤ -Real.log (31250000000 / 59887232257) ∧
    -Real.log (31250000000 / 59887232257) ≤ (162610989 / 250000000) := by
  have h := checkLog_sound (w := (28637232257 / 91137232257)) (n := 12)
    (lo := (130088791 / 200000000)) (hi := (162610989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59887232257 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59887232257 / 31250000000) = 1/(31250000000 / 59887232257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (130088791 / 200000000) (162610989 / 250000000) (Real.log (59887232257 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (59887232257 / 31250000000) = -Real.log (31250000000 / 59887232257) := by
    rw [show ((59887232257 / 31250000000) : ℝ) = ((31250000000 / 59887232257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (65204211 / 100000000) ≤ -Real.log (500000000000 / 959728286177) ∧
    -Real.log (500000000000 / 959728286177) ≤ (652042111 / 1000000000) := by
  have h := checkLog_sound (w := (459728286177 / 1459728286177)) (n := 12)
    (lo := (65204211 / 100000000)) (hi := (652042111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959728286177 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959728286177 / 500000000000) = 1/(500000000000 / 959728286177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (65204211 / 100000000) (652042111 / 1000000000) (Real.log (959728286177 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (959728286177 / 500000000000) = -Real.log (500000000000 / 959728286177) := by
    rw [show ((959728286177 / 500000000000) : ℝ) = ((500000000000 / 959728286177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0217

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0218Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0218
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

theorem reflection_log_1_neg : (128772489 / 500000000) ≤ -Real.log (160 / 207) ∧
    -Real.log (160 / 207) ≤ (257544979 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 367)) (n := 12)
    (lo := (128772489 / 500000000)) (hi := (257544979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207 / 160) = 1/(160 / 207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128772489 / 500000000) (257544979 / 1000000000) (Real.log (207 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (207 / 160) = -Real.log (160 / 207) := by
    rw [show ((207 / 160) : ℝ) = ((160 / 207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86946499 / 250000000) ≤ -Real.log (113 / 160) ∧
    -Real.log (113 / 160) ≤ (347785997 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 113) = 1/(113 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-347785997 / 1000000000) (-86946499 / 250000000) (Real.log (113 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (32136497 / 125000000) ≤ -Real.log (5120 / 6621) ∧
    -Real.log (5120 / 6621) ≤ (257091977 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 11741)) (n := 12)
    (lo := (32136497 / 125000000)) (hi := (257091977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6621 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6621 / 5120) = 1/(5120 / 6621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (32136497 / 125000000) (257091977 / 1000000000) (Real.log (6621 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6621 / 5120) = -Real.log (5120 / 6621) := by
    rw [show ((6621 / 5120) : ℝ) = ((5120 / 6621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (173478347 / 500000000) ≤ -Real.log (3619 / 5120) ∧
    -Real.log (3619 / 5120) ≤ (69391339 / 200000000) := by
  have h := checkLog_sound (w := (1501 / 8739)) (n := 12)
    (lo := (173478347 / 500000000)) (hi := (69391339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3619) = 1/(3619 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-69391339 / 200000000) (-173478347 / 500000000) (Real.log (3619 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (462160451 / 1000000000) ≤ -Real.log (80 / 127) ∧
    -Real.log (80 / 127) ≤ (115540113 / 250000000) := by
  have h := checkLog_sound (w := (47 / 207)) (n := 12)
    (lo := (462160451 / 1000000000)) (hi := (115540113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 80) = 1/(80 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (462160451 / 1000000000) (115540113 / 250000000) (Real.log (127 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (127 / 80) = -Real.log (80 / 127) := by
    rw [show ((127 / 80) : ℝ) = ((80 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (27672471 / 31250000) ≤ -Real.log (33 / 80) ∧
    -Real.log (33 / 80) ≤ (442759537 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 33) = 1/(33 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-442759537 / 500000000) (-27672471 / 31250000) (Real.log (33 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46142199 / 100000000) ≤ -Real.log (2560 / 4061) ∧
    -Real.log (2560 / 4061) ≤ (461421991 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 6621)) (n := 12)
    (lo := (46142199 / 100000000)) (hi := (461421991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4061 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4061 / 2560) = 1/(2560 / 4061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46142199 / 100000000) (461421991 / 1000000000) (Real.log (4061 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4061 / 2560) = -Real.log (2560 / 4061) := by
    rw [show ((4061 / 2560) : ℝ) = ((2560 / 4061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (882682191 / 1000000000) ≤ -Real.log (1059 / 2560) ∧
    -Real.log (1059 / 2560) ≤ (882682193 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 2339)) (n := 12)
    (lo := (189535011 / 1000000000)) (hi := (47383753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1059) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1059) = 1/(1059 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-882682193 / 1000000000) (-882682191 / 1000000000) (Real.log (1059 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (175885871 / 500000000) ≤ -Real.log (62500 / 88849) ∧
    -Real.log (62500 / 88849) ≤ (351771743 / 1000000000) := by
  have h := checkLog_sound (w := (26349 / 151349)) (n := 12)
    (lo := (175885871 / 500000000)) (hi := (351771743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88849 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88849 / 62500) = 1/(62500 / 88849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (175885871 / 500000000) (351771743 / 1000000000) (Real.log (88849 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (88849 / 62500) = -Real.log (62500 / 88849) := by
    rw [show ((88849 / 62500) : ℝ) = ((62500 / 88849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (273730973 / 500000000) ≤ -Real.log (36151 / 62500) ∧
    -Real.log (36151 / 62500) ≤ (547461947 / 1000000000) := by
  have h := checkLog_sound (w := (26349 / 98651)) (n := 12)
    (lo := (273730973 / 500000000)) (hi := (547461947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 36151) = 1/(36151 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-547461947 / 1000000000) (-273730973 / 500000000) (Real.log (36151 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35238847 / 100000000) ≤ -Real.log (1000000 / 1422461) ∧
    -Real.log (1000000 / 1422461) ≤ (352388471 / 1000000000) := by
  have h := checkLog_sound (w := (422461 / 2422461)) (n := 12)
    (lo := (35238847 / 100000000)) (hi := (352388471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1422461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1422461 / 1000000) = 1/(1000000 / 1422461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35238847 / 100000000) (352388471 / 1000000000) (Real.log (1422461 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1422461 / 1000000) = -Real.log (1000000 / 1422461) := by
    rw [show ((1422461 / 1000000) : ℝ) = ((1000000 / 1422461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (274489653 / 500000000) ≤ -Real.log (577539 / 1000000) ∧
    -Real.log (577539 / 1000000) ≤ (548979307 / 1000000000) := by
  have h := checkLog_sound (w := (422461 / 1577539)) (n := 12)
    (lo := (274489653 / 500000000)) (hi := (548979307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 577539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 577539) = 1/(577539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-548979307 / 1000000000) (-274489653 / 500000000) (Real.log (577539 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68174213 / 250000000) ≤ -Real.log (500000 / 656751) ∧
    -Real.log (500000 / 656751) ≤ (272696853 / 1000000000) := by
  have h := checkLog_sound (w := (156751 / 1156751)) (n := 12)
    (lo := (68174213 / 250000000)) (hi := (272696853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656751 / 500000) = 1/(500000 / 656751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68174213 / 250000000) (272696853 / 1000000000) (Real.log (656751 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (656751 / 500000) = -Real.log (500000 / 656751) := by
    rw [show ((656751 / 500000) : ℝ) = ((500000 / 656751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (376151967 / 1000000000) ≤ -Real.log (343249 / 500000) ∧
    -Real.log (343249 / 500000) ≤ (11754749 / 31250000) := by
  have h := checkLog_sound (w := (156751 / 843249)) (n := 12)
    (lo := (376151967 / 1000000000)) (hi := (11754749 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 343249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 343249) = 1/(343249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-11754749 / 31250000) (-376151967 / 1000000000) (Real.log (343249 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (54648971 / 200000000) ≤ -Real.log (500000 / 657111) ∧
    -Real.log (500000 / 657111) ≤ (34155607 / 125000000) := by
  have h := checkLog_sound (w := (157111 / 1157111)) (n := 12)
    (lo := (54648971 / 200000000)) (hi := (34155607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657111 / 500000) = 1/(500000 / 657111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54648971 / 200000000) (34155607 / 125000000) (Real.log (657111 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (657111 / 500000) = -Real.log (500000 / 657111) := by
    rw [show ((657111 / 500000) : ℝ) = ((500000 / 657111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (188600659 / 500000000) ≤ -Real.log (342889 / 500000) ∧
    -Real.log (342889 / 500000) ≤ (377201319 / 1000000000) := by
  have h := checkLog_sound (w := (157111 / 842889)) (n := 12)
    (lo := (188600659 / 500000000)) (hi := (377201319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342889) = 1/(342889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-377201319 / 1000000000) (-188600659 / 500000000) (Real.log (342889 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (112404211 / 125000000) ≤ -Real.log (500000000000 / 1228859505961) ∧
    -Real.log (500000000000 / 1228859505961) ≤ (89923369 / 100000000) := by
  have h := checkLog_sound (w := (228859505961 / 2228859505961)) (n := 12)
    (lo := (51521627 / 250000000)) (hi := (206086509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228859505961 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1228859505961 / 1000000000000) = 1/(500000000000 / 1228859505961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (112404211 / 125000000) (89923369 / 100000000) (Real.log (1228859505961 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1228859505961 / 500000000000) = -Real.log (500000000000 / 1228859505961) := by
    rw [show ((1228859505961 / 500000000000) : ℝ) = ((500000000000 / 1228859505961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (36054711 / 40000000) ≤ -Real.log (500000000000 / 1231484800161) ∧
    -Real.log (500000000000 / 1231484800161) ≤ (901367777 / 1000000000) := by
  have h := checkLog_sound (w := (231484800161 / 2231484800161)) (n := 12)
    (lo := (41644119 / 200000000)) (hi := (52055149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231484800161 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1231484800161 / 1000000000000) = 1/(500000000000 / 1231484800161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (36054711 / 40000000) (901367777 / 1000000000) (Real.log (1231484800161 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1231484800161 / 500000000000) = -Real.log (500000000000 / 1231484800161) := by
    rw [show ((1231484800161 / 500000000000) : ℝ) = ((500000000000 / 1231484800161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (648848819 / 1000000000) ≤ -Real.log (250000000000 / 478334241323) ∧
    -Real.log (250000000000 / 478334241323) ≤ (32442441 / 50000000) := by
  have h := checkLog_sound (w := (228334241323 / 728334241323)) (n := 12)
    (lo := (648848819 / 1000000000)) (hi := (32442441 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((478334241323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(478334241323 / 250000000000) = 1/(250000000000 / 478334241323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (648848819 / 1000000000) (32442441 / 50000000) (Real.log (478334241323 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (478334241323 / 250000000000) = -Real.log (250000000000 / 478334241323) := by
    rw [show ((478334241323 / 250000000000) : ℝ) = ((250000000000 / 478334241323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (325223087 / 500000000) ≤ -Real.log (500000000000 / 958197842451) ∧
    -Real.log (500000000000 / 958197842451) ≤ (26017847 / 40000000) := by
  have h := checkLog_sound (w := (458197842451 / 1458197842451)) (n := 12)
    (lo := (325223087 / 500000000)) (hi := (26017847 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((958197842451 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(958197842451 / 500000000000) = 1/(500000000000 / 958197842451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (325223087 / 500000000) (26017847 / 40000000) (Real.log (958197842451 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (958197842451 / 500000000000) = -Real.log (500000000000 / 958197842451) := by
    rw [show ((958197842451 / 500000000000) : ℝ) = ((500000000000 / 958197842451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0218

end


