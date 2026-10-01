-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0371Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0371Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:31:02.806344+00:00
-- url     : https://prove2.me/theorems/f85e9a53-082d-41fd-9154-361c7c0c3516
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0371Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0372Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0371Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0372Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0373Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0374Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0375Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0376Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0371Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0372Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0373Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0374Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0375Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0376Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0371Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0372Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0373Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0374Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0375Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0376Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0371Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0372Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0373Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0374Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0375Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0376Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0371Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0371
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

theorem reflection_log_1_neg : (20715707 / 100000000) ≤ -Real.log (10240 / 12597) ∧
    -Real.log (10240 / 12597) ≤ (207157071 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 22837)) (n := 12)
    (lo := (20715707 / 100000000)) (hi := (207157071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12597 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12597 / 10240) = 1/(10240 / 12597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20715707 / 100000000) (207157071 / 1000000000) (Real.log (12597 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12597 / 10240) = -Real.log (10240 / 12597) := by
    rw [show ((12597 / 10240) : ℝ) = ((10240 / 12597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (261593077 / 1000000000) ≤ -Real.log (7883 / 10240) ∧
    -Real.log (7883 / 10240) ≤ (130796539 / 500000000) := by
  have h := checkLog_sound (w := (2357 / 18123)) (n := 12)
    (lo := (261593077 / 1000000000)) (hi := (130796539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7883) = 1/(7883 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-130796539 / 500000000) (-261593077 / 1000000000) (Real.log (7883 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20691889 / 100000000) ≤ -Real.log (5120 / 6297) ∧
    -Real.log (5120 / 6297) ≤ (206918891 / 1000000000) := by
  have h := checkLog_sound (w := (1177 / 11417)) (n := 12)
    (lo := (20691889 / 100000000)) (hi := (206918891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6297 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6297 / 5120) = 1/(5120 / 6297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20691889 / 100000000) (206918891 / 1000000000) (Real.log (6297 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6297 / 5120) = -Real.log (5120 / 6297) := by
    rw [show ((6297 / 5120) : ℝ) = ((5120 / 6297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (32651573 / 125000000) ≤ -Real.log (3943 / 5120) ∧
    -Real.log (3943 / 5120) ≤ (52242517 / 200000000) := by
  have h := checkLog_sound (w := (1177 / 9063)) (n := 12)
    (lo := (32651573 / 125000000)) (hi := (52242517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3943) = 1/(3943 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-52242517 / 200000000) (-32651573 / 125000000) (Real.log (3943 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (189338601 / 500000000) ≤ -Real.log (5120 / 7477) ∧
    -Real.log (5120 / 7477) ≤ (378677203 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 12597)) (n := 12)
    (lo := (189338601 / 500000000)) (hi := (378677203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7477 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7477 / 5120) = 1/(5120 / 7477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (189338601 / 500000000) (378677203 / 1000000000) (Real.log (7477 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7477 / 5120) = -Real.log (5120 / 7477) := by
    rw [show ((7477 / 5120) : ℝ) = ((5120 / 7477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (616837393 / 1000000000) ≤ -Real.log (2763 / 5120) ∧
    -Real.log (2763 / 5120) ≤ (308418697 / 500000000) := by
  have h := checkLog_sound (w := (2357 / 7883)) (n := 12)
    (lo := (616837393 / 1000000000)) (hi := (308418697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2763) = 1/(2763 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-308418697 / 500000000) (-616837393 / 1000000000) (Real.log (2763 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (94568973 / 250000000) ≤ -Real.log (2560 / 3737) ∧
    -Real.log (2560 / 3737) ≤ (378275893 / 1000000000) := by
  have h := checkLog_sound (w := (1177 / 6297)) (n := 12)
    (lo := (94568973 / 250000000)) (hi := (378275893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3737 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3737 / 2560) = 1/(2560 / 3737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (94568973 / 250000000) (378275893 / 1000000000) (Real.log (3737 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3737 / 2560) = -Real.log (2560 / 3737) := by
    rw [show ((3737 / 2560) : ℝ) = ((2560 / 3737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (123150441 / 200000000) ≤ -Real.log (1383 / 2560) ∧
    -Real.log (1383 / 2560) ≤ (307876103 / 500000000) := by
  have h := checkLog_sound (w := (1177 / 3943)) (n := 12)
    (lo := (123150441 / 200000000)) (hi := (307876103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1383) = 1/(1383 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-307876103 / 500000000) (-123150441 / 200000000) (Real.log (1383 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (141931143 / 500000000) ≤ -Real.log (4000 / 5313) ∧
    -Real.log (4000 / 5313) ≤ (283862287 / 1000000000) := by
  have h := checkLog_sound (w := (1313 / 9313)) (n := 12)
    (lo := (141931143 / 500000000)) (hi := (283862287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5313 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5313 / 4000) = 1/(4000 / 5313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (141931143 / 500000000) (283862287 / 1000000000) (Real.log (5313 / 4000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (5313 / 4000) = -Real.log (4000 / 5313) := by
    rw [show ((5313 / 4000) : ℝ) = ((4000 / 5313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (397869031 / 1000000000) ≤ -Real.log (2687 / 4000) ∧
    -Real.log (2687 / 4000) ≤ (49733629 / 125000000) := by
  have h := checkLog_sound (w := (1313 / 6687)) (n := 12)
    (lo := (397869031 / 1000000000)) (hi := (49733629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 2687) = 1/(2687 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-49733629 / 125000000) (-397869031 / 1000000000) (Real.log (2687 / 4000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (142092231 / 500000000) ≤ -Real.log (500000 / 664339) ∧
    -Real.log (500000 / 664339) ≤ (284184463 / 1000000000) := by
  have h := checkLog_sound (w := (164339 / 1164339)) (n := 12)
    (lo := (142092231 / 500000000)) (hi := (284184463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664339 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664339 / 500000) = 1/(500000 / 664339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (142092231 / 500000000) (284184463 / 1000000000) (Real.log (664339 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (664339 / 500000) = -Real.log (500000 / 664339) := by
    rw [show ((664339 / 500000) : ℝ) = ((500000 / 664339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (49813297 / 125000000) ≤ -Real.log (335661 / 500000) ∧
    -Real.log (335661 / 500000) ≤ (398506377 / 1000000000) := by
  have h := checkLog_sound (w := (164339 / 835661)) (n := 12)
    (lo := (49813297 / 125000000)) (hi := (398506377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 335661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 335661) = 1/(335661 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-398506377 / 1000000000) (-49813297 / 125000000) (Real.log (335661 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (107249951 / 500000000) ≤ -Real.log (500000 / 619621) ∧
    -Real.log (500000 / 619621) ≤ (214499903 / 1000000000) := by
  have h := checkLog_sound (w := (119621 / 1119621)) (n := 12)
    (lo := (107249951 / 500000000)) (hi := (214499903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619621 / 500000) = 1/(500000 / 619621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (107249951 / 500000000) (214499903 / 1000000000) (Real.log (619621 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (619621 / 500000) = -Real.log (500000 / 619621) := by
    rw [show ((619621 / 500000) : ℝ) = ((500000 / 619621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (136719987 / 500000000) ≤ -Real.log (380379 / 500000) ∧
    -Real.log (380379 / 500000) ≤ (10937599 / 40000000) := by
  have h := checkLog_sound (w := (119621 / 880379)) (n := 12)
    (lo := (136719987 / 500000000)) (hi := (10937599 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380379) = 1/(380379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10937599 / 40000000) (-136719987 / 500000000) (Real.log (380379 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53691943 / 250000000) ≤ -Real.log (500000 / 619787) ∧
    -Real.log (500000 / 619787) ≤ (214767773 / 1000000000) := by
  have h := checkLog_sound (w := (119787 / 1119787)) (n := 12)
    (lo := (53691943 / 250000000)) (hi := (214767773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619787 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619787 / 500000) = 1/(500000 / 619787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53691943 / 250000000) (214767773 / 1000000000) (Real.log (619787 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (619787 / 500000) = -Real.log (500000 / 619787) := by
    rw [show ((619787 / 500000) : ℝ) = ((500000 / 619787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (68469119 / 250000000) ≤ -Real.log (380213 / 500000) ∧
    -Real.log (380213 / 500000) ≤ (273876477 / 1000000000) := by
  have h := checkLog_sound (w := (119787 / 880213)) (n := 12)
    (lo := (68469119 / 250000000)) (hi := (273876477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380213) = 1/(380213 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-273876477 / 1000000000) (-68469119 / 250000000) (Real.log (380213 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (681731317 / 1000000000) ≤ -Real.log (250000000000 / 494324525493) ∧
    -Real.log (250000000000 / 494324525493) ≤ (340865659 / 500000000) := by
  have h := checkLog_sound (w := (244324525493 / 744324525493)) (n := 12)
    (lo := (681731317 / 1000000000)) (hi := (340865659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494324525493 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494324525493 / 250000000000) = 1/(250000000000 / 494324525493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (681731317 / 1000000000) (340865659 / 500000000) (Real.log (494324525493 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (494324525493 / 250000000000) = -Real.log (250000000000 / 494324525493) := by
    rw [show ((494324525493 / 250000000000) : ℝ) = ((250000000000 / 494324525493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (682690839 / 1000000000) ≤ -Real.log (100000000000 / 197919627243) ∧
    -Real.log (100000000000 / 197919627243) ≤ (17067271 / 25000000) := by
  have h := checkLog_sound (w := (97919627243 / 297919627243)) (n := 12)
    (lo := (682690839 / 1000000000)) (hi := (17067271 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197919627243 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197919627243 / 100000000000) = 1/(100000000000 / 197919627243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (682690839 / 1000000000) (17067271 / 25000000) (Real.log (197919627243 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (197919627243 / 100000000000) = -Real.log (100000000000 / 197919627243) := by
    rw [show ((197919627243 / 100000000000) : ℝ) = ((100000000000 / 197919627243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (121984969 / 250000000) ≤ -Real.log (500000000000 / 814478454383) ∧
    -Real.log (500000000000 / 814478454383) ≤ (487939877 / 1000000000) := by
  have h := checkLog_sound (w := (314478454383 / 1314478454383)) (n := 12)
    (lo := (121984969 / 250000000)) (hi := (487939877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814478454383 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814478454383 / 500000000000) = 1/(500000000000 / 814478454383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (121984969 / 250000000) (487939877 / 1000000000) (Real.log (814478454383 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (814478454383 / 500000000000) = -Real.log (500000000000 / 814478454383) := by
    rw [show ((814478454383 / 500000000000) : ℝ) = ((500000000000 / 814478454383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (61080531 / 125000000) ≤ -Real.log (100000000000 / 163010470447) ∧
    -Real.log (100000000000 / 163010470447) ≤ (488644249 / 1000000000) := by
  have h := checkLog_sound (w := (63010470447 / 263010470447)) (n := 12)
    (lo := (61080531 / 125000000)) (hi := (488644249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163010470447 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163010470447 / 100000000000) = 1/(100000000000 / 163010470447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (61080531 / 125000000) (488644249 / 1000000000) (Real.log (163010470447 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (163010470447 / 100000000000) = -Real.log (100000000000 / 163010470447) := by
    rw [show ((163010470447 / 100000000000) : ℝ) = ((100000000000 / 163010470447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0371

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0372Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0372
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

theorem reflection_log_1_neg : (20691889 / 100000000) ≤ -Real.log (5120 / 6297) ∧
    -Real.log (5120 / 6297) ≤ (206918891 / 1000000000) := by
  have h := checkLog_sound (w := (1177 / 11417)) (n := 12)
    (lo := (20691889 / 100000000)) (hi := (206918891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6297 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6297 / 5120) = 1/(5120 / 6297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20691889 / 100000000) (206918891 / 1000000000) (Real.log (6297 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6297 / 5120) = -Real.log (5120 / 6297) := by
    rw [show ((6297 / 5120) : ℝ) = ((5120 / 6297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (32651573 / 125000000) ≤ -Real.log (3943 / 5120) ∧
    -Real.log (3943 / 5120) ≤ (52242517 / 200000000) := by
  have h := checkLog_sound (w := (1177 / 9063)) (n := 12)
    (lo := (32651573 / 125000000)) (hi := (52242517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3943) = 1/(3943 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-52242517 / 200000000) (-32651573 / 125000000) (Real.log (3943 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (206680653 / 1000000000) ≤ -Real.log (10240 / 12591) ∧
    -Real.log (10240 / 12591) ≤ (103340327 / 500000000) := by
  have h := checkLog_sound (w := (2351 / 22831)) (n := 12)
    (lo := (206680653 / 1000000000)) (hi := (103340327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12591 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12591 / 10240) = 1/(10240 / 12591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (206680653 / 1000000000) (103340327 / 500000000) (Real.log (12591 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12591 / 10240) = -Real.log (10240 / 12591) := by
    rw [show ((12591 / 10240) : ℝ) = ((10240 / 12591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (52166447 / 200000000) ≤ -Real.log (7889 / 10240) ∧
    -Real.log (7889 / 10240) ≤ (65208059 / 250000000) := by
  have h := checkLog_sound (w := (2351 / 18129)) (n := 12)
    (lo := (52166447 / 200000000)) (hi := (65208059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7889) = 1/(7889 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65208059 / 250000000) (-52166447 / 200000000) (Real.log (7889 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (94568973 / 250000000) ≤ -Real.log (2560 / 3737) ∧
    -Real.log (2560 / 3737) ≤ (378275893 / 1000000000) := by
  have h := checkLog_sound (w := (1177 / 6297)) (n := 12)
    (lo := (94568973 / 250000000)) (hi := (378275893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3737 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3737 / 2560) = 1/(2560 / 3737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (94568973 / 250000000) (378275893 / 1000000000) (Real.log (3737 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3737 / 2560) = -Real.log (2560 / 3737) := by
    rw [show ((3737 / 2560) : ℝ) = ((2560 / 3737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (123150441 / 200000000) ≤ -Real.log (1383 / 2560) ∧
    -Real.log (1383 / 2560) ≤ (307876103 / 500000000) := by
  have h := checkLog_sound (w := (1177 / 3943)) (n := 12)
    (lo := (123150441 / 200000000)) (hi := (307876103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1383) = 1/(1383 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-307876103 / 500000000) (-123150441 / 200000000) (Real.log (1383 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (377874419 / 1000000000) ≤ -Real.log (5120 / 7471) ∧
    -Real.log (5120 / 7471) ≤ (18893721 / 50000000) := by
  have h := checkLog_sound (w := (2351 / 12591)) (n := 12)
    (lo := (377874419 / 1000000000)) (hi := (18893721 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7471 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7471 / 5120) = 1/(5120 / 7471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (377874419 / 1000000000) (18893721 / 50000000) (Real.log (7471 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7471 / 5120) = -Real.log (5120 / 7471) := by
    rw [show ((7471 / 5120) : ℝ) = ((5120 / 7471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (307334097 / 500000000) ≤ -Real.log (2769 / 5120) ∧
    -Real.log (2769 / 5120) ≤ (122933639 / 200000000) := by
  have h := checkLog_sound (w := (2351 / 7889)) (n := 12)
    (lo := (307334097 / 500000000)) (hi := (122933639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2769) = 1/(2769 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-122933639 / 200000000) (-307334097 / 500000000) (Real.log (2769 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (283540759 / 1000000000) ≤ -Real.log (1000000 / 1327823) ∧
    -Real.log (1000000 / 1327823) ≤ (7088519 / 25000000) := by
  have h := checkLog_sound (w := (327823 / 2327823)) (n := 12)
    (lo := (283540759 / 1000000000)) (hi := (7088519 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327823 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327823 / 1000000) = 1/(1000000 / 1327823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (283540759 / 1000000000) (7088519 / 25000000) (Real.log (1327823 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1327823 / 1000000) = -Real.log (1000000 / 1327823) := by
    rw [show ((1327823 / 1000000) : ℝ) = ((1000000 / 1327823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (19861679 / 50000000) ≤ -Real.log (672177 / 1000000) ∧
    -Real.log (672177 / 1000000) ≤ (397233581 / 1000000000) := by
  have h := checkLog_sound (w := (327823 / 1672177)) (n := 12)
    (lo := (19861679 / 50000000)) (hi := (397233581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 672177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 672177) = 1/(672177 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-397233581 / 1000000000) (-19861679 / 50000000) (Real.log (672177 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (283863039 / 1000000000) ≤ -Real.log (1000000 / 1328251) ∧
    -Real.log (1000000 / 1328251) ≤ (110884 / 390625) := by
  have h := checkLog_sound (w := (328251 / 2328251)) (n := 12)
    (lo := (283863039 / 1000000000)) (hi := (110884 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328251 / 1000000) = 1/(1000000 / 1328251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (283863039 / 1000000000) (110884 / 390625) (Real.log (1328251 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1328251 / 1000000) = -Real.log (1000000 / 1328251) := by
    rw [show ((1328251 / 1000000) : ℝ) = ((1000000 / 1328251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (9946763 / 25000000) ≤ -Real.log (671749 / 1000000) ∧
    -Real.log (671749 / 1000000) ≤ (397870521 / 1000000000) := by
  have h := checkLog_sound (w := (328251 / 1671749)) (n := 12)
    (lo := (9946763 / 25000000)) (hi := (397870521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671749) = 1/(671749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-397870521 / 1000000000) (-9946763 / 25000000) (Real.log (671749 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8569343 / 40000000) ≤ -Real.log (15625 / 19358) ∧
    -Real.log (15625 / 19358) ≤ (26779197 / 125000000) := by
  have h := checkLog_sound (w := (3733 / 34983)) (n := 12)
    (lo := (8569343 / 40000000)) (hi := (26779197 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19358 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19358 / 15625) = 1/(15625 / 19358) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8569343 / 40000000) (26779197 / 125000000) (Real.log (19358 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (19358 / 15625) = -Real.log (15625 / 19358) := by
    rw [show ((19358 / 15625) : ℝ) = ((15625 / 19358) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (27300629 / 100000000) ≤ -Real.log (11892 / 15625) ∧
    -Real.log (11892 / 15625) ≤ (273006291 / 1000000000) := by
  have h := checkLog_sound (w := (3733 / 27517)) (n := 12)
    (lo := (27300629 / 100000000)) (hi := (273006291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11892) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11892) = 1/(11892 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-273006291 / 1000000000) (-27300629 / 100000000) (Real.log (11892 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (214500709 / 1000000000) ≤ -Real.log (1000000 / 1239243) ∧
    -Real.log (1000000 / 1239243) ≤ (21450071 / 100000000) := by
  have h := checkLog_sound (w := (239243 / 2239243)) (n := 12)
    (lo := (214500709 / 1000000000)) (hi := (21450071 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239243 / 1000000) = 1/(1000000 / 1239243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (214500709 / 1000000000) (21450071 / 100000000) (Real.log (1239243 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1239243 / 1000000) = -Real.log (1000000 / 1239243) := by
    rw [show ((1239243 / 1000000) : ℝ) = ((1000000 / 1239243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (34180161 / 125000000) ≤ -Real.log (760757 / 1000000) ∧
    -Real.log (760757 / 1000000) ≤ (273441289 / 1000000000) := by
  have h := checkLog_sound (w := (239243 / 1760757)) (n := 12)
    (lo := (34180161 / 125000000)) (hi := (273441289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760757) = 1/(760757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-273441289 / 1000000000) (-34180161 / 125000000) (Real.log (760757 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (680774339 / 1000000000) ≤ -Real.log (500000000000 / 987703387649) ∧
    -Real.log (500000000000 / 987703387649) ≤ (34038717 / 50000000) := by
  have h := checkLog_sound (w := (487703387649 / 1487703387649)) (n := 12)
    (lo := (680774339 / 1000000000)) (hi := (34038717 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987703387649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987703387649 / 500000000000) = 1/(500000000000 / 987703387649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (680774339 / 1000000000) (34038717 / 50000000) (Real.log (987703387649 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (987703387649 / 500000000000) = -Real.log (500000000000 / 987703387649) := by
    rw [show ((987703387649 / 500000000000) : ℝ) = ((500000000000 / 987703387649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (681733559 / 1000000000) ≤ -Real.log (250000000000 / 494325633533) ∧
    -Real.log (250000000000 / 494325633533) ≤ (17043339 / 25000000) := by
  have h := checkLog_sound (w := (244325633533 / 744325633533)) (n := 12)
    (lo := (681733559 / 1000000000)) (hi := (17043339 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494325633533 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494325633533 / 250000000000) = 1/(250000000000 / 494325633533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (681733559 / 1000000000) (17043339 / 25000000) (Real.log (494325633533 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (494325633533 / 250000000000) = -Real.log (250000000000 / 494325633533) := by
    rw [show ((494325633533 / 250000000000) : ℝ) = ((250000000000 / 494325633533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (97447973 / 200000000) ≤ -Real.log (250000000000 / 406954254961) ∧
    -Real.log (250000000000 / 406954254961) ≤ (243619933 / 500000000) := by
  have h := checkLog_sound (w := (156954254961 / 656954254961)) (n := 12)
    (lo := (97447973 / 200000000)) (hi := (243619933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406954254961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406954254961 / 250000000000) = 1/(250000000000 / 406954254961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (97447973 / 200000000) (243619933 / 500000000) (Real.log (406954254961 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (406954254961 / 250000000000) = -Real.log (250000000000 / 406954254961) := by
    rw [show ((406954254961 / 250000000000) : ℝ) = ((250000000000 / 406954254961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (243970999 / 500000000) ≤ -Real.log (3125000000 / 5090501139) ∧
    -Real.log (3125000000 / 5090501139) ≤ (487941999 / 1000000000) := by
  have h := checkLog_sound (w := (1965501139 / 8215501139)) (n := 12)
    (lo := (243970999 / 500000000)) (hi := (487941999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5090501139 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5090501139 / 3125000000) = 1/(3125000000 / 5090501139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (243970999 / 500000000) (487941999 / 1000000000) (Real.log (5090501139 / 3125000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5090501139 / 3125000000) = -Real.log (3125000000 / 5090501139) := by
    rw [show ((5090501139 / 3125000000) : ℝ) = ((3125000000 / 5090501139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0372

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0373Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0373
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

theorem reflection_log_1_neg : (206680653 / 1000000000) ≤ -Real.log (10240 / 12591) ∧
    -Real.log (10240 / 12591) ≤ (103340327 / 500000000) := by
  have h := checkLog_sound (w := (2351 / 22831)) (n := 12)
    (lo := (206680653 / 1000000000)) (hi := (103340327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12591 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12591 / 10240) = 1/(10240 / 12591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (206680653 / 1000000000) (103340327 / 500000000) (Real.log (12591 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12591 / 10240) = -Real.log (10240 / 12591) := by
    rw [show ((12591 / 10240) : ℝ) = ((10240 / 12591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (52166447 / 200000000) ≤ -Real.log (7889 / 10240) ∧
    -Real.log (7889 / 10240) ≤ (65208059 / 250000000) := by
  have h := checkLog_sound (w := (2351 / 18129)) (n := 12)
    (lo := (52166447 / 200000000)) (hi := (65208059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7889) = 1/(7889 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65208059 / 250000000) (-52166447 / 200000000) (Real.log (7889 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (206442359 / 1000000000) ≤ -Real.log (2560 / 3147) ∧
    -Real.log (2560 / 3147) ≤ (5161059 / 25000000) := by
  have h := checkLog_sound (w := (587 / 5707)) (n := 12)
    (lo := (206442359 / 1000000000)) (hi := (5161059 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3147 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3147 / 2560) = 1/(2560 / 3147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (206442359 / 1000000000) (5161059 / 25000000) (Real.log (3147 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3147 / 2560) = -Real.log (2560 / 3147) := by
    rw [show ((3147 / 2560) : ℝ) = ((2560 / 3147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (260452031 / 1000000000) ≤ -Real.log (1973 / 2560) ∧
    -Real.log (1973 / 2560) ≤ (4069563 / 15625000) := by
  have h := checkLog_sound (w := (587 / 4533)) (n := 12)
    (lo := (260452031 / 1000000000)) (hi := (4069563 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1973) = 1/(1973 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4069563 / 15625000) (-260452031 / 1000000000) (Real.log (1973 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (377874419 / 1000000000) ≤ -Real.log (5120 / 7471) ∧
    -Real.log (5120 / 7471) ≤ (18893721 / 50000000) := by
  have h := checkLog_sound (w := (2351 / 12591)) (n := 12)
    (lo := (377874419 / 1000000000)) (hi := (18893721 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7471 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7471 / 5120) = 1/(5120 / 7471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (377874419 / 1000000000) (18893721 / 50000000) (Real.log (7471 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7471 / 5120) = -Real.log (5120 / 7471) := by
    rw [show ((7471 / 5120) : ℝ) = ((5120 / 7471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (307334097 / 500000000) ≤ -Real.log (2769 / 5120) ∧
    -Real.log (2769 / 5120) ≤ (122933639 / 200000000) := by
  have h := checkLog_sound (w := (2351 / 7889)) (n := 12)
    (lo := (307334097 / 500000000)) (hi := (122933639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2769) = 1/(2769 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-122933639 / 200000000) (-307334097 / 500000000) (Real.log (2769 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (188736393 / 500000000) ≤ -Real.log (1280 / 1867) ∧
    -Real.log (1280 / 1867) ≤ (377472787 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 3147)) (n := 12)
    (lo := (188736393 / 500000000)) (hi := (377472787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1867 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1867 / 1280) = 1/(1280 / 1867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (188736393 / 500000000) (377472787 / 1000000000) (Real.log (1867 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1867 / 1280) = -Real.log (1280 / 1867) := by
    rw [show ((1867 / 1280) : ℝ) = ((1280 / 1867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (613585357 / 1000000000) ≤ -Real.log (693 / 1280) ∧
    -Real.log (693 / 1280) ≤ (306792679 / 500000000) := by
  have h := checkLog_sound (w := (587 / 1973)) (n := 12)
    (lo := (613585357 / 1000000000)) (hi := (306792679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 693) = 1/(693 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-306792679 / 500000000) (-613585357 / 1000000000) (Real.log (693 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35402391 / 125000000) ≤ -Real.log (250000 / 331849) ∧
    -Real.log (250000 / 331849) ≤ (283219129 / 1000000000) := by
  have h := checkLog_sound (w := (81849 / 581849)) (n := 12)
    (lo := (35402391 / 125000000)) (hi := (283219129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331849 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331849 / 250000) = 1/(250000 / 331849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35402391 / 125000000) (283219129 / 1000000000) (Real.log (331849 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (331849 / 250000) = -Real.log (250000 / 331849) := by
    rw [show ((331849 / 250000) : ℝ) = ((250000 / 331849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (99149633 / 250000000) ≤ -Real.log (168151 / 250000) ∧
    -Real.log (168151 / 250000) ≤ (396598533 / 1000000000) := by
  have h := checkLog_sound (w := (81849 / 418151)) (n := 12)
    (lo := (99149633 / 250000000)) (hi := (396598533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 168151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 168151) = 1/(168151 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-396598533 / 1000000000) (-99149633 / 250000000) (Real.log (168151 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35442689 / 125000000) ≤ -Real.log (62500 / 82989) ∧
    -Real.log (62500 / 82989) ≤ (283541513 / 1000000000) := by
  have h := checkLog_sound (w := (20489 / 145489)) (n := 12)
    (lo := (35442689 / 125000000)) (hi := (283541513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82989 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82989 / 62500) = 1/(62500 / 82989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35442689 / 125000000) (283541513 / 1000000000) (Real.log (82989 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (82989 / 62500) = -Real.log (62500 / 82989) := by
    rw [show ((82989 / 62500) : ℝ) = ((62500 / 82989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (397235067 / 1000000000) ≤ -Real.log (42011 / 62500) ∧
    -Real.log (42011 / 62500) ≤ (99308767 / 250000000) := by
  have h := checkLog_sound (w := (20489 / 104511)) (n := 12)
    (lo := (397235067 / 1000000000)) (hi := (99308767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42011) = 1/(42011 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-99308767 / 250000000) (-397235067 / 1000000000) (Real.log (42011 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26745897 / 125000000) ≤ -Real.log (500000 / 619291) ∧
    -Real.log (500000 / 619291) ≤ (213967177 / 1000000000) := by
  have h := checkLog_sound (w := (119291 / 1119291)) (n := 12)
    (lo := (26745897 / 125000000)) (hi := (213967177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619291 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619291 / 500000) = 1/(500000 / 619291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26745897 / 125000000) (213967177 / 1000000000) (Real.log (619291 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (619291 / 500000) = -Real.log (500000 / 619291) := by
    rw [show ((619291 / 500000) : ℝ) = ((500000 / 619291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (136286397 / 500000000) ≤ -Real.log (380709 / 500000) ∧
    -Real.log (380709 / 500000) ≤ (54514559 / 200000000) := by
  have h := checkLog_sound (w := (119291 / 880709)) (n := 12)
    (lo := (136286397 / 500000000)) (hi := (54514559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380709) = 1/(380709 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-54514559 / 200000000) (-136286397 / 500000000) (Real.log (380709 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (107117191 / 500000000) ≤ -Real.log (1000000 / 1238913) ∧
    -Real.log (1000000 / 1238913) ≤ (214234383 / 1000000000) := by
  have h := checkLog_sound (w := (238913 / 2238913)) (n := 12)
    (lo := (107117191 / 500000000)) (hi := (214234383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238913 / 1000000) = 1/(1000000 / 1238913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (107117191 / 500000000) (214234383 / 1000000000) (Real.log (1238913 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1238913 / 1000000) = -Real.log (1000000 / 1238913) := by
    rw [show ((1238913 / 1000000) : ℝ) = ((1000000 / 1238913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (68251901 / 250000000) ≤ -Real.log (761087 / 1000000) ∧
    -Real.log (761087 / 1000000) ≤ (54601521 / 200000000) := by
  have h := checkLog_sound (w := (238913 / 1761087)) (n := 12)
    (lo := (68251901 / 250000000)) (hi := (54601521 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761087) = 1/(761087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-54601521 / 200000000) (-68251901 / 250000000) (Real.log (761087 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (33990883 / 50000000) ≤ -Real.log (500000000000 / 986758925013) ∧
    -Real.log (500000000000 / 986758925013) ≤ (679817661 / 1000000000) := by
  have h := checkLog_sound (w := (486758925013 / 1486758925013)) (n := 12)
    (lo := (33990883 / 50000000)) (hi := (679817661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986758925013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986758925013 / 500000000000) = 1/(500000000000 / 986758925013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (33990883 / 50000000) (679817661 / 1000000000) (Real.log (986758925013 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (986758925013 / 500000000000) = -Real.log (500000000000 / 986758925013) := by
    rw [show ((986758925013 / 500000000000) : ℝ) = ((500000000000 / 986758925013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (34038829 / 50000000) ≤ -Real.log (100000000000 / 197541120183) ∧
    -Real.log (100000000000 / 197541120183) ≤ (680776581 / 1000000000) := by
  have h := checkLog_sound (w := (97541120183 / 297541120183)) (n := 12)
    (lo := (34038829 / 50000000)) (hi := (680776581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197541120183 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197541120183 / 100000000000) = 1/(100000000000 / 197541120183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (34038829 / 50000000) (680776581 / 1000000000) (Real.log (197541120183 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (197541120183 / 100000000000) = -Real.log (100000000000 / 197541120183) := by
    rw [show ((197541120183 / 100000000000) : ℝ) = ((100000000000 / 197541120183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (486539971 / 1000000000) ≤ -Real.log (500000000000 / 813339059491) ∧
    -Real.log (500000000000 / 813339059491) ≤ (121634993 / 250000000) := by
  have h := checkLog_sound (w := (313339059491 / 1313339059491)) (n := 12)
    (lo := (486539971 / 1000000000)) (hi := (121634993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813339059491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813339059491 / 500000000000) = 1/(500000000000 / 813339059491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (486539971 / 1000000000) (121634993 / 250000000) (Real.log (813339059491 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (813339059491 / 500000000000) = -Real.log (500000000000 / 813339059491) := by
    rw [show ((813339059491 / 500000000000) : ℝ) = ((500000000000 / 813339059491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (243620993 / 500000000) ≤ -Real.log (500000000000 / 813910236281) ∧
    -Real.log (500000000000 / 813910236281) ≤ (487241987 / 1000000000) := by
  have h := checkLog_sound (w := (313910236281 / 1313910236281)) (n := 12)
    (lo := (243620993 / 500000000)) (hi := (487241987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813910236281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813910236281 / 500000000000) = 1/(500000000000 / 813910236281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (243620993 / 500000000) (487241987 / 1000000000) (Real.log (813910236281 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (813910236281 / 500000000000) = -Real.log (500000000000 / 813910236281) := by
    rw [show ((813910236281 / 500000000000) : ℝ) = ((500000000000 / 813910236281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0373

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0374Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0374
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

theorem reflection_log_1_neg : (206442359 / 1000000000) ≤ -Real.log (2560 / 3147) ∧
    -Real.log (2560 / 3147) ≤ (5161059 / 25000000) := by
  have h := checkLog_sound (w := (587 / 5707)) (n := 12)
    (lo := (206442359 / 1000000000)) (hi := (5161059 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3147 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3147 / 2560) = 1/(2560 / 3147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (206442359 / 1000000000) (5161059 / 25000000) (Real.log (3147 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3147 / 2560) = -Real.log (2560 / 3147) := by
    rw [show ((3147 / 2560) : ℝ) = ((2560 / 3147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (260452031 / 1000000000) ≤ -Real.log (1973 / 2560) ∧
    -Real.log (1973 / 2560) ≤ (4069563 / 15625000) := by
  have h := checkLog_sound (w := (587 / 4533)) (n := 12)
    (lo := (260452031 / 1000000000)) (hi := (4069563 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1973) = 1/(1973 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4069563 / 15625000) (-260452031 / 1000000000) (Real.log (1973 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (25775501 / 125000000) ≤ -Real.log (2048 / 2517) ∧
    -Real.log (2048 / 2517) ≤ (206204009 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 4565)) (n := 12)
    (lo := (25775501 / 125000000)) (hi := (206204009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2517 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2517 / 2048) = 1/(2048 / 2517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (25775501 / 125000000) (206204009 / 1000000000) (Real.log (2517 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2517 / 2048) = -Real.log (2048 / 2517) := by
    rw [show ((2517 / 2048) : ℝ) = ((2048 / 2517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (260071971 / 1000000000) ≤ -Real.log (1579 / 2048) ∧
    -Real.log (1579 / 2048) ≤ (65017993 / 250000000) := by
  have h := checkLog_sound (w := (469 / 3627)) (n := 12)
    (lo := (260071971 / 1000000000)) (hi := (65017993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1579) = 1/(1579 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65017993 / 250000000) (-260071971 / 1000000000) (Real.log (1579 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (188736393 / 500000000) ≤ -Real.log (1280 / 1867) ∧
    -Real.log (1280 / 1867) ≤ (377472787 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 3147)) (n := 12)
    (lo := (188736393 / 500000000)) (hi := (377472787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1867 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1867 / 1280) = 1/(1280 / 1867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (188736393 / 500000000) (377472787 / 1000000000) (Real.log (1867 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1867 / 1280) = -Real.log (1280 / 1867) := by
    rw [show ((1867 / 1280) : ℝ) = ((1280 / 1867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (613585357 / 1000000000) ≤ -Real.log (693 / 1280) ∧
    -Real.log (693 / 1280) ≤ (306792679 / 500000000) := by
  have h := checkLog_sound (w := (587 / 1973)) (n := 12)
    (lo := (613585357 / 1000000000)) (hi := (306792679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 693) = 1/(693 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-306792679 / 500000000) (-613585357 / 1000000000) (Real.log (693 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (377070991 / 1000000000) ≤ -Real.log (1024 / 1493) ∧
    -Real.log (1024 / 1493) ≤ (23566937 / 62500000) := by
  have h := checkLog_sound (w := (469 / 2517)) (n := 12)
    (lo := (377070991 / 1000000000)) (hi := (23566937 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493 / 1024) = 1/(1024 / 1493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (377070991 / 1000000000) (23566937 / 62500000) (Real.log (1493 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1493 / 1024) = -Real.log (1024 / 1493) := by
    rw [show ((1493 / 1024) : ℝ) = ((1024 / 1493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (612503691 / 1000000000) ≤ -Real.log (555 / 1024) ∧
    -Real.log (555 / 1024) ≤ (153125923 / 250000000) := by
  have h := checkLog_sound (w := (469 / 1579)) (n := 12)
    (lo := (612503691 / 1000000000)) (hi := (153125923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 555) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 555) = 1/(555 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-153125923 / 250000000) (-612503691 / 1000000000) (Real.log (555 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (141448697 / 500000000) ≤ -Real.log (1000000 / 1326969) ∧
    -Real.log (1000000 / 1326969) ≤ (56579479 / 200000000) := by
  have h := checkLog_sound (w := (326969 / 2326969)) (n := 12)
    (lo := (141448697 / 500000000)) (hi := (56579479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326969 / 1000000) = 1/(1000000 / 1326969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (141448697 / 500000000) (56579479 / 200000000) (Real.log (1326969 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1326969 / 1000000) = -Real.log (1000000 / 1326969) := by
    rw [show ((1326969 / 1000000) : ℝ) = ((1000000 / 1326969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (395963887 / 1000000000) ≤ -Real.log (673031 / 1000000) ∧
    -Real.log (673031 / 1000000) ≤ (24747743 / 62500000) := by
  have h := checkLog_sound (w := (326969 / 1673031)) (n := 12)
    (lo := (395963887 / 1000000000)) (hi := (24747743 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673031) = 1/(673031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-24747743 / 62500000) (-395963887 / 1000000000) (Real.log (673031 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (283219881 / 1000000000) ≤ -Real.log (1000000 / 1327397) ∧
    -Real.log (1000000 / 1327397) ≤ (141609941 / 500000000) := by
  have h := checkLog_sound (w := (327397 / 2327397)) (n := 12)
    (lo := (283219881 / 1000000000)) (hi := (141609941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327397 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327397 / 1000000) = 1/(1000000 / 1327397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (283219881 / 1000000000) (141609941 / 500000000) (Real.log (1327397 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1327397 / 1000000) = -Real.log (1000000 / 1327397) := by
    rw [show ((1327397 / 1000000) : ℝ) = ((1000000 / 1327397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (396600019 / 1000000000) ≤ -Real.log (672603 / 1000000) ∧
    -Real.log (672603 / 1000000) ≤ (19830001 / 50000000) := by
  have h := checkLog_sound (w := (327397 / 1672603)) (n := 12)
    (lo := (396600019 / 1000000000)) (hi := (19830001 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 672603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 672603) = 1/(672603 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-19830001 / 50000000) (-396600019 / 1000000000) (Real.log (672603 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (213700707 / 1000000000) ≤ -Real.log (250000 / 309563) ∧
    -Real.log (250000 / 309563) ≤ (53425177 / 250000000) := by
  have h := checkLog_sound (w := (59563 / 559563)) (n := 12)
    (lo := (213700707 / 1000000000)) (hi := (53425177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309563 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309563 / 250000) = 1/(250000 / 309563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (213700707 / 1000000000) (53425177 / 250000000) (Real.log (309563 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (309563 / 250000) = -Real.log (250000 / 309563) := by
    rw [show ((309563 / 250000) : ℝ) = ((250000 / 309563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (136069743 / 500000000) ≤ -Real.log (190437 / 250000) ∧
    -Real.log (190437 / 250000) ≤ (272139487 / 1000000000) := by
  have h := checkLog_sound (w := (59563 / 440437)) (n := 12)
    (lo := (136069743 / 500000000)) (hi := (272139487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190437) = 1/(190437 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-272139487 / 1000000000) (-136069743 / 500000000) (Real.log (190437 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (13372999 / 62500000) ≤ -Real.log (1000000 / 1238583) ∧
    -Real.log (1000000 / 1238583) ≤ (42793597 / 200000000) := by
  have h := checkLog_sound (w := (238583 / 2238583)) (n := 12)
    (lo := (13372999 / 62500000)) (hi := (42793597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238583 / 1000000) = 1/(1000000 / 1238583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (13372999 / 62500000) (42793597 / 200000000) (Real.log (1238583 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1238583 / 1000000) = -Real.log (1000000 / 1238583) := by
    rw [show ((1238583 / 1000000) : ℝ) = ((1000000 / 1238583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (272574107 / 1000000000) ≤ -Real.log (761417 / 1000000) ∧
    -Real.log (761417 / 1000000) ≤ (68143527 / 250000000) := by
  have h := checkLog_sound (w := (238583 / 1761417)) (n := 12)
    (lo := (272574107 / 1000000000)) (hi := (68143527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761417) = 1/(761417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-68143527 / 250000000) (-272574107 / 1000000000) (Real.log (761417 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (339430641 / 500000000) ≤ -Real.log (250000000000 / 492907830397) ∧
    -Real.log (250000000000 / 492907830397) ≤ (678861283 / 1000000000) := by
  have h := checkLog_sound (w := (242907830397 / 742907830397)) (n := 12)
    (lo := (339430641 / 500000000)) (hi := (678861283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492907830397 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492907830397 / 250000000000) = 1/(250000000000 / 492907830397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (339430641 / 500000000) (678861283 / 1000000000) (Real.log (492907830397 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (492907830397 / 250000000000) = -Real.log (250000000000 / 492907830397) := by
    rw [show ((492907830397 / 250000000000) : ℝ) = ((250000000000 / 492907830397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (679819901 / 1000000000) ≤ -Real.log (50000000000 / 98676113547) ∧
    -Real.log (50000000000 / 98676113547) ≤ (339909951 / 500000000) := by
  have h := checkLog_sound (w := (48676113547 / 148676113547)) (n := 12)
    (lo := (679819901 / 1000000000)) (hi := (339909951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98676113547 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98676113547 / 50000000000) = 1/(50000000000 / 98676113547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (679819901 / 1000000000) (339909951 / 500000000) (Real.log (98676113547 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (98676113547 / 50000000000) = -Real.log (50000000000 / 98676113547) := by
    rw [show ((98676113547 / 50000000000) : ℝ) = ((50000000000 / 98676113547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (242920097 / 500000000) ≤ -Real.log (31250000000 / 50798131403) ∧
    -Real.log (31250000000 / 50798131403) ≤ (97168039 / 200000000) := by
  have h := checkLog_sound (w := (19548131403 / 82048131403)) (n := 12)
    (lo := (242920097 / 500000000)) (hi := (97168039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50798131403 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50798131403 / 31250000000) = 1/(31250000000 / 50798131403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (242920097 / 500000000) (97168039 / 200000000) (Real.log (50798131403 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (50798131403 / 31250000000) = -Real.log (31250000000 / 50798131403) := by
    rw [show ((50798131403 / 31250000000) : ℝ) = ((31250000000 / 50798131403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (121635523 / 250000000) ≤ -Real.log (250000000000 / 406670392177) ∧
    -Real.log (250000000000 / 406670392177) ≤ (486542093 / 1000000000) := by
  have h := checkLog_sound (w := (156670392177 / 656670392177)) (n := 12)
    (lo := (121635523 / 250000000)) (hi := (486542093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406670392177 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406670392177 / 250000000000) = 1/(250000000000 / 406670392177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (121635523 / 250000000) (486542093 / 1000000000) (Real.log (406670392177 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (406670392177 / 250000000000) = -Real.log (250000000000 / 406670392177) := by
    rw [show ((406670392177 / 250000000000) : ℝ) = ((250000000000 / 406670392177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0374

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0375Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0375
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

theorem reflection_log_1_neg : (25775501 / 125000000) ≤ -Real.log (2048 / 2517) ∧
    -Real.log (2048 / 2517) ≤ (206204009 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 4565)) (n := 12)
    (lo := (25775501 / 125000000)) (hi := (206204009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2517 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2517 / 2048) = 1/(2048 / 2517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (25775501 / 125000000) (206204009 / 1000000000) (Real.log (2517 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2517 / 2048) = -Real.log (2048 / 2517) := by
    rw [show ((2517 / 2048) : ℝ) = ((2048 / 2517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (260071971 / 1000000000) ≤ -Real.log (1579 / 2048) ∧
    -Real.log (1579 / 2048) ≤ (65017993 / 250000000) := by
  have h := checkLog_sound (w := (469 / 3627)) (n := 12)
    (lo := (260071971 / 1000000000)) (hi := (65017993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1579) = 1/(1579 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65017993 / 250000000) (-260071971 / 1000000000) (Real.log (1579 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (205965601 / 1000000000) ≤ -Real.log (5120 / 6291) ∧
    -Real.log (5120 / 6291) ≤ (102982801 / 500000000) := by
  have h := checkLog_sound (w := (1171 / 11411)) (n := 12)
    (lo := (205965601 / 1000000000)) (hi := (102982801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6291 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6291 / 5120) = 1/(5120 / 6291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (205965601 / 1000000000) (102982801 / 500000000) (Real.log (6291 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6291 / 5120) = -Real.log (5120 / 6291) := by
    rw [show ((6291 / 5120) : ℝ) = ((5120 / 6291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (32461507 / 125000000) ≤ -Real.log (3949 / 5120) ∧
    -Real.log (3949 / 5120) ≤ (259692057 / 1000000000) := by
  have h := checkLog_sound (w := (1171 / 9069)) (n := 12)
    (lo := (32461507 / 125000000)) (hi := (259692057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3949) = 1/(3949 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-259692057 / 1000000000) (-32461507 / 125000000) (Real.log (3949 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (377070991 / 1000000000) ≤ -Real.log (1024 / 1493) ∧
    -Real.log (1024 / 1493) ≤ (23566937 / 62500000) := by
  have h := checkLog_sound (w := (469 / 2517)) (n := 12)
    (lo := (377070991 / 1000000000)) (hi := (23566937 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493 / 1024) = 1/(1024 / 1493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (377070991 / 1000000000) (23566937 / 62500000) (Real.log (1493 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1493 / 1024) = -Real.log (1024 / 1493) := by
    rw [show ((1493 / 1024) : ℝ) = ((1024 / 1493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (612503691 / 1000000000) ≤ -Real.log (555 / 1024) ∧
    -Real.log (555 / 1024) ≤ (153125923 / 250000000) := by
  have h := checkLog_sound (w := (469 / 1579)) (n := 12)
    (lo := (612503691 / 1000000000)) (hi := (153125923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 555) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 555) = 1/(555 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-153125923 / 250000000) (-612503691 / 1000000000) (Real.log (555 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (75333807 / 200000000) ≤ -Real.log (2560 / 3731) ∧
    -Real.log (2560 / 3731) ≤ (94167259 / 250000000) := by
  have h := checkLog_sound (w := (1171 / 6291)) (n := 12)
    (lo := (75333807 / 200000000)) (hi := (94167259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3731 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3731 / 2560) = 1/(2560 / 3731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (75333807 / 200000000) (94167259 / 250000000) (Real.log (3731 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3731 / 2560) = -Real.log (2560 / 3731) := by
    rw [show ((3731 / 2560) : ℝ) = ((2560 / 3731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (305711597 / 500000000) ≤ -Real.log (1389 / 2560) ∧
    -Real.log (1389 / 2560) ≤ (122284639 / 200000000) := by
  have h := checkLog_sound (w := (1171 / 3949)) (n := 12)
    (lo := (305711597 / 500000000)) (hi := (122284639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1389) = 1/(1389 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-122284639 / 200000000) (-305711597 / 500000000) (Real.log (1389 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (141287401 / 500000000) ≤ -Real.log (1000000 / 1326541) ∧
    -Real.log (1000000 / 1326541) ≤ (282574803 / 1000000000) := by
  have h := checkLog_sound (w := (326541 / 2326541)) (n := 12)
    (lo := (141287401 / 500000000)) (hi := (282574803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326541 / 1000000) = 1/(1000000 / 1326541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (141287401 / 500000000) (282574803 / 1000000000) (Real.log (1326541 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1326541 / 1000000) = -Real.log (1000000 / 1326541) := by
    rw [show ((1326541 / 1000000) : ℝ) = ((1000000 / 1326541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (395328161 / 1000000000) ≤ -Real.log (673459 / 1000000) ∧
    -Real.log (673459 / 1000000) ≤ (197664081 / 500000000) := by
  have h := checkLog_sound (w := (326541 / 1673459)) (n := 12)
    (lo := (395328161 / 1000000000)) (hi := (197664081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673459) = 1/(673459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-197664081 / 500000000) (-395328161 / 1000000000) (Real.log (673459 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (282898147 / 1000000000) ≤ -Real.log (100000 / 132697) ∧
    -Real.log (100000 / 132697) ≤ (70724537 / 250000000) := by
  have h := checkLog_sound (w := (32697 / 232697)) (n := 12)
    (lo := (282898147 / 1000000000)) (hi := (70724537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132697 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132697 / 100000) = 1/(100000 / 132697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (282898147 / 1000000000) (70724537 / 250000000) (Real.log (132697 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (132697 / 100000) = -Real.log (100000 / 132697) := by
    rw [show ((132697 / 100000) : ℝ) = ((100000 / 132697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (395965373 / 1000000000) ≤ -Real.log (67303 / 100000) ∧
    -Real.log (67303 / 100000) ≤ (197982687 / 500000000) := by
  have h := checkLog_sound (w := (32697 / 167303)) (n := 12)
    (lo := (395965373 / 1000000000)) (hi := (197982687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 67303) = 1/(67303 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-197982687 / 500000000) (-395965373 / 1000000000) (Real.log (67303 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (213433359 / 1000000000) ≤ -Real.log (1000000 / 1237921) ∧
    -Real.log (1000000 / 1237921) ≤ (2667917 / 12500000) := by
  have h := checkLog_sound (w := (237921 / 2237921)) (n := 12)
    (lo := (213433359 / 1000000000)) (hi := (2667917 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237921 / 1000000) = 1/(1000000 / 1237921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (213433359 / 1000000000) (2667917 / 12500000) (Real.log (1237921 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1237921 / 1000000) = -Real.log (1000000 / 1237921) := by
    rw [show ((1237921 / 1000000) : ℝ) = ((1000000 / 1237921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (135852527 / 500000000) ≤ -Real.log (762079 / 1000000) ∧
    -Real.log (762079 / 1000000) ≤ (54341011 / 200000000) := by
  have h := checkLog_sound (w := (237921 / 1762079)) (n := 12)
    (lo := (135852527 / 500000000)) (hi := (54341011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 762079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 762079) = 1/(762079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-54341011 / 200000000) (-135852527 / 500000000) (Real.log (762079 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42740303 / 200000000) ≤ -Real.log (1000000 / 1238253) ∧
    -Real.log (1000000 / 1238253) ≤ (53425379 / 250000000) := by
  have h := checkLog_sound (w := (238253 / 2238253)) (n := 12)
    (lo := (42740303 / 200000000)) (hi := (53425379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238253 / 1000000) = 1/(1000000 / 1238253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42740303 / 200000000) (53425379 / 250000000) (Real.log (1238253 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1238253 / 1000000) = -Real.log (1000000 / 1238253) := by
    rw [show ((1238253 / 1000000) : ℝ) = ((1000000 / 1238253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (272140799 / 1000000000) ≤ -Real.log (761747 / 1000000) ∧
    -Real.log (761747 / 1000000) ≤ (21261 / 78125) := by
  have h := checkLog_sound (w := (238253 / 1761747)) (n := 12)
    (lo := (272140799 / 1000000000)) (hi := (21261 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761747) = 1/(761747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-21261 / 78125) (-272140799 / 1000000000) (Real.log (761747 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (677902963 / 1000000000) ≤ -Real.log (62500000000 / 123108923483) ∧
    -Real.log (62500000000 / 123108923483) ≤ (169475741 / 250000000) := by
  have h := checkLog_sound (w := (60608923483 / 185608923483)) (n := 12)
    (lo := (677902963 / 1000000000)) (hi := (169475741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123108923483 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123108923483 / 62500000000) = 1/(62500000000 / 123108923483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (677902963 / 1000000000) (169475741 / 250000000) (Real.log (123108923483 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (123108923483 / 62500000000) = -Real.log (62500000000 / 123108923483) := by
    rw [show ((123108923483 / 62500000000) : ℝ) = ((62500000000 / 123108923483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (678863521 / 1000000000) ≤ -Real.log (250000000000 / 492908934223) ∧
    -Real.log (250000000000 / 492908934223) ≤ (339431761 / 500000000) := by
  have h := checkLog_sound (w := (242908934223 / 742908934223)) (n := 12)
    (lo := (678863521 / 1000000000)) (hi := (339431761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492908934223 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492908934223 / 250000000000) = 1/(250000000000 / 492908934223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (678863521 / 1000000000) (339431761 / 500000000) (Real.log (492908934223 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (492908934223 / 250000000000) = -Real.log (250000000000 / 492908934223) := by
    rw [show ((492908934223 / 250000000000) : ℝ) = ((250000000000 / 492908934223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (485138413 / 1000000000) ≤ -Real.log (500000000000 / 812199916281) ∧
    -Real.log (500000000000 / 812199916281) ≤ (242569207 / 500000000) := by
  have h := checkLog_sound (w := (312199916281 / 1312199916281)) (n := 12)
    (lo := (485138413 / 1000000000)) (hi := (242569207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812199916281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812199916281 / 500000000000) = 1/(500000000000 / 812199916281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (485138413 / 1000000000) (242569207 / 500000000) (Real.log (812199916281 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (812199916281 / 500000000000) = -Real.log (500000000000 / 812199916281) := by
    rw [show ((812199916281 / 500000000000) : ℝ) = ((500000000000 / 812199916281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (242921157 / 500000000) ≤ -Real.log (500000000000 / 812771825817) ∧
    -Real.log (500000000000 / 812771825817) ≤ (97168463 / 200000000) := by
  have h := checkLog_sound (w := (312771825817 / 1312771825817)) (n := 12)
    (lo := (242921157 / 500000000)) (hi := (97168463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812771825817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812771825817 / 500000000000) = 1/(500000000000 / 812771825817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (242921157 / 500000000) (97168463 / 200000000) (Real.log (812771825817 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (812771825817 / 500000000000) = -Real.log (500000000000 / 812771825817) := by
    rw [show ((812771825817 / 500000000000) : ℝ) = ((500000000000 / 812771825817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0375

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0376Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0376
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

theorem reflection_log_1_neg : (205965601 / 1000000000) ≤ -Real.log (5120 / 6291) ∧
    -Real.log (5120 / 6291) ≤ (102982801 / 500000000) := by
  have h := checkLog_sound (w := (1171 / 11411)) (n := 12)
    (lo := (205965601 / 1000000000)) (hi := (102982801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6291 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6291 / 5120) = 1/(5120 / 6291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (205965601 / 1000000000) (102982801 / 500000000) (Real.log (6291 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6291 / 5120) = -Real.log (5120 / 6291) := by
    rw [show ((6291 / 5120) : ℝ) = ((5120 / 6291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (32461507 / 125000000) ≤ -Real.log (3949 / 5120) ∧
    -Real.log (3949 / 5120) ≤ (259692057 / 1000000000) := by
  have h := checkLog_sound (w := (1171 / 9069)) (n := 12)
    (lo := (32461507 / 125000000)) (hi := (259692057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3949) = 1/(3949 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-259692057 / 1000000000) (-32461507 / 125000000) (Real.log (3949 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (205727137 / 1000000000) ≤ -Real.log (10240 / 12579) ∧
    -Real.log (10240 / 12579) ≤ (102863569 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 22819)) (n := 12)
    (lo := (205727137 / 1000000000)) (hi := (102863569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12579 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12579 / 10240) = 1/(10240 / 12579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (205727137 / 1000000000) (102863569 / 500000000) (Real.log (12579 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12579 / 10240) = -Real.log (10240 / 12579) := by
    rw [show ((12579 / 10240) : ℝ) = ((10240 / 12579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (51862457 / 200000000) ≤ -Real.log (7901 / 10240) ∧
    -Real.log (7901 / 10240) ≤ (129656143 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 18141)) (n := 12)
    (lo := (51862457 / 200000000)) (hi := (129656143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7901) = 1/(7901 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-129656143 / 500000000) (-51862457 / 200000000) (Real.log (7901 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (75333807 / 200000000) ≤ -Real.log (2560 / 3731) ∧
    -Real.log (2560 / 3731) ≤ (94167259 / 250000000) := by
  have h := checkLog_sound (w := (1171 / 6291)) (n := 12)
    (lo := (75333807 / 200000000)) (hi := (94167259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3731 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3731 / 2560) = 1/(2560 / 3731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (75333807 / 200000000) (94167259 / 250000000) (Real.log (3731 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3731 / 2560) = -Real.log (2560 / 3731) := by
    rw [show ((3731 / 2560) : ℝ) = ((2560 / 3731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (305711597 / 500000000) ≤ -Real.log (1389 / 2560) ∧
    -Real.log (1389 / 2560) ≤ (122284639 / 200000000) := by
  have h := checkLog_sound (w := (1171 / 3949)) (n := 12)
    (lo := (305711597 / 500000000)) (hi := (122284639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1389) = 1/(1389 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-122284639 / 200000000) (-305711597 / 500000000) (Real.log (1389 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (376266917 / 1000000000) ≤ -Real.log (5120 / 7459) ∧
    -Real.log (5120 / 7459) ≤ (188133459 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 12579)) (n := 12)
    (lo := (376266917 / 1000000000)) (hi := (188133459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7459 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7459 / 5120) = 1/(5120 / 7459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (376266917 / 1000000000) (188133459 / 500000000) (Real.log (7459 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7459 / 5120) = -Real.log (5120 / 7459) := by
    rw [show ((7459 / 5120) : ℝ) = ((5120 / 7459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (610343863 / 1000000000) ≤ -Real.log (2781 / 5120) ∧
    -Real.log (2781 / 5120) ≤ (76292983 / 125000000) := by
  have h := checkLog_sound (w := (2339 / 7901)) (n := 12)
    (lo := (610343863 / 1000000000)) (hi := (76292983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2781) = 1/(2781 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-76292983 / 125000000) (-610343863 / 1000000000) (Real.log (2781 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (14112643 / 50000000) ≤ -Real.log (500000 / 663057) ∧
    -Real.log (500000 / 663057) ≤ (282252861 / 1000000000) := by
  have h := checkLog_sound (w := (163057 / 1163057)) (n := 12)
    (lo := (14112643 / 50000000)) (hi := (282252861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663057 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663057 / 500000) = 1/(500000 / 663057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (14112643 / 50000000) (282252861 / 1000000000) (Real.log (663057 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (663057 / 500000) = -Real.log (500000 / 663057) := by
    rw [show ((663057 / 500000) : ℝ) = ((500000 / 663057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (394694321 / 1000000000) ≤ -Real.log (336943 / 500000) ∧
    -Real.log (336943 / 500000) ≤ (197347161 / 500000000) := by
  have h := checkLog_sound (w := (163057 / 836943)) (n := 12)
    (lo := (394694321 / 1000000000)) (hi := (197347161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 336943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 336943) = 1/(336943 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-197347161 / 500000000) (-394694321 / 1000000000) (Real.log (336943 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (28257631 / 100000000) ≤ -Real.log (1000000 / 1326543) ∧
    -Real.log (1000000 / 1326543) ≤ (282576311 / 1000000000) := by
  have h := checkLog_sound (w := (326543 / 2326543)) (n := 12)
    (lo := (28257631 / 100000000)) (hi := (282576311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326543 / 1000000) = 1/(1000000 / 1326543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (28257631 / 100000000) (282576311 / 1000000000) (Real.log (1326543 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1326543 / 1000000) = -Real.log (1000000 / 1326543) := by
    rw [show ((1326543 / 1000000) : ℝ) = ((1000000 / 1326543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (39533113 / 100000000) ≤ -Real.log (673457 / 1000000) ∧
    -Real.log (673457 / 1000000) ≤ (395331131 / 1000000000) := by
  have h := checkLog_sound (w := (326543 / 1673457)) (n := 12)
    (lo := (39533113 / 100000000)) (hi := (395331131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673457) = 1/(673457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-395331131 / 1000000000) (-39533113 / 100000000) (Real.log (673457 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (53291889 / 250000000) ≤ -Real.log (125000 / 154699) ∧
    -Real.log (125000 / 154699) ≤ (213167557 / 1000000000) := by
  have h := checkLog_sound (w := (29699 / 279699)) (n := 12)
    (lo := (53291889 / 250000000)) (hi := (213167557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154699 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154699 / 125000) = 1/(125000 / 154699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (53291889 / 250000000) (213167557 / 1000000000) (Real.log (154699 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (154699 / 125000) = -Real.log (125000 / 154699) := by
    rw [show ((154699 / 125000) : ℝ) = ((125000 / 154699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (271273433 / 1000000000) ≤ -Real.log (95301 / 125000) ∧
    -Real.log (95301 / 125000) ≤ (135636717 / 500000000) := by
  have h := checkLog_sound (w := (29699 / 220301)) (n := 12)
    (lo := (271273433 / 1000000000)) (hi := (135636717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95301) = 1/(95301 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-135636717 / 500000000) (-271273433 / 1000000000) (Real.log (95301 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (213434167 / 1000000000) ≤ -Real.log (500000 / 618961) ∧
    -Real.log (500000 / 618961) ≤ (26679271 / 125000000) := by
  have h := checkLog_sound (w := (118961 / 1118961)) (n := 12)
    (lo := (213434167 / 1000000000)) (hi := (26679271 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618961 / 500000) = 1/(500000 / 618961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (213434167 / 1000000000) (26679271 / 125000000) (Real.log (618961 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (618961 / 500000) = -Real.log (500000 / 618961) := by
    rw [show ((618961 / 500000) : ℝ) = ((500000 / 618961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (135853183 / 500000000) ≤ -Real.log (381039 / 500000) ∧
    -Real.log (381039 / 500000) ≤ (271706367 / 1000000000) := by
  have h := checkLog_sound (w := (118961 / 881039)) (n := 12)
    (lo := (135853183 / 500000000)) (hi := (271706367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381039) = 1/(381039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-271706367 / 1000000000) (-135853183 / 500000000) (Real.log (381039 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (338473591 / 500000000) ≤ -Real.log (500000000000 / 983930516437) ∧
    -Real.log (500000000000 / 983930516437) ≤ (676947183 / 1000000000) := by
  have h := checkLog_sound (w := (483930516437 / 1483930516437)) (n := 12)
    (lo := (338473591 / 500000000)) (hi := (676947183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983930516437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983930516437 / 500000000000) = 1/(500000000000 / 983930516437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (338473591 / 500000000) (676947183 / 1000000000) (Real.log (983930516437 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (983930516437 / 500000000000) = -Real.log (500000000000 / 983930516437) := by
    rw [show ((983930516437 / 500000000000) : ℝ) = ((500000000000 / 983930516437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (8473843 / 12500000) ≤ -Real.log (125000000000 / 246218949391) ∧
    -Real.log (125000000000 / 246218949391) ≤ (677907441 / 1000000000) := by
  have h := checkLog_sound (w := (121218949391 / 371218949391)) (n := 12)
    (lo := (8473843 / 12500000)) (hi := (677907441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246218949391 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246218949391 / 125000000000) = 1/(125000000000 / 246218949391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (8473843 / 12500000) (677907441 / 1000000000) (Real.log (246218949391 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (246218949391 / 125000000000) = -Real.log (125000000000 / 246218949391) := by
    rw [show ((246218949391 / 125000000000) : ℝ) = ((125000000000 / 246218949391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (484440989 / 1000000000) ≤ -Real.log (500000000000 / 811633665963) ∧
    -Real.log (500000000000 / 811633665963) ≤ (48444099 / 100000000) := by
  have h := checkLog_sound (w := (311633665963 / 1311633665963)) (n := 12)
    (lo := (484440989 / 1000000000)) (hi := (48444099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811633665963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811633665963 / 500000000000) = 1/(500000000000 / 811633665963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (484440989 / 1000000000) (48444099 / 100000000) (Real.log (811633665963 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (811633665963 / 500000000000) = -Real.log (500000000000 / 811633665963) := by
    rw [show ((811633665963 / 500000000000) : ℝ) = ((500000000000 / 811633665963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (485140533 / 1000000000) ≤ -Real.log (500000000000 / 812201638153) ∧
    -Real.log (500000000000 / 812201638153) ≤ (242570267 / 500000000) := by
  have h := checkLog_sound (w := (312201638153 / 1312201638153)) (n := 12)
    (lo := (485140533 / 1000000000)) (hi := (242570267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812201638153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812201638153 / 500000000000) = 1/(500000000000 / 812201638153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (485140533 / 1000000000) (242570267 / 500000000) (Real.log (812201638153 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (812201638153 / 500000000000) = -Real.log (500000000000 / 812201638153) := by
    rw [show ((812201638153 / 500000000000) : ℝ) = ((500000000000 / 812201638153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0376

end


