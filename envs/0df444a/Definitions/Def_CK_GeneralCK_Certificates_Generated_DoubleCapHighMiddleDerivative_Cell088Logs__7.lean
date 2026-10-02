-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell088Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell088Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:10:05.294869+00:00
-- url     : https://prove2.me/theorems/3f902a61-6460-42a9-9631-e0ec607d155f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell088Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell089…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell088Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell089Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell090Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell091Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell092Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell093Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell094Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell088Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell089Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell090Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell091Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell092Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell093Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell094Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell088Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell089Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell090Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell091Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell092Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell093Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell094Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell088Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell089Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell090Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell091Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell092Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell093Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell094Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell088Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell088
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (33001943 / 125000000) ≤ -Real.log (5120 / 6667) ∧
    -Real.log (5120 / 6667) ≤ (52803109 / 200000000) := by
  have h := checkLog_sound (w := (1547 / 11787)) (n := 12)
    (lo := (33001943 / 125000000)) (hi := (52803109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6667 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6667 / 5120) = 1/(5120 / 6667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33001943 / 125000000) (52803109 / 200000000) (Real.log (6667 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6667 / 5120) = -Real.log (5120 / 6667) := by
    rw [show ((6667 / 5120) : ℝ) = ((5120 / 6667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (17987443 / 50000000) ≤ -Real.log (3573 / 5120) ∧
    -Real.log (3573 / 5120) ≤ (359748861 / 1000000000) := by
  have h := checkLog_sound (w := (1547 / 8693)) (n := 12)
    (lo := (17987443 / 50000000)) (hi := (359748861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3573) = 1/(3573 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-359748861 / 1000000000) (-17987443 / 50000000) (Real.log (3573 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (52713093 / 200000000) ≤ -Real.log (640 / 833) ∧
    -Real.log (640 / 833) ≤ (131782733 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1473)) (n := 12)
    (lo := (52713093 / 200000000)) (hi := (131782733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833 / 640) = 1/(640 / 833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (52713093 / 200000000) (131782733 / 500000000) (Real.log (833 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (833 / 640) = -Real.log (640 / 833) := by
    rw [show ((833 / 640) : ℝ) = ((640 / 833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (358909581 / 1000000000) ≤ -Real.log (447 / 640) ∧
    -Real.log (447 / 640) ≤ (179454791 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1087)) (n := 12)
    (lo := (358909581 / 1000000000)) (hi := (179454791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 447) = 1/(447 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-179454791 / 500000000) (-358909581 / 1000000000) (Real.log (447 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (193983293 / 1000000000) ≤ -Real.log (250000 / 303519) ∧
    -Real.log (250000 / 303519) ≤ (96991647 / 500000000) := by
  have h := checkLog_sound (w := (53519 / 553519)) (n := 12)
    (lo := (193983293 / 1000000000)) (hi := (96991647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303519 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303519 / 250000) = 1/(250000 / 303519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (193983293 / 1000000000) (96991647 / 500000000) (Real.log (303519 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (303519 / 250000) = -Real.log (250000 / 303519) := by
    rw [show ((303519 / 250000) : ℝ) = ((250000 / 303519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (240895183 / 1000000000) ≤ -Real.log (196481 / 250000) ∧
    -Real.log (196481 / 250000) ≤ (15055949 / 62500000) := by
  have h := checkLog_sound (w := (53519 / 446481)) (n := 12)
    (lo := (240895183 / 1000000000)) (hi := (15055949 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196481) = 1/(196481 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-15055949 / 62500000) (-240895183 / 1000000000) (Real.log (196481 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (194329999 / 1000000000) ≤ -Real.log (1000000 / 1214497) ∧
    -Real.log (1000000 / 1214497) ≤ (19433 / 100000) := by
  have h := checkLog_sound (w := (214497 / 2214497)) (n := 12)
    (lo := (194329999 / 1000000000)) (hi := (19433 / 100000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1214497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1214497 / 1000000) = 1/(1000000 / 1214497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (194329999 / 1000000000) (19433 / 100000) (Real.log (1214497 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1214497 / 1000000) = -Real.log (1000000 / 1214497) := by
    rw [show ((1214497 / 1000000) : ℝ) = ((1000000 / 1214497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (120715501 / 500000000) ≤ -Real.log (785503 / 1000000) ∧
    -Real.log (785503 / 1000000) ≤ (241431003 / 1000000000) := by
  have h := checkLog_sound (w := (214497 / 1785503)) (n := 12)
    (lo := (120715501 / 500000000)) (hi := (241431003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 785503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 785503) = 1/(785503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-241431003 / 1000000000) (-120715501 / 500000000) (Real.log (785503 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142646473 / 1000000000) ≤ -Real.log (500000 / 576661) ∧
    -Real.log (500000 / 576661) ≤ (71323237 / 500000000) := by
  have h := checkLog_sound (w := (76661 / 1076661)) (n := 12)
    (lo := (142646473 / 1000000000)) (hi := (71323237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576661 / 500000) = 1/(500000 / 576661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142646473 / 1000000000) (71323237 / 500000000) (Real.log (576661 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576661 / 500000) = -Real.log (500000 / 576661) := by
    rw [show ((576661 / 500000) : ℝ) = ((500000 / 576661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (166434821 / 1000000000) ≤ -Real.log (423339 / 500000) ∧
    -Real.log (423339 / 500000) ≤ (83217411 / 500000000) := by
  have h := checkLog_sound (w := (76661 / 923339)) (n := 12)
    (lo := (166434821 / 1000000000)) (hi := (83217411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423339) = 1/(423339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83217411 / 500000000) (-166434821 / 1000000000) (Real.log (423339 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (142914359 / 1000000000) ≤ -Real.log (1000000 / 1153631) ∧
    -Real.log (1000000 / 1153631) ≤ (3572859 / 25000000) := by
  have h := checkLog_sound (w := (153631 / 2153631)) (n := 12)
    (lo := (142914359 / 1000000000)) (hi := (3572859 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153631 / 1000000) = 1/(1000000 / 1153631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (142914359 / 1000000000) (3572859 / 25000000) (Real.log (1153631 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1153631 / 1000000) = -Real.log (1000000 / 1153631) := by
    rw [show ((1153631 / 1000000) : ℝ) = ((1000000 / 1153631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (41699961 / 250000000) ≤ -Real.log (846369 / 1000000) ∧
    -Real.log (846369 / 1000000) ≤ (33359969 / 200000000) := by
  have h := checkLog_sound (w := (153631 / 1846369)) (n := 12)
    (lo := (41699961 / 250000000)) (hi := (33359969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846369) = 1/(846369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-33359969 / 200000000) (-41699961 / 250000000) (Real.log (846369 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (622475047 / 1000000000) ≤ -Real.log (500000000000 / 931767337807) ∧
    -Real.log (500000000000 / 931767337807) ≤ (77809381 / 125000000) := by
  have h := checkLog_sound (w := (431767337807 / 1431767337807)) (n := 12)
    (lo := (622475047 / 1000000000)) (hi := (77809381 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((931767337807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(931767337807 / 500000000000) = 1/(500000000000 / 931767337807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (622475047 / 1000000000) (77809381 / 125000000) (Real.log (931767337807 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (931767337807 / 500000000000) = -Real.log (500000000000 / 931767337807) := by
    rw [show ((931767337807 / 500000000000) : ℝ) = ((500000000000 / 931767337807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (155941101 / 250000000) ≤ -Real.log (500000000000 / 932969493423) ∧
    -Real.log (500000000000 / 932969493423) ≤ (124752881 / 200000000) := by
  have h := checkLog_sound (w := (432969493423 / 1432969493423)) (n := 12)
    (lo := (155941101 / 250000000)) (hi := (124752881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((932969493423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(932969493423 / 500000000000) = 1/(500000000000 / 932969493423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (155941101 / 250000000) (124752881 / 200000000) (Real.log (932969493423 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (932969493423 / 500000000000) = -Real.log (500000000000 / 932969493423) := by
    rw [show ((932969493423 / 500000000000) : ℝ) = ((500000000000 / 932969493423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (108719619 / 250000000) ≤ -Real.log (500000000000 / 772387660893) ∧
    -Real.log (500000000000 / 772387660893) ≤ (434878477 / 1000000000) := by
  have h := checkLog_sound (w := (272387660893 / 1272387660893)) (n := 12)
    (lo := (108719619 / 250000000)) (hi := (434878477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772387660893 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772387660893 / 500000000000) = 1/(500000000000 / 772387660893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108719619 / 250000000) (434878477 / 1000000000) (Real.log (772387660893 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (772387660893 / 500000000000) = -Real.log (500000000000 / 772387660893) := by
    rw [show ((772387660893 / 500000000000) : ℝ) = ((500000000000 / 772387660893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (435761001 / 1000000000) ≤ -Real.log (6250000000 / 9663370159) ∧
    -Real.log (6250000000 / 9663370159) ≤ (217880501 / 500000000) := by
  have h := checkLog_sound (w := (3413370159 / 15913370159)) (n := 12)
    (lo := (435761001 / 1000000000)) (hi := (217880501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9663370159 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9663370159 / 6250000000) = 1/(6250000000 / 9663370159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (435761001 / 1000000000) (217880501 / 500000000) (Real.log (9663370159 / 6250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (9663370159 / 6250000000) = -Real.log (6250000000 / 9663370159) := by
    rw [show ((9663370159 / 6250000000) : ℝ) = ((6250000000 / 9663370159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (61816259 / 200000000) ≤ -Real.log (7812500000 / 10641977381) ∧
    -Real.log (7812500000 / 10641977381) ≤ (19317581 / 62500000) := by
  have h := checkLog_sound (w := (2829477381 / 18454477381)) (n := 12)
    (lo := (61816259 / 200000000)) (hi := (19317581 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10641977381 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10641977381 / 7812500000) = 1/(7812500000 / 10641977381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (61816259 / 200000000) (19317581 / 62500000) (Real.log (10641977381 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10641977381 / 7812500000) = -Real.log (7812500000 / 10641977381) := by
    rw [show ((10641977381 / 7812500000) : ℝ) = ((7812500000 / 10641977381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (309714203 / 1000000000) ≤ -Real.log (500000000000 / 681517754077) ∧
    -Real.log (500000000000 / 681517754077) ≤ (77428551 / 250000000) := by
  have h := checkLog_sound (w := (181517754077 / 1181517754077)) (n := 12)
    (lo := (309714203 / 1000000000)) (hi := (77428551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681517754077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681517754077 / 500000000000) = 1/(500000000000 / 681517754077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (309714203 / 1000000000) (77428551 / 250000000) (Real.log (681517754077 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (681517754077 / 500000000000) = -Real.log (500000000000 / 681517754077) := by
    rw [show ((681517754077 / 500000000000) : ℝ) = ((500000000000 / 681517754077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5971371 / 250000000) ≤ -Real.log (976397515839 / 1000000000000) ∧
    -Real.log (976397515839 / 1000000000000) ≤ (4777097 / 200000000) := by
  have h := checkLog_sound (w := (23602484161 / 1976397515839)) (n := 12)
    (lo := (5971371 / 250000000)) (hi := (4777097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976397515839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976397515839) = 1/(976397515839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4777097 / 200000000) (-5971371 / 250000000) (Real.log (976397515839 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5947087 / 250000000) ≤ -Real.log (244123091079 / 250000000000) ∧
    -Real.log (244123091079 / 250000000000) ≤ (23788349 / 1000000000) := by
  have h := checkLog_sound (w := (5876908921 / 494123091079)) (n := 12)
    (lo := (5947087 / 250000000)) (hi := (23788349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244123091079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244123091079) = 1/(244123091079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-23788349 / 1000000000) (-5947087 / 250000000) (Real.log (244123091079 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell088

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell089Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell089
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (13223271 / 50000000) ≤ -Real.log (512 / 667) ∧
    -Real.log (512 / 667) ≤ (264465421 / 1000000000) := by
  have h := checkLog_sound (w := (155 / 1179)) (n := 12)
    (lo := (13223271 / 50000000)) (hi := (264465421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667 / 512) = 1/(512 / 667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13223271 / 50000000) (264465421 / 1000000000) (Real.log (667 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (667 / 512) = -Real.log (512 / 667) := by
    rw [show ((667 / 512) : ℝ) = ((512 / 667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (360588843 / 1000000000) ≤ -Real.log (357 / 512) ∧
    -Real.log (357 / 512) ≤ (90147211 / 250000000) := by
  have h := checkLog_sound (w := (155 / 869)) (n := 12)
    (lo := (360588843 / 1000000000)) (hi := (90147211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 357) = 1/(357 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-90147211 / 250000000) (-360588843 / 1000000000) (Real.log (357 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33001943 / 125000000) ≤ -Real.log (5120 / 6667) ∧
    -Real.log (5120 / 6667) ≤ (52803109 / 200000000) := by
  have h := checkLog_sound (w := (1547 / 11787)) (n := 12)
    (lo := (33001943 / 125000000)) (hi := (52803109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6667 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6667 / 5120) = 1/(5120 / 6667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33001943 / 125000000) (52803109 / 200000000) (Real.log (6667 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6667 / 5120) = -Real.log (5120 / 6667) := by
    rw [show ((6667 / 5120) : ℝ) = ((5120 / 6667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (17987443 / 50000000) ≤ -Real.log (3573 / 5120) ∧
    -Real.log (3573 / 5120) ≤ (359748861 / 1000000000) := by
  have h := checkLog_sound (w := (1547 / 8693)) (n := 12)
    (lo := (17987443 / 50000000)) (hi := (359748861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3573) = 1/(3573 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-359748861 / 1000000000) (-17987443 / 50000000) (Real.log (3573 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7773167 / 40000000) ≤ -Real.log (31250 / 37953) ∧
    -Real.log (31250 / 37953) ≤ (24291147 / 125000000) := by
  have h := checkLog_sound (w := (6703 / 69203)) (n := 12)
    (lo := (7773167 / 40000000)) (hi := (24291147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37953 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37953 / 31250) = 1/(31250 / 37953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7773167 / 40000000) (24291147 / 125000000) (Real.log (37953 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37953 / 31250) = -Real.log (31250 / 37953) := by
    rw [show ((37953 / 31250) : ℝ) = ((31250 / 37953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (241429729 / 1000000000) ≤ -Real.log (24547 / 31250) ∧
    -Real.log (24547 / 31250) ≤ (24142973 / 100000000) := by
  have h := checkLog_sound (w := (6703 / 55797)) (n := 12)
    (lo := (241429729 / 1000000000)) (hi := (24142973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24547) = 1/(24547 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-24142973 / 100000000) (-241429729 / 1000000000) (Real.log (24547 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97337469 / 500000000) ≤ -Real.log (250000 / 303729) ∧
    -Real.log (250000 / 303729) ≤ (194674939 / 1000000000) := by
  have h := checkLog_sound (w := (53729 / 553729)) (n := 12)
    (lo := (97337469 / 500000000)) (hi := (194674939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303729 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303729 / 250000) = 1/(250000 / 303729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97337469 / 500000000) (194674939 / 1000000000) (Real.log (303729 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (303729 / 250000) = -Real.log (250000 / 303729) := by
    rw [show ((303729 / 250000) : ℝ) = ((250000 / 303729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3024557 / 12500000) ≤ -Real.log (196271 / 250000) ∧
    -Real.log (196271 / 250000) ≤ (241964561 / 1000000000) := by
  have h := checkLog_sound (w := (53729 / 446271)) (n := 12)
    (lo := (3024557 / 12500000)) (hi := (241964561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196271) = 1/(196271 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-241964561 / 1000000000) (-3024557 / 12500000) (Real.log (196271 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35728373 / 250000000) ≤ -Real.log (100000 / 115363) ∧
    -Real.log (100000 / 115363) ≤ (142913493 / 1000000000) := by
  have h := checkLog_sound (w := (15363 / 215363)) (n := 12)
    (lo := (35728373 / 250000000)) (hi := (142913493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115363 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115363 / 100000) = 1/(100000 / 115363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35728373 / 250000000) (142913493 / 1000000000) (Real.log (115363 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (115363 / 100000) = -Real.log (100000 / 115363) := by
    rw [show ((115363 / 100000) : ℝ) = ((100000 / 115363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (83399331 / 500000000) ≤ -Real.log (84637 / 100000) ∧
    -Real.log (84637 / 100000) ≤ (166798663 / 1000000000) := by
  have h := checkLog_sound (w := (15363 / 184637)) (n := 12)
    (lo := (83399331 / 500000000)) (hi := (166798663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 84637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 84637) = 1/(84637 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-166798663 / 1000000000) (-83399331 / 500000000) (Real.log (84637 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (143181307 / 1000000000) ≤ -Real.log (1000000 / 1153939) ∧
    -Real.log (1000000 / 1153939) ≤ (35795327 / 250000000) := by
  have h := checkLog_sound (w := (153939 / 2153939)) (n := 12)
    (lo := (143181307 / 1000000000)) (hi := (35795327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153939 / 1000000) = 1/(1000000 / 1153939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (143181307 / 1000000000) (35795327 / 250000000) (Real.log (1153939 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1153939 / 1000000) = -Real.log (1000000 / 1153939) := by
    rw [show ((1153939 / 1000000) : ℝ) = ((1000000 / 1153939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (167163817 / 1000000000) ≤ -Real.log (846061 / 1000000) ∧
    -Real.log (846061 / 1000000) ≤ (83581909 / 500000000) := by
  have h := checkLog_sound (w := (153939 / 1846061)) (n := 12)
    (lo := (167163817 / 1000000000)) (hi := (83581909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846061) = 1/(846061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-83581909 / 500000000) (-167163817 / 1000000000) (Real.log (846061 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (155941101 / 250000000) ≤ -Real.log (250000000000 / 466484746711) ∧
    -Real.log (250000000000 / 466484746711) ≤ (124752881 / 200000000) := by
  have h := checkLog_sound (w := (216484746711 / 716484746711)) (n := 12)
    (lo := (155941101 / 250000000)) (hi := (124752881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((466484746711 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(466484746711 / 250000000000) = 1/(250000000000 / 466484746711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (155941101 / 250000000) (124752881 / 200000000) (Real.log (466484746711 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (466484746711 / 250000000000) = -Real.log (250000000000 / 466484746711) := by
    rw [show ((466484746711 / 250000000000) : ℝ) = ((250000000000 / 466484746711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (78131783 / 125000000) ≤ -Real.log (125000000000 / 233543417367) ∧
    -Real.log (125000000000 / 233543417367) ≤ (125010853 / 200000000) := by
  have h := checkLog_sound (w := (108543417367 / 358543417367)) (n := 12)
    (lo := (78131783 / 125000000)) (hi := (125010853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233543417367 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233543417367 / 125000000000) = 1/(125000000000 / 233543417367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (78131783 / 125000000) (125010853 / 200000000) (Real.log (233543417367 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (233543417367 / 125000000000) = -Real.log (125000000000 / 233543417367) := by
    rw [show ((233543417367 / 125000000000) : ℝ) = ((125000000000 / 233543417367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (54469863 / 125000000) ≤ -Real.log (100000000000 / 154613598403) ∧
    -Real.log (100000000000 / 154613598403) ≤ (87151781 / 200000000) := by
  have h := checkLog_sound (w := (54613598403 / 254613598403)) (n := 12)
    (lo := (54469863 / 125000000)) (hi := (87151781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154613598403 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154613598403 / 100000000000) = 1/(100000000000 / 154613598403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54469863 / 125000000) (87151781 / 200000000) (Real.log (154613598403 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (154613598403 / 100000000000) = -Real.log (100000000000 / 154613598403) := by
    rw [show ((154613598403 / 100000000000) : ℝ) = ((100000000000 / 154613598403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (436639499 / 1000000000) ≤ -Real.log (500000000000 / 773749051057) ∧
    -Real.log (500000000000 / 773749051057) ≤ (873279 / 2000000) := by
  have h := checkLog_sound (w := (273749051057 / 1273749051057)) (n := 12)
    (lo := (436639499 / 1000000000)) (hi := (873279 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773749051057 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773749051057 / 500000000000) = 1/(500000000000 / 773749051057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (436639499 / 1000000000) (873279 / 2000000) (Real.log (773749051057 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (773749051057 / 500000000000) = -Real.log (500000000000 / 773749051057) := by
    rw [show ((773749051057 / 500000000000) : ℝ) = ((500000000000 / 773749051057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (61942431 / 200000000) ≤ -Real.log (500000000000 / 681516358093) ∧
    -Real.log (500000000000 / 681516358093) ≤ (77428039 / 250000000) := by
  have h := checkLog_sound (w := (181516358093 / 1181516358093)) (n := 12)
    (lo := (61942431 / 200000000)) (hi := (77428039 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681516358093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681516358093 / 500000000000) = 1/(500000000000 / 681516358093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (61942431 / 200000000) (77428039 / 250000000) (Real.log (681516358093 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (681516358093 / 500000000000) = -Real.log (500000000000 / 681516358093) := by
    rw [show ((681516358093 / 500000000000) : ℝ) = ((500000000000 / 681516358093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2482761 / 8000000) ≤ -Real.log (100000000000 / 136389574747) ∧
    -Real.log (100000000000 / 136389574747) ≤ (155172563 / 500000000) := by
  have h := checkLog_sound (w := (36389574747 / 236389574747)) (n := 12)
    (lo := (2482761 / 8000000)) (hi := (155172563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136389574747 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136389574747 / 100000000000) = 1/(100000000000 / 136389574747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2482761 / 8000000) (155172563 / 500000000) (Real.log (136389574747 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (136389574747 / 100000000000) = -Real.log (100000000000 / 136389574747) := by
    rw [show ((136389574747 / 100000000000) : ℝ) = ((100000000000 / 136389574747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2398251 / 100000000) ≤ -Real.log (976302784279 / 1000000000000) ∧
    -Real.log (976302784279 / 1000000000000) ≤ (23982511 / 1000000000) := by
  have h := checkLog_sound (w := (23697215721 / 1976302784279)) (n := 12)
    (lo := (2398251 / 100000000)) (hi := (23982511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976302784279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976302784279) = 1/(976302784279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23982511 / 1000000000) (-2398251 / 100000000) (Real.log (976302784279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (23885169 / 1000000000) ≤ -Real.log (9763978231 / 10000000000) ∧
    -Real.log (9763978231 / 10000000000) ≤ (2388517 / 100000000) := by
  have h := checkLog_sound (w := (236021769 / 19763978231)) (n := 12)
    (lo := (23885169 / 1000000000)) (hi := (2388517 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9763978231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9763978231) = 1/(9763978231 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2388517 / 100000000) (-23885169 / 1000000000) (Real.log (9763978231 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell089

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell090Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell090
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (132457547 / 500000000) ≤ -Real.log (5120 / 6673) ∧
    -Real.log (5120 / 6673) ≤ (52983019 / 200000000) := by
  have h := checkLog_sound (w := (1553 / 11793)) (n := 12)
    (lo := (132457547 / 500000000)) (hi := (52983019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6673 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6673 / 5120) = 1/(5120 / 6673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132457547 / 500000000) (52983019 / 200000000) (Real.log (6673 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6673 / 5120) = -Real.log (5120 / 6673) := by
    rw [show ((6673 / 5120) : ℝ) = ((5120 / 6673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (90357383 / 250000000) ≤ -Real.log (3567 / 5120) ∧
    -Real.log (3567 / 5120) ≤ (361429533 / 1000000000) := by
  have h := checkLog_sound (w := (1553 / 8687)) (n := 12)
    (lo := (90357383 / 250000000)) (hi := (361429533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3567) = 1/(3567 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-361429533 / 1000000000) (-90357383 / 250000000) (Real.log (3567 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13223271 / 50000000) ≤ -Real.log (512 / 667) ∧
    -Real.log (512 / 667) ≤ (264465421 / 1000000000) := by
  have h := checkLog_sound (w := (155 / 1179)) (n := 12)
    (lo := (13223271 / 50000000)) (hi := (264465421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667 / 512) = 1/(512 / 667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13223271 / 50000000) (264465421 / 1000000000) (Real.log (667 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (667 / 512) = -Real.log (512 / 667) := by
    rw [show ((667 / 512) : ℝ) = ((512 / 667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (360588843 / 1000000000) ≤ -Real.log (357 / 512) ∧
    -Real.log (357 / 512) ≤ (90147211 / 250000000) := by
  have h := checkLog_sound (w := (155 / 869)) (n := 12)
    (lo := (360588843 / 1000000000)) (hi := (90147211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 357) = 1/(357 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-90147211 / 250000000) (-360588843 / 1000000000) (Real.log (357 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38934823 / 200000000) ≤ -Real.log (200000 / 242983) ∧
    -Real.log (200000 / 242983) ≤ (48668529 / 250000000) := by
  have h := checkLog_sound (w := (42983 / 442983)) (n := 12)
    (lo := (38934823 / 200000000)) (hi := (48668529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242983 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242983 / 200000) = 1/(200000 / 242983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38934823 / 200000000) (48668529 / 250000000) (Real.log (242983 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (242983 / 200000) = -Real.log (200000 / 242983) := by
    rw [show ((242983 / 200000) : ℝ) = ((200000 / 242983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (120981643 / 500000000) ≤ -Real.log (157017 / 200000) ∧
    -Real.log (157017 / 200000) ≤ (241963287 / 1000000000) := by
  have h := checkLog_sound (w := (42983 / 357017)) (n := 12)
    (lo := (120981643 / 500000000)) (hi := (241963287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157017) = 1/(157017 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-241963287 / 1000000000) (-120981643 / 500000000) (Real.log (157017 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (195020581 / 1000000000) ≤ -Real.log (125000 / 151917) ∧
    -Real.log (125000 / 151917) ≤ (97510291 / 500000000) := by
  have h := checkLog_sound (w := (26917 / 276917)) (n := 12)
    (lo := (195020581 / 1000000000)) (hi := (97510291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151917 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151917 / 125000) = 1/(125000 / 151917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (195020581 / 1000000000) (97510291 / 500000000) (Real.log (151917 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (151917 / 125000) = -Real.log (125000 / 151917) := by
    rw [show ((151917 / 125000) : ℝ) = ((125000 / 151917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (121249839 / 500000000) ≤ -Real.log (98083 / 125000) ∧
    -Real.log (98083 / 125000) ≤ (242499679 / 1000000000) := by
  have h := checkLog_sound (w := (26917 / 223083)) (n := 12)
    (lo := (121249839 / 500000000)) (hi := (242499679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98083) = 1/(98083 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-242499679 / 1000000000) (-121249839 / 500000000) (Real.log (98083 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (3579511 / 25000000) ≤ -Real.log (500000 / 576969) ∧
    -Real.log (500000 / 576969) ≤ (143180441 / 1000000000) := by
  have h := checkLog_sound (w := (76969 / 1076969)) (n := 12)
    (lo := (3579511 / 25000000)) (hi := (143180441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576969 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576969 / 500000) = 1/(500000 / 576969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (3579511 / 25000000) (143180441 / 1000000000) (Real.log (576969 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576969 / 500000) = -Real.log (500000 / 576969) := by
    rw [show ((576969 / 500000) : ℝ) = ((500000 / 576969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41790659 / 250000000) ≤ -Real.log (423031 / 500000) ∧
    -Real.log (423031 / 500000) ≤ (167162637 / 1000000000) := by
  have h := checkLog_sound (w := (76969 / 923031)) (n := 12)
    (lo := (41790659 / 250000000)) (hi := (167162637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423031) = 1/(423031 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-167162637 / 1000000000) (-41790659 / 250000000) (Real.log (423031 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (143448183 / 1000000000) ≤ -Real.log (1000000 / 1154247) ∧
    -Real.log (1000000 / 1154247) ≤ (17931023 / 125000000) := by
  have h := checkLog_sound (w := (154247 / 2154247)) (n := 12)
    (lo := (143448183 / 1000000000)) (hi := (17931023 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1154247 / 1000000) = 1/(1000000 / 1154247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (143448183 / 1000000000) (17931023 / 125000000) (Real.log (1154247 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1154247 / 1000000) = -Real.log (1000000 / 1154247) := by
    rw [show ((1154247 / 1000000) : ℝ) = ((1000000 / 1154247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (41881981 / 250000000) ≤ -Real.log (845753 / 1000000) ∧
    -Real.log (845753 / 1000000) ≤ (6701117 / 40000000) := by
  have h := checkLog_sound (w := (154247 / 1845753)) (n := 12)
    (lo := (41881981 / 250000000)) (hi := (6701117 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 845753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 845753) = 1/(845753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6701117 / 40000000) (-41881981 / 250000000) (Real.log (845753 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (78131783 / 125000000) ≤ -Real.log (500000000000 / 934173669467) ∧
    -Real.log (500000000000 / 934173669467) ≤ (125010853 / 200000000) := by
  have h := checkLog_sound (w := (434173669467 / 1434173669467)) (n := 12)
    (lo := (78131783 / 125000000)) (hi := (125010853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((934173669467 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(934173669467 / 500000000000) = 1/(500000000000 / 934173669467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (78131783 / 125000000) (125010853 / 200000000) (Real.log (934173669467 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (934173669467 / 500000000000) = -Real.log (500000000000 / 934173669467) := by
    rw [show ((934173669467 / 500000000000) : ℝ) = ((500000000000 / 934173669467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (626344627 / 1000000000) ≤ -Real.log (500000000000 / 935379871041) ∧
    -Real.log (500000000000 / 935379871041) ≤ (156586157 / 250000000) := by
  have h := checkLog_sound (w := (435379871041 / 1435379871041)) (n := 12)
    (lo := (626344627 / 1000000000)) (hi := (156586157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935379871041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935379871041 / 500000000000) = 1/(500000000000 / 935379871041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (626344627 / 1000000000) (156586157 / 250000000) (Real.log (935379871041 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (935379871041 / 500000000000) = -Real.log (500000000000 / 935379871041) := by
    rw [show ((935379871041 / 500000000000) : ℝ) = ((500000000000 / 935379871041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (218318701 / 500000000) ≤ -Real.log (250000000000 / 386873714311) ∧
    -Real.log (250000000000 / 386873714311) ≤ (436637403 / 1000000000) := by
  have h := checkLog_sound (w := (136873714311 / 636873714311)) (n := 12)
    (lo := (218318701 / 500000000)) (hi := (436637403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386873714311 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386873714311 / 250000000000) = 1/(250000000000 / 386873714311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (218318701 / 500000000) (436637403 / 1000000000) (Real.log (386873714311 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (386873714311 / 250000000000) = -Real.log (250000000000 / 386873714311) := by
    rw [show ((386873714311 / 250000000000) : ℝ) = ((250000000000 / 386873714311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (21876013 / 50000000) ≤ -Real.log (125000000000 / 193607709797) ∧
    -Real.log (125000000000 / 193607709797) ≤ (437520261 / 1000000000) := by
  have h := checkLog_sound (w := (68607709797 / 318607709797)) (n := 12)
    (lo := (21876013 / 50000000)) (hi := (437520261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193607709797 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193607709797 / 125000000000) = 1/(125000000000 / 193607709797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (21876013 / 50000000) (437520261 / 1000000000) (Real.log (193607709797 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (193607709797 / 125000000000) = -Real.log (125000000000 / 193607709797) := by
    rw [show ((193607709797 / 125000000000) : ℝ) = ((125000000000 / 193607709797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (77585769 / 250000000) ≤ -Real.log (100000000000 / 136389295347) ∧
    -Real.log (100000000000 / 136389295347) ≤ (310343077 / 1000000000) := by
  have h := checkLog_sound (w := (36389295347 / 236389295347)) (n := 12)
    (lo := (77585769 / 250000000)) (hi := (310343077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136389295347 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136389295347 / 100000000000) = 1/(100000000000 / 136389295347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (77585769 / 250000000) (310343077 / 1000000000) (Real.log (136389295347 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (136389295347 / 100000000000) = -Real.log (100000000000 / 136389295347) := by
    rw [show ((136389295347 / 100000000000) : ℝ) = ((100000000000 / 136389295347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (310976107 / 1000000000) ≤ -Real.log (500000000000 / 682378306669) ∧
    -Real.log (500000000000 / 682378306669) ≤ (77744027 / 250000000) := by
  have h := checkLog_sound (w := (182378306669 / 1182378306669)) (n := 12)
    (lo := (310976107 / 1000000000)) (hi := (77744027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682378306669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682378306669 / 500000000000) = 1/(500000000000 / 682378306669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (310976107 / 1000000000) (77744027 / 250000000) (Real.log (682378306669 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (682378306669 / 500000000000) = -Real.log (500000000000 / 682378306669) := by
    rw [show ((682378306669 / 500000000000) : ℝ) = ((500000000000 / 682378306669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1203987 / 50000000) ≤ -Real.log (976207862991 / 1000000000000) ∧
    -Real.log (976207862991 / 1000000000000) ≤ (24079741 / 1000000000) := by
  have h := checkLog_sound (w := (23792137009 / 1976207862991)) (n := 12)
    (lo := (1203987 / 50000000)) (hi := (24079741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976207862991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976207862991) = 1/(976207862991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-24079741 / 1000000000) (-1203987 / 50000000) (Real.log (976207862991 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4796439 / 200000000) ≤ -Real.log (244075773039 / 250000000000) ∧
    -Real.log (244075773039 / 250000000000) ≤ (5995549 / 250000000) := by
  have h := checkLog_sound (w := (5924226961 / 494075773039)) (n := 12)
    (lo := (4796439 / 200000000)) (hi := (5995549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244075773039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244075773039) = 1/(244075773039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5995549 / 250000000) (-4796439 / 200000000) (Real.log (244075773039 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell090

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell091Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell091
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (132682283 / 500000000) ≤ -Real.log (1280 / 1669) ∧
    -Real.log (1280 / 1669) ≤ (265364567 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 2949)) (n := 12)
    (lo := (132682283 / 500000000)) (hi := (265364567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1669 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1669 / 1280) = 1/(1280 / 1669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132682283 / 500000000) (265364567 / 1000000000) (Real.log (1669 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1669 / 1280) = -Real.log (1280 / 1669) := by
    rw [show ((1669 / 1280) : ℝ) = ((1280 / 1669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (362270929 / 1000000000) ≤ -Real.log (891 / 1280) ∧
    -Real.log (891 / 1280) ≤ (36227093 / 100000000) := by
  have h := checkLog_sound (w := (389 / 2171)) (n := 12)
    (lo := (362270929 / 1000000000)) (hi := (36227093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 891) = 1/(891 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-36227093 / 100000000) (-362270929 / 1000000000) (Real.log (891 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132457547 / 500000000) ≤ -Real.log (5120 / 6673) ∧
    -Real.log (5120 / 6673) ≤ (52983019 / 200000000) := by
  have h := checkLog_sound (w := (1553 / 11793)) (n := 12)
    (lo := (132457547 / 500000000)) (hi := (52983019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6673 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6673 / 5120) = 1/(5120 / 6673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132457547 / 500000000) (52983019 / 200000000) (Real.log (6673 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6673 / 5120) = -Real.log (5120 / 6673) := by
    rw [show ((6673 / 5120) : ℝ) = ((5120 / 6673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (90357383 / 250000000) ≤ -Real.log (3567 / 5120) ∧
    -Real.log (3567 / 5120) ≤ (361429533 / 1000000000) := by
  have h := checkLog_sound (w := (1553 / 8687)) (n := 12)
    (lo := (90357383 / 250000000)) (hi := (361429533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3567) = 1/(3567 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-361429533 / 1000000000) (-90357383 / 250000000) (Real.log (3567 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24377367 / 125000000) ≤ -Real.log (500000 / 607667) ∧
    -Real.log (500000 / 607667) ≤ (195018937 / 1000000000) := by
  have h := checkLog_sound (w := (107667 / 1107667)) (n := 12)
    (lo := (24377367 / 125000000)) (hi := (195018937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607667 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607667 / 500000) = 1/(500000 / 607667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24377367 / 125000000) (195018937 / 1000000000) (Real.log (607667 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (607667 / 500000) = -Real.log (500000 / 607667) := by
    rw [show ((607667 / 500000) : ℝ) = ((500000 / 607667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (242497129 / 1000000000) ≤ -Real.log (392333 / 500000) ∧
    -Real.log (392333 / 500000) ≤ (24249713 / 100000000) := by
  have h := checkLog_sound (w := (107667 / 892333)) (n := 12)
    (lo := (242497129 / 1000000000)) (hi := (24249713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392333) = 1/(392333 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-24249713 / 100000000) (-242497129 / 1000000000) (Real.log (392333 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97682641 / 500000000) ≤ -Real.log (200000 / 243151) ∧
    -Real.log (200000 / 243151) ≤ (195365283 / 1000000000) := by
  have h := checkLog_sound (w := (43151 / 443151)) (n := 12)
    (lo := (97682641 / 500000000)) (hi := (195365283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243151 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243151 / 200000) = 1/(200000 / 243151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97682641 / 500000000) (195365283 / 1000000000) (Real.log (243151 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (243151 / 200000) = -Real.log (200000 / 243151) := by
    rw [show ((243151 / 200000) : ℝ) = ((200000 / 243151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (243033807 / 1000000000) ≤ -Real.log (156849 / 200000) ∧
    -Real.log (156849 / 200000) ≤ (15189613 / 62500000) := by
  have h := checkLog_sound (w := (43151 / 356849)) (n := 12)
    (lo := (243033807 / 1000000000)) (hi := (15189613 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 156849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 156849) = 1/(156849 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-15189613 / 62500000) (-243033807 / 1000000000) (Real.log (156849 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35861829 / 250000000) ≤ -Real.log (500000 / 577123) ∧
    -Real.log (500000 / 577123) ≤ (143447317 / 1000000000) := by
  have h := checkLog_sound (w := (77123 / 1077123)) (n := 12)
    (lo := (35861829 / 250000000)) (hi := (143447317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577123 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577123 / 500000) = 1/(500000 / 577123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35861829 / 250000000) (143447317 / 1000000000) (Real.log (577123 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (577123 / 500000) = -Real.log (500000 / 577123) := by
    rw [show ((577123 / 500000) : ℝ) = ((500000 / 577123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (167526741 / 1000000000) ≤ -Real.log (422877 / 500000) ∧
    -Real.log (422877 / 500000) ≤ (83763371 / 500000000) := by
  have h := checkLog_sound (w := (77123 / 922877)) (n := 12)
    (lo := (167526741 / 1000000000)) (hi := (83763371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 422877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 422877) = 1/(422877 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83763371 / 500000000) (-167526741 / 1000000000) (Real.log (422877 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (71857927 / 500000000) ≤ -Real.log (250000 / 288639) ∧
    -Real.log (250000 / 288639) ≤ (28743171 / 200000000) := by
  have h := checkLog_sound (w := (38639 / 538639)) (n := 12)
    (lo := (71857927 / 500000000)) (hi := (28743171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288639 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288639 / 250000) = 1/(250000 / 288639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (71857927 / 500000000) (28743171 / 200000000) (Real.log (288639 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (288639 / 250000) = -Real.log (250000 / 288639) := by
    rw [show ((288639 / 250000) : ℝ) = ((250000 / 288639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (33578669 / 200000000) ≤ -Real.log (211361 / 250000) ∧
    -Real.log (211361 / 250000) ≤ (83946673 / 500000000) := by
  have h := checkLog_sound (w := (38639 / 461361)) (n := 12)
    (lo := (33578669 / 200000000)) (hi := (83946673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211361) = 1/(211361 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-83946673 / 500000000) (-33578669 / 200000000) (Real.log (211361 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (626344627 / 1000000000) ≤ -Real.log (1562500000 / 2923062097) ∧
    -Real.log (1562500000 / 2923062097) ≤ (156586157 / 250000000) := by
  have h := checkLog_sound (w := (1360562097 / 4485562097)) (n := 12)
    (lo := (626344627 / 1000000000)) (hi := (156586157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2923062097 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2923062097 / 1562500000) = 1/(1562500000 / 2923062097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (626344627 / 1000000000) (156586157 / 250000000) (Real.log (2923062097 / 1562500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (2923062097 / 1562500000) = -Real.log (1562500000 / 2923062097) := by
    rw [show ((2923062097 / 1562500000) : ℝ) = ((1562500000 / 2923062097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (78454437 / 125000000) ≤ -Real.log (100000000000 / 187317620651) ∧
    -Real.log (100000000000 / 187317620651) ≤ (627635497 / 1000000000) := by
  have h := checkLog_sound (w := (87317620651 / 287317620651)) (n := 12)
    (lo := (78454437 / 125000000)) (hi := (627635497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187317620651 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187317620651 / 100000000000) = 1/(100000000000 / 187317620651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (78454437 / 125000000) (627635497 / 1000000000) (Real.log (187317620651 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (187317620651 / 100000000000) = -Real.log (100000000000 / 187317620651) := by
    rw [show ((187317620651 / 100000000000) : ℝ) = ((100000000000 / 187317620651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (87503213 / 200000000) ≤ -Real.log (500000000000 / 774427590847) ∧
    -Real.log (500000000000 / 774427590847) ≤ (218758033 / 500000000) := by
  have h := checkLog_sound (w := (274427590847 / 1274427590847)) (n := 12)
    (lo := (87503213 / 200000000)) (hi := (218758033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774427590847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774427590847 / 500000000000) = 1/(500000000000 / 774427590847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (87503213 / 200000000) (218758033 / 500000000) (Real.log (774427590847 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (774427590847 / 500000000000) = -Real.log (500000000000 / 774427590847) := by
    rw [show ((774427590847 / 500000000000) : ℝ) = ((500000000000 / 774427590847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (43839909 / 100000000) ≤ -Real.log (250000000000 / 387555865833) ∧
    -Real.log (250000000000 / 387555865833) ≤ (438399091 / 1000000000) := by
  have h := checkLog_sound (w := (137555865833 / 637555865833)) (n := 12)
    (lo := (43839909 / 100000000)) (hi := (438399091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387555865833 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387555865833 / 250000000000) = 1/(250000000000 / 387555865833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (43839909 / 100000000) (438399091 / 1000000000) (Real.log (387555865833 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (387555865833 / 250000000000) = -Real.log (250000000000 / 387555865833) := by
    rw [show ((387555865833 / 250000000000) : ℝ) = ((250000000000 / 387555865833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (155487029 / 500000000) ≤ -Real.log (500000000000 / 682376908651) ∧
    -Real.log (500000000000 / 682376908651) ≤ (310974059 / 1000000000) := by
  have h := checkLog_sound (w := (182376908651 / 1182376908651)) (n := 12)
    (lo := (155487029 / 500000000)) (hi := (310974059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682376908651 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682376908651 / 500000000000) = 1/(500000000000 / 682376908651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (155487029 / 500000000) (310974059 / 1000000000) (Real.log (682376908651 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (682376908651 / 500000000000) = -Real.log (500000000000 / 682376908651) := by
    rw [show ((682376908651 / 500000000000) : ℝ) = ((500000000000 / 682376908651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (779023 / 2500000) ≤ -Real.log (25000000000 / 34140522613) ∧
    -Real.log (25000000000 / 34140522613) ≤ (311609201 / 1000000000) := by
  have h := checkLog_sound (w := (9140522613 / 59140522613)) (n := 12)
    (lo := (779023 / 2500000)) (hi := (311609201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34140522613 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34140522613 / 25000000000) = 1/(25000000000 / 34140522613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (779023 / 2500000) (311609201 / 1000000000) (Real.log (34140522613 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (34140522613 / 25000000000) = -Real.log (25000000000 / 34140522613) := by
    rw [show ((34140522613 / 25000000000) : ℝ) = ((25000000000 / 34140522613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24177491 / 1000000000) ≤ -Real.log (61007027679 / 62500000000) ∧
    -Real.log (61007027679 / 62500000000) ≤ (6044373 / 250000000) := by
  have h := checkLog_sound (w := (1492972321 / 123507027679)) (n := 12)
    (lo := (24177491 / 1000000000)) (hi := (6044373 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61007027679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61007027679) = 1/(61007027679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6044373 / 250000000) (-24177491 / 1000000000) (Real.log (61007027679 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (376241 / 15625000) ≤ -Real.log (244052042871 / 250000000000) ∧
    -Real.log (244052042871 / 250000000000) ≤ (963177 / 40000000) := by
  have h := checkLog_sound (w := (5947957129 / 494052042871)) (n := 12)
    (lo := (376241 / 15625000)) (hi := (963177 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244052042871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244052042871) = 1/(244052042871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-963177 / 40000000) (-376241 / 15625000) (Real.log (244052042871 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell091

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell092Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell092
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (66453459 / 250000000) ≤ -Real.log (5120 / 6679) ∧
    -Real.log (5120 / 6679) ≤ (265813837 / 1000000000) := by
  have h := checkLog_sound (w := (1559 / 11799)) (n := 12)
    (lo := (66453459 / 250000000)) (hi := (265813837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6679 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6679 / 5120) = 1/(5120 / 6679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66453459 / 250000000) (265813837 / 1000000000) (Real.log (6679 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6679 / 5120) = -Real.log (5120 / 6679) := by
    rw [show ((6679 / 5120) : ℝ) = ((5120 / 6679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (181556517 / 500000000) ≤ -Real.log (3561 / 5120) ∧
    -Real.log (3561 / 5120) ≤ (72622607 / 200000000) := by
  have h := checkLog_sound (w := (1559 / 8681)) (n := 12)
    (lo := (181556517 / 500000000)) (hi := (72622607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3561) = 1/(3561 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-72622607 / 200000000) (-181556517 / 500000000) (Real.log (3561 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132682283 / 500000000) ≤ -Real.log (1280 / 1669) ∧
    -Real.log (1280 / 1669) ≤ (265364567 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 2949)) (n := 12)
    (lo := (132682283 / 500000000)) (hi := (265364567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1669 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1669 / 1280) = 1/(1280 / 1669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132682283 / 500000000) (265364567 / 1000000000) (Real.log (1669 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1669 / 1280) = -Real.log (1280 / 1669) := by
    rw [show ((1669 / 1280) : ℝ) = ((1280 / 1669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (362270929 / 1000000000) ≤ -Real.log (891 / 1280) ∧
    -Real.log (891 / 1280) ≤ (36227093 / 100000000) := by
  have h := checkLog_sound (w := (389 / 2171)) (n := 12)
    (lo := (362270929 / 1000000000)) (hi := (36227093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 891) = 1/(891 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-36227093 / 100000000) (-362270929 / 1000000000) (Real.log (891 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (9768223 / 50000000) ≤ -Real.log (500000 / 607877) ∧
    -Real.log (500000 / 607877) ≤ (195364461 / 1000000000) := by
  have h := checkLog_sound (w := (107877 / 1107877)) (n := 12)
    (lo := (9768223 / 50000000)) (hi := (195364461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607877 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607877 / 500000) = 1/(500000 / 607877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (9768223 / 50000000) (195364461 / 1000000000) (Real.log (607877 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (607877 / 500000) = -Real.log (500000 / 607877) := by
    rw [show ((607877 / 500000) : ℝ) = ((500000 / 607877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (60758133 / 250000000) ≤ -Real.log (392123 / 500000) ∧
    -Real.log (392123 / 500000) ≤ (243032533 / 1000000000) := by
  have h := checkLog_sound (w := (107877 / 892123)) (n := 12)
    (lo := (60758133 / 250000000)) (hi := (243032533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392123) = 1/(392123 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-243032533 / 1000000000) (-60758133 / 250000000) (Real.log (392123 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39141973 / 200000000) ≤ -Real.log (500000 / 608087) ∧
    -Real.log (500000 / 608087) ≤ (97854933 / 500000000) := by
  have h := checkLog_sound (w := (108087 / 1108087)) (n := 12)
    (lo := (39141973 / 200000000)) (hi := (97854933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608087 / 500000) = 1/(500000 / 608087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39141973 / 200000000) (97854933 / 500000000) (Real.log (608087 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (608087 / 500000) = -Real.log (500000 / 608087) := by
    rw [show ((608087 / 500000) : ℝ) = ((500000 / 608087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (121784111 / 500000000) ≤ -Real.log (391913 / 500000) ∧
    -Real.log (391913 / 500000) ≤ (243568223 / 1000000000) := by
  have h := checkLog_sound (w := (108087 / 891913)) (n := 12)
    (lo := (121784111 / 500000000)) (hi := (243568223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391913) = 1/(391913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-243568223 / 1000000000) (-121784111 / 500000000) (Real.log (391913 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35928747 / 250000000) ≤ -Real.log (200000 / 230911) ∧
    -Real.log (200000 / 230911) ≤ (143714989 / 1000000000) := by
  have h := checkLog_sound (w := (30911 / 430911)) (n := 12)
    (lo := (35928747 / 250000000)) (hi := (143714989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230911 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230911 / 200000) = 1/(200000 / 230911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35928747 / 250000000) (143714989 / 1000000000) (Real.log (230911 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (230911 / 200000) = -Real.log (200000 / 230911) := by
    rw [show ((230911 / 200000) : ℝ) = ((200000 / 230911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (167892163 / 1000000000) ≤ -Real.log (169089 / 200000) ∧
    -Real.log (169089 / 200000) ≤ (41973041 / 250000000) := by
  have h := checkLog_sound (w := (30911 / 369089)) (n := 12)
    (lo := (167892163 / 1000000000)) (hi := (41973041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169089) = 1/(169089 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-41973041 / 250000000) (-167892163 / 1000000000) (Real.log (169089 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35995647 / 250000000) ≤ -Real.log (62500 / 72179) ∧
    -Real.log (62500 / 72179) ≤ (143982589 / 1000000000) := by
  have h := checkLog_sound (w := (9679 / 134679)) (n := 12)
    (lo := (35995647 / 250000000)) (hi := (143982589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72179 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72179 / 62500) = 1/(62500 / 72179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35995647 / 250000000) (143982589 / 1000000000) (Real.log (72179 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (72179 / 62500) = -Real.log (62500 / 72179) := by
    rw [show ((72179 / 62500) : ℝ) = ((62500 / 72179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (168257717 / 1000000000) ≤ -Real.log (52821 / 62500) ∧
    -Real.log (52821 / 62500) ≤ (84128859 / 500000000) := by
  have h := checkLog_sound (w := (9679 / 115321)) (n := 12)
    (lo := (168257717 / 1000000000)) (hi := (84128859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 52821) = 1/(52821 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-84128859 / 500000000) (-168257717 / 1000000000) (Real.log (52821 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (78454437 / 125000000) ≤ -Real.log (250000000000 / 468294051627) ∧
    -Real.log (250000000000 / 468294051627) ≤ (627635497 / 1000000000) := by
  have h := checkLog_sound (w := (218294051627 / 718294051627)) (n := 12)
    (lo := (78454437 / 125000000)) (hi := (627635497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468294051627 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468294051627 / 250000000000) = 1/(250000000000 / 468294051627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (78454437 / 125000000) (627635497 / 1000000000) (Real.log (468294051627 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (468294051627 / 250000000000) = -Real.log (250000000000 / 468294051627) := by
    rw [show ((468294051627 / 250000000000) : ℝ) = ((250000000000 / 468294051627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (628926871 / 1000000000) ≤ -Real.log (100000000000 / 187559674249) ∧
    -Real.log (100000000000 / 187559674249) ≤ (78615859 / 125000000) := by
  have h := checkLog_sound (w := (87559674249 / 287559674249)) (n := 12)
    (lo := (628926871 / 1000000000)) (hi := (78615859 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187559674249 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187559674249 / 100000000000) = 1/(100000000000 / 187559674249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (628926871 / 1000000000) (78615859 / 125000000) (Real.log (187559674249 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (187559674249 / 100000000000) = -Real.log (100000000000 / 187559674249) := by
    rw [show ((187559674249 / 100000000000) : ℝ) = ((100000000000 / 187559674249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (6849953 / 15625000) ≤ -Real.log (500000000000 / 775110105757) ∧
    -Real.log (500000000000 / 775110105757) ≤ (438396993 / 1000000000) := by
  have h := checkLog_sound (w := (275110105757 / 1275110105757)) (n := 12)
    (lo := (6849953 / 15625000)) (hi := (438396993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775110105757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775110105757 / 500000000000) = 1/(500000000000 / 775110105757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6849953 / 15625000) (438396993 / 1000000000) (Real.log (775110105757 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (775110105757 / 500000000000) = -Real.log (500000000000 / 775110105757) := by
    rw [show ((775110105757 / 500000000000) : ℝ) = ((500000000000 / 775110105757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (439278087 / 1000000000) ≤ -Real.log (500000000000 / 775793352097) ∧
    -Real.log (500000000000 / 775793352097) ≤ (54909761 / 125000000) := by
  have h := checkLog_sound (w := (275793352097 / 1275793352097)) (n := 12)
    (lo := (439278087 / 1000000000)) (hi := (54909761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775793352097 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775793352097 / 500000000000) = 1/(500000000000 / 775793352097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (439278087 / 1000000000) (54909761 / 125000000) (Real.log (775793352097 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (775793352097 / 500000000000) = -Real.log (500000000000 / 775793352097) := by
    rw [show ((775793352097 / 500000000000) : ℝ) = ((500000000000 / 775793352097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (311607151 / 1000000000) ≤ -Real.log (25000000000 / 34140452661) ∧
    -Real.log (25000000000 / 34140452661) ≤ (19475447 / 62500000) := by
  have h := checkLog_sound (w := (9140452661 / 59140452661)) (n := 12)
    (lo := (311607151 / 1000000000)) (hi := (19475447 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34140452661 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34140452661 / 25000000000) = 1/(25000000000 / 34140452661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (311607151 / 1000000000) (19475447 / 62500000) (Real.log (34140452661 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (34140452661 / 25000000000) = -Real.log (25000000000 / 34140452661) := by
    rw [show ((34140452661 / 25000000000) : ℝ) = ((25000000000 / 34140452661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (62448061 / 200000000) ≤ -Real.log (7812500000 / 10675648653) ∧
    -Real.log (7812500000 / 10675648653) ≤ (156120153 / 500000000) := by
  have h := checkLog_sound (w := (2863148653 / 18488148653)) (n := 12)
    (lo := (62448061 / 200000000)) (hi := (156120153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10675648653 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10675648653 / 7812500000) = 1/(7812500000 / 10675648653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (62448061 / 200000000) (156120153 / 500000000) (Real.log (10675648653 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10675648653 / 7812500000) = -Real.log (7812500000 / 10675648653) := by
    rw [show ((10675648653 / 7812500000) : ℝ) = ((7812500000 / 10675648653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24275129 / 1000000000) ≤ -Real.log (3812566959 / 3906250000) ∧
    -Real.log (3812566959 / 3906250000) ≤ (2427513 / 100000000) := by
  have h := checkLog_sound (w := (93683041 / 7718816959)) (n := 12)
    (lo := (24275129 / 1000000000)) (hi := (2427513 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3812566959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3812566959) = 1/(3812566959 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2427513 / 100000000) (-24275129 / 1000000000) (Real.log (3812566959 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12088587 / 500000000) ≤ -Real.log (39044510079 / 40000000000) ∧
    -Real.log (39044510079 / 40000000000) ≤ (967087 / 40000000) := by
  have h := checkLog_sound (w := (955489921 / 79044510079)) (n := 12)
    (lo := (12088587 / 500000000)) (hi := (967087 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39044510079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39044510079) = 1/(39044510079 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-967087 / 40000000) (-12088587 / 500000000) (Real.log (39044510079 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell092

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell093Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell093
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (33282863 / 125000000) ≤ -Real.log (2560 / 3341) ∧
    -Real.log (2560 / 3341) ≤ (53252581 / 200000000) := by
  have h := checkLog_sound (w := (781 / 5901)) (n := 12)
    (lo := (33282863 / 125000000)) (hi := (53252581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3341 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3341 / 2560) = 1/(2560 / 3341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33282863 / 125000000) (53252581 / 200000000) (Real.log (3341 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3341 / 2560) = -Real.log (2560 / 3341) := by
    rw [show ((3341 / 2560) : ℝ) = ((2560 / 3341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (363955849 / 1000000000) ≤ -Real.log (1779 / 2560) ∧
    -Real.log (1779 / 2560) ≤ (7279117 / 20000000) := by
  have h := checkLog_sound (w := (781 / 4339)) (n := 12)
    (lo := (363955849 / 1000000000)) (hi := (7279117 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1779) = 1/(1779 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7279117 / 20000000) (-363955849 / 1000000000) (Real.log (1779 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66453459 / 250000000) ≤ -Real.log (5120 / 6679) ∧
    -Real.log (5120 / 6679) ≤ (265813837 / 1000000000) := by
  have h := checkLog_sound (w := (1559 / 11799)) (n := 12)
    (lo := (66453459 / 250000000)) (hi := (265813837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6679 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6679 / 5120) = 1/(5120 / 6679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66453459 / 250000000) (265813837 / 1000000000) (Real.log (6679 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6679 / 5120) = -Real.log (5120 / 6679) := by
    rw [show ((6679 / 5120) : ℝ) = ((5120 / 6679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (181556517 / 500000000) ≤ -Real.log (3561 / 5120) ∧
    -Real.log (3561 / 5120) ≤ (72622607 / 200000000) := by
  have h := checkLog_sound (w := (1559 / 8681)) (n := 12)
    (lo := (181556517 / 500000000)) (hi := (72622607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3561) = 1/(3561 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-72622607 / 200000000) (-181556517 / 500000000) (Real.log (3561 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (195709043 / 1000000000) ≤ -Real.log (1000000 / 1216173) ∧
    -Real.log (1000000 / 1216173) ≤ (48927261 / 250000000) := by
  have h := checkLog_sound (w := (216173 / 2216173)) (n := 12)
    (lo := (195709043 / 1000000000)) (hi := (48927261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1216173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1216173 / 1000000) = 1/(1000000 / 1216173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (195709043 / 1000000000) (48927261 / 250000000) (Real.log (1216173 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1216173 / 1000000) = -Real.log (1000000 / 1216173) := by
    rw [show ((1216173 / 1000000) : ℝ) = ((1000000 / 1216173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (121783473 / 500000000) ≤ -Real.log (783827 / 1000000) ∧
    -Real.log (783827 / 1000000) ≤ (243566947 / 1000000000) := by
  have h := checkLog_sound (w := (216173 / 1783827)) (n := 12)
    (lo := (121783473 / 500000000)) (hi := (243566947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 783827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 783827) = 1/(783827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-243566947 / 1000000000) (-121783473 / 500000000) (Real.log (783827 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (196055151 / 1000000000) ≤ -Real.log (500000 / 608297) ∧
    -Real.log (500000 / 608297) ≤ (12253447 / 62500000) := by
  have h := checkLog_sound (w := (108297 / 1108297)) (n := 12)
    (lo := (196055151 / 1000000000)) (hi := (12253447 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608297 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608297 / 500000) = 1/(500000 / 608297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (196055151 / 1000000000) (12253447 / 62500000) (Real.log (608297 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (608297 / 500000) = -Real.log (500000 / 608297) := by
    rw [show ((608297 / 500000) : ℝ) = ((500000 / 608297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (122052099 / 500000000) ≤ -Real.log (391703 / 500000) ∧
    -Real.log (391703 / 500000) ≤ (244104199 / 1000000000) := by
  have h := checkLog_sound (w := (108297 / 891703)) (n := 12)
    (lo := (122052099 / 500000000)) (hi := (244104199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391703) = 1/(391703 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-244104199 / 1000000000) (-122052099 / 500000000) (Real.log (391703 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (71990861 / 500000000) ≤ -Real.log (1000000 / 1154863) ∧
    -Real.log (1000000 / 1154863) ≤ (143981723 / 1000000000) := by
  have h := checkLog_sound (w := (154863 / 2154863)) (n := 12)
    (lo := (71990861 / 500000000)) (hi := (143981723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1154863 / 1000000) = 1/(1000000 / 1154863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (71990861 / 500000000) (143981723 / 1000000000) (Real.log (1154863 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1154863 / 1000000) = -Real.log (1000000 / 1154863) := by
    rw [show ((1154863 / 1000000) : ℝ) = ((1000000 / 1154863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84128267 / 500000000) ≤ -Real.log (845137 / 1000000) ∧
    -Real.log (845137 / 1000000) ≤ (33651307 / 200000000) := by
  have h := checkLog_sound (w := (154863 / 1845137)) (n := 12)
    (lo := (84128267 / 500000000)) (hi := (33651307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 845137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 845137) = 1/(845137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-33651307 / 200000000) (-84128267 / 500000000) (Real.log (845137 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (576997 / 4000000) ≤ -Real.log (250000 / 288793) ∧
    -Real.log (250000 / 288793) ≤ (144249251 / 1000000000) := by
  have h := checkLog_sound (w := (38793 / 538793)) (n := 12)
    (lo := (576997 / 4000000)) (hi := (144249251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288793 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288793 / 250000) = 1/(250000 / 288793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (576997 / 4000000) (144249251 / 1000000000) (Real.log (288793 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (288793 / 250000) = -Real.log (250000 / 288793) := by
    rw [show ((288793 / 250000) : ℝ) = ((250000 / 288793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (84311111 / 500000000) ≤ -Real.log (211207 / 250000) ∧
    -Real.log (211207 / 250000) ≤ (168622223 / 1000000000) := by
  have h := checkLog_sound (w := (38793 / 461207)) (n := 12)
    (lo := (84311111 / 500000000)) (hi := (168622223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211207) = 1/(211207 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-168622223 / 1000000000) (-84311111 / 500000000) (Real.log (211207 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (628926871 / 1000000000) ≤ -Real.log (125000000000 / 234449592811) ∧
    -Real.log (125000000000 / 234449592811) ≤ (78615859 / 125000000) := by
  have h := checkLog_sound (w := (109449592811 / 359449592811)) (n := 12)
    (lo := (628926871 / 1000000000)) (hi := (78615859 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234449592811 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234449592811 / 125000000000) = 1/(125000000000 / 234449592811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (628926871 / 1000000000) (78615859 / 125000000) (Real.log (234449592811 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (234449592811 / 125000000000) = -Real.log (125000000000 / 234449592811) := by
    rw [show ((234449592811 / 125000000000) : ℝ) = ((125000000000 / 234449592811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (315109377 / 500000000) ≤ -Real.log (250000000000 / 469505340079) ∧
    -Real.log (250000000000 / 469505340079) ≤ (126043751 / 200000000) := by
  have h := checkLog_sound (w := (219505340079 / 719505340079)) (n := 12)
    (lo := (315109377 / 500000000)) (hi := (126043751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469505340079 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469505340079 / 250000000000) = 1/(250000000000 / 469505340079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (315109377 / 500000000) (126043751 / 200000000) (Real.log (469505340079 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (469505340079 / 250000000000) = -Real.log (250000000000 / 469505340079) := by
    rw [show ((469505340079 / 250000000000) : ℝ) = ((250000000000 / 469505340079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (439275989 / 1000000000) ≤ -Real.log (500000000000 / 775791724449) ∧
    -Real.log (500000000000 / 775791724449) ≤ (43927599 / 100000000) := by
  have h := checkLog_sound (w := (275791724449 / 1275791724449)) (n := 12)
    (lo := (439275989 / 1000000000)) (hi := (43927599 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775791724449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775791724449 / 500000000000) = 1/(500000000000 / 775791724449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (439275989 / 1000000000) (43927599 / 100000000) (Real.log (775791724449 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (775791724449 / 500000000000) = -Real.log (500000000000 / 775791724449) := by
    rw [show ((775791724449 / 500000000000) : ℝ) = ((500000000000 / 775791724449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (440159349 / 1000000000) ≤ -Real.log (3125000000 / 4852983319) ∧
    -Real.log (3125000000 / 4852983319) ≤ (8803187 / 20000000) := by
  have h := checkLog_sound (w := (1727983319 / 7977983319)) (n := 12)
    (lo := (440159349 / 1000000000)) (hi := (8803187 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4852983319 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4852983319 / 3125000000) = 1/(3125000000 / 4852983319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (440159349 / 1000000000) (8803187 / 20000000) (Real.log (4852983319 / 3125000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (4852983319 / 3125000000) = -Real.log (3125000000 / 4852983319) := by
    rw [show ((4852983319 / 3125000000) : ℝ) = ((3125000000 / 4852983319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (19514891 / 62500000) ≤ -Real.log (500000000000 / 683240113733) ∧
    -Real.log (500000000000 / 683240113733) ≤ (312238257 / 1000000000) := by
  have h := checkLog_sound (w := (183240113733 / 1183240113733)) (n := 12)
    (lo := (19514891 / 62500000)) (hi := (312238257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683240113733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683240113733 / 500000000000) = 1/(500000000000 / 683240113733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (19514891 / 62500000) (312238257 / 1000000000) (Real.log (683240113733 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (683240113733 / 500000000000) = -Real.log (500000000000 / 683240113733) := by
    rw [show ((683240113733 / 500000000000) : ℝ) = ((500000000000 / 683240113733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (312871473 / 1000000000) ≤ -Real.log (50000000000 / 68367288963) ∧
    -Real.log (50000000000 / 68367288963) ≤ (156435737 / 500000000) := by
  have h := checkLog_sound (w := (18367288963 / 118367288963)) (n := 12)
    (lo := (312871473 / 1000000000)) (hi := (156435737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68367288963 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68367288963 / 50000000000) = 1/(50000000000 / 68367288963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (312871473 / 1000000000) (156435737 / 500000000) (Real.log (68367288963 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (68367288963 / 50000000000) = -Real.log (50000000000 / 68367288963) := by
    rw [show ((68367288963 / 50000000000) : ℝ) = ((50000000000 / 68367288963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6093243 / 250000000) ≤ -Real.log (60995103151 / 62500000000) ∧
    -Real.log (60995103151 / 62500000000) ≤ (24372973 / 1000000000) := by
  have h := checkLog_sound (w := (1504896849 / 123495103151)) (n := 12)
    (lo := (6093243 / 250000000)) (hi := (24372973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60995103151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60995103151) = 1/(60995103151 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-24372973 / 1000000000) (-6093243 / 250000000) (Real.log (60995103151 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6068703 / 250000000) ≤ -Real.log (976017451231 / 1000000000000) ∧
    -Real.log (976017451231 / 1000000000000) ≤ (24274813 / 1000000000) := by
  have h := checkLog_sound (w := (23982548769 / 1976017451231)) (n := 12)
    (lo := (6068703 / 250000000)) (hi := (24274813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976017451231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976017451231) = 1/(976017451231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-24274813 / 1000000000) (-6068703 / 250000000) (Real.log (976017451231 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell093

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell094Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell094
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (266711771 / 1000000000) ≤ -Real.log (1024 / 1337) ∧
    -Real.log (1024 / 1337) ≤ (66677943 / 250000000) := by
  have h := checkLog_sound (w := (313 / 2361)) (n := 12)
    (lo := (266711771 / 1000000000)) (hi := (66677943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337 / 1024) = 1/(1024 / 1337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (266711771 / 1000000000) (66677943 / 250000000) (Real.log (1337 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1337 / 1024) = -Real.log (1024 / 1337) := by
    rw [show ((1337 / 1024) : ℝ) = ((1024 / 1337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (583679 / 1600000) ≤ -Real.log (711 / 1024) ∧
    -Real.log (711 / 1024) ≤ (22799961 / 62500000) := by
  have h := checkLog_sound (w := (313 / 1735)) (n := 12)
    (lo := (583679 / 1600000)) (hi := (22799961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 711) = 1/(711 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22799961 / 62500000) (-583679 / 1600000) (Real.log (711 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33282863 / 125000000) ≤ -Real.log (2560 / 3341) ∧
    -Real.log (2560 / 3341) ≤ (53252581 / 200000000) := by
  have h := checkLog_sound (w := (781 / 5901)) (n := 12)
    (lo := (33282863 / 125000000)) (hi := (53252581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3341 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3341 / 2560) = 1/(2560 / 3341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33282863 / 125000000) (53252581 / 200000000) (Real.log (3341 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3341 / 2560) = -Real.log (2560 / 3341) := by
    rw [show ((3341 / 2560) : ℝ) = ((2560 / 3341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (363955849 / 1000000000) ≤ -Real.log (1779 / 2560) ∧
    -Real.log (1779 / 2560) ≤ (7279117 / 20000000) := by
  have h := checkLog_sound (w := (781 / 4339)) (n := 12)
    (lo := (363955849 / 1000000000)) (hi := (7279117 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1779) = 1/(1779 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7279117 / 20000000) (-363955849 / 1000000000) (Real.log (1779 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (196053507 / 1000000000) ≤ -Real.log (62500 / 76037) ∧
    -Real.log (62500 / 76037) ≤ (49013377 / 250000000) := by
  have h := checkLog_sound (w := (13537 / 138537)) (n := 12)
    (lo := (196053507 / 1000000000)) (hi := (49013377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76037 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76037 / 62500) = 1/(62500 / 76037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (196053507 / 1000000000) (49013377 / 250000000) (Real.log (76037 / 62500)) := by
  have h := reflection_log_5_neg
  have he : Real.log (76037 / 62500) = -Real.log (62500 / 76037) := by
    rw [show ((76037 / 62500) : ℝ) = ((62500 / 76037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (48820329 / 200000000) ≤ -Real.log (48963 / 62500) ∧
    -Real.log (48963 / 62500) ≤ (122050823 / 500000000) := by
  have h := checkLog_sound (w := (13537 / 111463)) (n := 12)
    (lo := (48820329 / 200000000)) (hi := (122050823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48963) = 1/(48963 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-122050823 / 500000000) (-48820329 / 200000000) (Real.log (48963 / 62500)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39279899 / 200000000) ≤ -Real.log (1000000 / 1217013) ∧
    -Real.log (1000000 / 1217013) ≤ (24549937 / 125000000) := by
  have h := checkLog_sound (w := (217013 / 2217013)) (n := 12)
    (lo := (39279899 / 200000000)) (hi := (24549937 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217013 / 1000000) = 1/(1000000 / 1217013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39279899 / 200000000) (24549937 / 125000000) (Real.log (1217013 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1217013 / 1000000) = -Real.log (1000000 / 1217013) := by
    rw [show ((1217013 / 1000000) : ℝ) = ((1000000 / 1217013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (48927837 / 200000000) ≤ -Real.log (782987 / 1000000) ∧
    -Real.log (782987 / 1000000) ≤ (122319593 / 500000000) := by
  have h := checkLog_sound (w := (217013 / 1782987)) (n := 12)
    (lo := (48927837 / 200000000)) (hi := (122319593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782987) = 1/(782987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-122319593 / 500000000) (-48927837 / 200000000) (Real.log (782987 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2253881 / 15625000) ≤ -Real.log (1000000 / 1155171) ∧
    -Real.log (1000000 / 1155171) ≤ (28849677 / 200000000) := by
  have h := checkLog_sound (w := (155171 / 2155171)) (n := 12)
    (lo := (2253881 / 15625000)) (hi := (28849677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1155171 / 1000000) = 1/(1000000 / 1155171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2253881 / 15625000) (28849677 / 200000000) (Real.log (1155171 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1155171 / 1000000) = -Real.log (1000000 / 1155171) := by
    rw [show ((1155171 / 1000000) : ℝ) = ((1000000 / 1155171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84310519 / 500000000) ≤ -Real.log (844829 / 1000000) ∧
    -Real.log (844829 / 1000000) ≤ (168621039 / 1000000000) := by
  have h := checkLog_sound (w := (155171 / 1844829)) (n := 12)
    (lo := (84310519 / 500000000)) (hi := (168621039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 844829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 844829) = 1/(844829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-168621039 / 1000000000) (-84310519 / 500000000) (Real.log (844829 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (144516707 / 1000000000) ≤ -Real.log (1000000 / 1155481) ∧
    -Real.log (1000000 / 1155481) ≤ (36129177 / 250000000) := by
  have h := checkLog_sound (w := (155481 / 2155481)) (n := 12)
    (lo := (144516707 / 1000000000)) (hi := (36129177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1155481 / 1000000) = 1/(1000000 / 1155481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (144516707 / 1000000000) (36129177 / 250000000) (Real.log (1155481 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1155481 / 1000000) = -Real.log (1000000 / 1155481) := by
    rw [show ((1155481 / 1000000) : ℝ) = ((1000000 / 1155481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (42247011 / 250000000) ≤ -Real.log (844519 / 1000000) ∧
    -Real.log (844519 / 1000000) ≤ (33797609 / 200000000) := by
  have h := checkLog_sound (w := (155481 / 1844519)) (n := 12)
    (lo := (42247011 / 250000000)) (hi := (33797609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 844519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 844519) = 1/(844519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-33797609 / 200000000) (-42247011 / 250000000) (Real.log (844519 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (315109377 / 500000000) ≤ -Real.log (500000000000 / 939010680157) ∧
    -Real.log (500000000000 / 939010680157) ≤ (126043751 / 200000000) := by
  have h := checkLog_sound (w := (439010680157 / 1439010680157)) (n := 12)
    (lo := (315109377 / 500000000)) (hi := (126043751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939010680157 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939010680157 / 500000000000) = 1/(500000000000 / 939010680157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (315109377 / 500000000) (126043751 / 200000000) (Real.log (939010680157 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (939010680157 / 500000000000) = -Real.log (500000000000 / 939010680157) := by
    rw [show ((939010680157 / 500000000000) : ℝ) = ((500000000000 / 939010680157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (631511147 / 1000000000) ≤ -Real.log (250000000000 / 470112517581) ∧
    -Real.log (250000000000 / 470112517581) ≤ (157877787 / 250000000) := by
  have h := checkLog_sound (w := (220112517581 / 720112517581)) (n := 12)
    (lo := (631511147 / 1000000000)) (hi := (157877787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470112517581 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(470112517581 / 250000000000) = 1/(250000000000 / 470112517581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (631511147 / 1000000000) (157877787 / 250000000) (Real.log (470112517581 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (470112517581 / 250000000000) = -Real.log (250000000000 / 470112517581) := by
    rw [show ((470112517581 / 250000000000) : ℝ) = ((250000000000 / 470112517581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (440155153 / 1000000000) ≤ -Real.log (250000000000 / 388237036129) ∧
    -Real.log (250000000000 / 388237036129) ≤ (220077577 / 500000000) := by
  have h := checkLog_sound (w := (138237036129 / 638237036129)) (n := 12)
    (lo := (440155153 / 1000000000)) (hi := (220077577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388237036129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388237036129 / 250000000000) = 1/(250000000000 / 388237036129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (440155153 / 1000000000) (220077577 / 500000000) (Real.log (388237036129 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (388237036129 / 250000000000) = -Real.log (250000000000 / 388237036129) := by
    rw [show ((388237036129 / 250000000000) : ℝ) = ((250000000000 / 388237036129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (441038681 / 1000000000) ≤ -Real.log (4000000000 / 6217283301) ∧
    -Real.log (4000000000 / 6217283301) ≤ (220519341 / 500000000) := by
  have h := checkLog_sound (w := (2217283301 / 10217283301)) (n := 12)
    (lo := (441038681 / 1000000000)) (hi := (220519341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6217283301 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6217283301 / 4000000000) = 1/(4000000000 / 6217283301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (441038681 / 1000000000) (220519341 / 500000000) (Real.log (6217283301 / 4000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (6217283301 / 4000000000) = -Real.log (4000000000 / 6217283301) := by
    rw [show ((6217283301 / 4000000000) : ℝ) = ((4000000000 / 6217283301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (312869423 / 1000000000) ≤ -Real.log (500000000000 / 683671488549) ∧
    -Real.log (500000000000 / 683671488549) ≤ (19554339 / 62500000) := by
  have h := checkLog_sound (w := (183671488549 / 1183671488549)) (n := 12)
    (lo := (312869423 / 1000000000)) (hi := (19554339 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683671488549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683671488549 / 500000000000) = 1/(500000000000 / 683671488549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (312869423 / 1000000000) (19554339 / 62500000) (Real.log (683671488549 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (683671488549 / 500000000000) = -Real.log (500000000000 / 683671488549) := by
    rw [show ((683671488549 / 500000000000) : ℝ) = ((500000000000 / 683671488549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (313504751 / 1000000000) ≤ -Real.log (250000000000 / 342052991111) ∧
    -Real.log (250000000000 / 342052991111) ≤ (19594047 / 62500000) := by
  have h := checkLog_sound (w := (92052991111 / 592052991111)) (n := 12)
    (lo := (313504751 / 1000000000)) (hi := (19594047 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342052991111 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342052991111 / 250000000000) = 1/(250000000000 / 342052991111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (313504751 / 1000000000) (19594047 / 62500000) (Real.log (342052991111 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (342052991111 / 250000000000) = -Real.log (250000000000 / 342052991111) := by
    rw [show ((342052991111 / 250000000000) : ℝ) = ((250000000000 / 342052991111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3058917 / 125000000) ≤ -Real.log (975825658639 / 1000000000000) ∧
    -Real.log (975825658639 / 1000000000000) ≤ (24471337 / 1000000000) := by
  have h := checkLog_sound (w := (24174341361 / 1975825658639)) (n := 12)
    (lo := (3058917 / 125000000)) (hi := (24471337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975825658639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975825658639) = 1/(975825658639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-24471337 / 1000000000) (-3058917 / 125000000) (Real.log (975825658639 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12186327 / 500000000) ≤ -Real.log (975921960759 / 1000000000000) ∧
    -Real.log (975921960759 / 1000000000000) ≤ (4874531 / 200000000) := by
  have h := checkLog_sound (w := (24078039241 / 1975921960759)) (n := 12)
    (lo := (12186327 / 500000000)) (hi := (4874531 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975921960759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975921960759) = 1/(975921960759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4874531 / 200000000) (-12186327 / 500000000) (Real.log (975921960759 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell094

end


