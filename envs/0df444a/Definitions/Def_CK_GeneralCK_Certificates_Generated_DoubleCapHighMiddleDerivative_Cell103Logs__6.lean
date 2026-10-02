-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell103Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell103Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:24:59.64399+00:00
-- url     : https://prove2.me/theorems/1bb48c3d-7967-4aab-825b-7e92a79d7674
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell103Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell104…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell103Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell104Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell105Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell106Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell107Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell108Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell103Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell104Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell105Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell106Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell107Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell108Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell103Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell104Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell105Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell106Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell107Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell108Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell103Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell104Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell105Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell106Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell107Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell108Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell103Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell103
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

theorem reflection_log_1_neg : (27074253 / 100000000) ≤ -Real.log (640 / 839) ∧
    -Real.log (640 / 839) ≤ (270742531 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1479)) (n := 12)
    (lo := (27074253 / 100000000)) (hi := (270742531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839 / 640) = 1/(640 / 839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27074253 / 100000000) (270742531 / 1000000000) (Real.log (839 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (839 / 640) = -Real.log (640 / 839) := by
    rw [show ((839 / 640) : ℝ) = ((640 / 839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3724233 / 10000000) ≤ -Real.log (441 / 640) ∧
    -Real.log (441 / 640) ≤ (372423301 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1081)) (n := 12)
    (lo := (3724233 / 10000000)) (hi := (372423301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 441) = 1/(441 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-372423301 / 1000000000) (-3724233 / 10000000) (Real.log (441 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (270295469 / 1000000000) ≤ -Real.log (5120 / 6709) ∧
    -Real.log (5120 / 6709) ≤ (27029547 / 100000000) := by
  have h := checkLog_sound (w := (1589 / 11829)) (n := 12)
    (lo := (270295469 / 1000000000)) (hi := (27029547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6709 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6709 / 5120) = 1/(5120 / 6709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (270295469 / 1000000000) (27029547 / 100000000) (Real.log (6709 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6709 / 5120) = -Real.log (5120 / 6709) := by
    rw [show ((6709 / 5120) : ℝ) = ((5120 / 6709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (185786661 / 500000000) ≤ -Real.log (3531 / 5120) ∧
    -Real.log (3531 / 5120) ≤ (371573323 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 8651)) (n := 12)
    (lo := (185786661 / 500000000)) (hi := (371573323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3531) = 1/(3531 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-371573323 / 1000000000) (-185786661 / 500000000) (Real.log (3531 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24894159 / 125000000) ≤ -Real.log (1000000 / 1220369) ∧
    -Real.log (1000000 / 1220369) ≤ (199153273 / 1000000000) := by
  have h := checkLog_sound (w := (220369 / 2220369)) (n := 12)
    (lo := (24894159 / 125000000)) (hi := (199153273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220369 / 1000000) = 1/(1000000 / 1220369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24894159 / 125000000) (199153273 / 1000000000) (Real.log (1220369 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1220369 / 1000000) = -Real.log (1000000 / 1220369) := by
    rw [show ((1220369 / 1000000) : ℝ) = ((1000000 / 1220369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (62233637 / 250000000) ≤ -Real.log (779631 / 1000000) ∧
    -Real.log (779631 / 1000000) ≤ (248934549 / 1000000000) := by
  have h := checkLog_sound (w := (220369 / 1779631)) (n := 12)
    (lo := (62233637 / 250000000)) (hi := (248934549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779631) = 1/(779631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-248934549 / 1000000000) (-62233637 / 250000000) (Real.log (779631 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19949819 / 100000000) ≤ -Real.log (100000 / 122079) ∧
    -Real.log (100000 / 122079) ≤ (199498191 / 1000000000) := by
  have h := checkLog_sound (w := (22079 / 222079)) (n := 12)
    (lo := (19949819 / 100000000)) (hi := (199498191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122079 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122079 / 100000) = 1/(100000 / 122079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (19949819 / 100000000) (199498191 / 1000000000) (Real.log (122079 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (122079 / 100000) = -Real.log (100000 / 122079) := by
    rw [show ((122079 / 100000) : ℝ) = ((100000 / 122079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (249474693 / 1000000000) ≤ -Real.log (77921 / 100000) ∧
    -Real.log (77921 / 100000) ≤ (124737347 / 500000000) := by
  have h := checkLog_sound (w := (22079 / 177921)) (n := 12)
    (lo := (249474693 / 1000000000)) (hi := (124737347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 77921) = 1/(77921 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-124737347 / 500000000) (-249474693 / 1000000000) (Real.log (77921 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (91657 / 625000) ≤ -Real.log (20000 / 23159) ∧
    -Real.log (20000 / 23159) ≤ (146651201 / 1000000000) := by
  have h := checkLog_sound (w := (3159 / 43159)) (n := 12)
    (lo := (91657 / 625000)) (hi := (146651201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23159 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23159 / 20000) = 1/(20000 / 23159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (91657 / 625000) (146651201 / 1000000000) (Real.log (23159 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (23159 / 20000) = -Real.log (20000 / 23159) := by
    rw [show ((23159 / 20000) : ℝ) = ((20000 / 23159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (42978971 / 250000000) ≤ -Real.log (16841 / 20000) ∧
    -Real.log (16841 / 20000) ≤ (34383177 / 200000000) := by
  have h := checkLog_sound (w := (3159 / 36841)) (n := 12)
    (lo := (42978971 / 250000000)) (hi := (34383177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 16841) = 1/(16841 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-34383177 / 200000000) (-42978971 / 250000000) (Real.log (16841 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (73459439 / 500000000) ≤ -Real.log (50000 / 57913) ∧
    -Real.log (50000 / 57913) ≤ (146918879 / 1000000000) := by
  have h := checkLog_sound (w := (7913 / 107913)) (n := 12)
    (lo := (73459439 / 500000000)) (hi := (146918879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57913 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57913 / 50000) = 1/(50000 / 57913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (73459439 / 500000000) (146918879 / 1000000000) (Real.log (57913 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (57913 / 50000) = -Real.log (50000 / 57913) := by
    rw [show ((57913 / 50000) : ℝ) = ((50000 / 57913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (172284101 / 1000000000) ≤ -Real.log (42087 / 50000) ∧
    -Real.log (42087 / 50000) ≤ (86142051 / 500000000) := by
  have h := checkLog_sound (w := (7913 / 92087)) (n := 12)
    (lo := (172284101 / 1000000000)) (hi := (86142051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42087) = 1/(42087 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86142051 / 500000000) (-172284101 / 1000000000) (Real.log (42087 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (641868791 / 1000000000) ≤ -Real.log (250000000000 / 475007080147) ∧
    -Real.log (250000000000 / 475007080147) ≤ (80233599 / 125000000) := by
  have h := checkLog_sound (w := (225007080147 / 725007080147)) (n := 12)
    (lo := (641868791 / 1000000000)) (hi := (80233599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475007080147 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(475007080147 / 250000000000) = 1/(250000000000 / 475007080147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (641868791 / 1000000000) (80233599 / 125000000) (Real.log (475007080147 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (475007080147 / 250000000000) = -Real.log (250000000000 / 475007080147) := by
    rw [show ((475007080147 / 250000000000) : ℝ) = ((250000000000 / 475007080147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (643165831 / 1000000000) ≤ -Real.log (500000000000 / 951247165533) ∧
    -Real.log (500000000000 / 951247165533) ≤ (80395729 / 125000000) := by
  have h := checkLog_sound (w := (451247165533 / 1451247165533)) (n := 12)
    (lo := (643165831 / 1000000000)) (hi := (80395729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951247165533 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951247165533 / 500000000000) = 1/(500000000000 / 951247165533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (643165831 / 1000000000) (80395729 / 125000000) (Real.log (951247165533 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (951247165533 / 500000000000) = -Real.log (500000000000 / 951247165533) := by
    rw [show ((951247165533 / 500000000000) : ℝ) = ((500000000000 / 951247165533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22404391 / 50000000) ≤ -Real.log (125000000000 / 195664519497) ∧
    -Real.log (125000000000 / 195664519497) ≤ (448087821 / 1000000000) := by
  have h := checkLog_sound (w := (70664519497 / 320664519497)) (n := 12)
    (lo := (22404391 / 50000000)) (hi := (448087821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195664519497 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195664519497 / 125000000000) = 1/(125000000000 / 195664519497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22404391 / 50000000) (448087821 / 1000000000) (Real.log (195664519497 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (195664519497 / 125000000000) = -Real.log (125000000000 / 195664519497) := by
    rw [show ((195664519497 / 125000000000) : ℝ) = ((125000000000 / 195664519497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (448972883 / 1000000000) ≤ -Real.log (500000000000 / 783351086357) ∧
    -Real.log (500000000000 / 783351086357) ≤ (112243221 / 250000000) := by
  have h := checkLog_sound (w := (283351086357 / 1283351086357)) (n := 12)
    (lo := (448972883 / 1000000000)) (hi := (112243221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783351086357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783351086357 / 500000000000) = 1/(500000000000 / 783351086357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (448972883 / 1000000000) (112243221 / 250000000) (Real.log (783351086357 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (783351086357 / 500000000000) = -Real.log (500000000000 / 783351086357) := by
    rw [show ((783351086357 / 500000000000) : ℝ) = ((500000000000 / 783351086357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (79641771 / 250000000) ≤ -Real.log (500000000000 / 687577934801) ∧
    -Real.log (500000000000 / 687577934801) ≤ (63713417 / 200000000) := by
  have h := checkLog_sound (w := (187577934801 / 1187577934801)) (n := 12)
    (lo := (79641771 / 250000000)) (hi := (63713417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687577934801 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687577934801 / 500000000000) = 1/(500000000000 / 687577934801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79641771 / 250000000) (63713417 / 200000000) (Real.log (687577934801 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (687577934801 / 500000000000) = -Real.log (500000000000 / 687577934801) := by
    rw [show ((687577934801 / 500000000000) : ℝ) = ((500000000000 / 687577934801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (15960149 / 50000000) ≤ -Real.log (250000000000 / 344007650819) ∧
    -Real.log (250000000000 / 344007650819) ≤ (319202981 / 1000000000) := by
  have h := checkLog_sound (w := (94007650819 / 594007650819)) (n := 12)
    (lo := (15960149 / 50000000)) (hi := (319202981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344007650819 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344007650819 / 250000000000) = 1/(250000000000 / 344007650819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (15960149 / 50000000) (319202981 / 1000000000) (Real.log (344007650819 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (344007650819 / 250000000000) = -Real.log (250000000000 / 344007650819) := by
    rw [show ((344007650819 / 250000000000) : ℝ) = ((250000000000 / 344007650819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (12682611 / 500000000) ≤ -Real.log (2437384431 / 2500000000) ∧
    -Real.log (2437384431 / 2500000000) ≤ (25365223 / 1000000000) := by
  have h := checkLog_sound (w := (62615569 / 4937384431)) (n := 12)
    (lo := (12682611 / 500000000)) (hi := (25365223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2437384431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2437384431) = 1/(2437384431 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25365223 / 1000000000) (-12682611 / 500000000) (Real.log (2437384431 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (25264683 / 1000000000) ≤ -Real.log (390020719 / 400000000) ∧
    -Real.log (390020719 / 400000000) ≤ (6316171 / 250000000) := by
  have h := checkLog_sound (w := (9979281 / 790020719)) (n := 12)
    (lo := (25264683 / 1000000000)) (hi := (6316171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 390020719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 390020719) = 1/(390020719 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6316171 / 250000000) (-25264683 / 1000000000) (Real.log (390020719 / 400000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell103

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell104Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell104
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

theorem reflection_log_1_neg : (27118939 / 100000000) ≤ -Real.log (1024 / 1343) ∧
    -Real.log (1024 / 1343) ≤ (271189391 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 2367)) (n := 12)
    (lo := (27118939 / 100000000)) (hi := (271189391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1343 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1343 / 1024) = 1/(1024 / 1343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27118939 / 100000000) (271189391 / 1000000000) (Real.log (1343 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1343 / 1024) = -Real.log (1024 / 1343) := by
    rw [show ((1343 / 1024) : ℝ) = ((1024 / 1343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (186637001 / 500000000) ≤ -Real.log (705 / 1024) ∧
    -Real.log (705 / 1024) ≤ (373274003 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1729)) (n := 12)
    (lo := (186637001 / 500000000)) (hi := (373274003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 705) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 705) = 1/(705 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-373274003 / 1000000000) (-186637001 / 500000000) (Real.log (705 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27074253 / 100000000) ≤ -Real.log (640 / 839) ∧
    -Real.log (640 / 839) ≤ (270742531 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1479)) (n := 12)
    (lo := (27074253 / 100000000)) (hi := (270742531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839 / 640) = 1/(640 / 839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27074253 / 100000000) (270742531 / 1000000000) (Real.log (839 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (839 / 640) = -Real.log (640 / 839) := by
    rw [show ((839 / 640) : ℝ) = ((640 / 839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3724233 / 10000000) ≤ -Real.log (441 / 640) ∧
    -Real.log (441 / 640) ≤ (372423301 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1081)) (n := 12)
    (lo := (3724233 / 10000000)) (hi := (372423301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 441) = 1/(441 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-372423301 / 1000000000) (-3724233 / 10000000) (Real.log (441 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (199497371 / 1000000000) ≤ -Real.log (1000000 / 1220789) ∧
    -Real.log (1000000 / 1220789) ≤ (49874343 / 250000000) := by
  have h := checkLog_sound (w := (220789 / 2220789)) (n := 12)
    (lo := (199497371 / 1000000000)) (hi := (49874343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220789 / 1000000) = 1/(1000000 / 1220789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (199497371 / 1000000000) (49874343 / 250000000) (Real.log (1220789 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1220789 / 1000000) = -Real.log (1000000 / 1220789) := by
    rw [show ((1220789 / 1000000) : ℝ) = ((1000000 / 1220789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (249473409 / 1000000000) ≤ -Real.log (779211 / 1000000) ∧
    -Real.log (779211 / 1000000) ≤ (24947341 / 100000000) := by
  have h := checkLog_sound (w := (220789 / 1779211)) (n := 12)
    (lo := (249473409 / 1000000000)) (hi := (24947341 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779211) = 1/(779211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-24947341 / 100000000) (-249473409 / 1000000000) (Real.log (779211 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (199841351 / 1000000000) ≤ -Real.log (1000000 / 1221209) ∧
    -Real.log (1000000 / 1221209) ≤ (24980169 / 125000000) := by
  have h := checkLog_sound (w := (221209 / 2221209)) (n := 12)
    (lo := (199841351 / 1000000000)) (hi := (24980169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221209 / 1000000) = 1/(1000000 / 1221209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (199841351 / 1000000000) (24980169 / 125000000) (Real.log (1221209 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1221209 / 1000000) = -Real.log (1000000 / 1221209) := by
    rw [show ((1221209 / 1000000) : ℝ) = ((1000000 / 1221209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (250012561 / 1000000000) ≤ -Real.log (778791 / 1000000) ∧
    -Real.log (778791 / 1000000) ≤ (125006281 / 500000000) := by
  have h := checkLog_sound (w := (221209 / 1778791)) (n := 12)
    (lo := (250012561 / 1000000000)) (hi := (125006281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778791) = 1/(778791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-125006281 / 500000000) (-250012561 / 1000000000) (Real.log (778791 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29383603 / 200000000) ≤ -Real.log (1000000 / 1158259) ∧
    -Real.log (1000000 / 1158259) ≤ (1147797 / 7812500) := by
  have h := checkLog_sound (w := (158259 / 2158259)) (n := 12)
    (lo := (29383603 / 200000000)) (hi := (1147797 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158259 / 1000000) = 1/(1000000 / 1158259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29383603 / 200000000) (1147797 / 7812500) (Real.log (1158259 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1158259 / 1000000) = -Real.log (1000000 / 1158259) := by
    rw [show ((1158259 / 1000000) : ℝ) = ((1000000 / 1158259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (172282913 / 1000000000) ≤ -Real.log (841741 / 1000000) ∧
    -Real.log (841741 / 1000000) ≤ (86141457 / 500000000) := by
  have h := checkLog_sound (w := (158259 / 1841741)) (n := 12)
    (lo := (172282913 / 1000000000)) (hi := (86141457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841741) = 1/(841741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86141457 / 500000000) (-172282913 / 1000000000) (Real.log (841741 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (73592811 / 500000000) ≤ -Real.log (1000000 / 1158569) ∧
    -Real.log (1000000 / 1158569) ≤ (147185623 / 1000000000) := by
  have h := checkLog_sound (w := (158569 / 2158569)) (n := 12)
    (lo := (73592811 / 500000000)) (hi := (147185623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158569 / 1000000) = 1/(1000000 / 1158569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (73592811 / 500000000) (147185623 / 1000000000) (Real.log (1158569 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1158569 / 1000000) = -Real.log (1000000 / 1158569) := by
    rw [show ((1158569 / 1000000) : ℝ) = ((1000000 / 1158569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (34530253 / 200000000) ≤ -Real.log (841431 / 1000000) ∧
    -Real.log (841431 / 1000000) ≤ (86325633 / 500000000) := by
  have h := checkLog_sound (w := (158569 / 1841431)) (n := 12)
    (lo := (34530253 / 200000000)) (hi := (86325633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841431) = 1/(841431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86325633 / 500000000) (-34530253 / 200000000) (Real.log (841431 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (643165831 / 1000000000) ≤ -Real.log (125000000000 / 237811791383) ∧
    -Real.log (125000000000 / 237811791383) ≤ (80395729 / 125000000) := by
  have h := checkLog_sound (w := (112811791383 / 362811791383)) (n := 12)
    (lo := (643165831 / 1000000000)) (hi := (80395729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237811791383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237811791383 / 125000000000) = 1/(125000000000 / 237811791383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (643165831 / 1000000000) (80395729 / 125000000) (Real.log (237811791383 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (237811791383 / 125000000000) = -Real.log (125000000000 / 237811791383) := by
    rw [show ((237811791383 / 125000000000) : ℝ) = ((125000000000 / 237811791383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (644463393 / 1000000000) ≤ -Real.log (7812500000 / 14882535461) ∧
    -Real.log (7812500000 / 14882535461) ≤ (322231697 / 500000000) := by
  have h := checkLog_sound (w := (7070035461 / 22695035461)) (n := 12)
    (lo := (644463393 / 1000000000)) (hi := (322231697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14882535461 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14882535461 / 7812500000) = 1/(7812500000 / 14882535461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (644463393 / 1000000000) (322231697 / 500000000) (Real.log (14882535461 / 7812500000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (14882535461 / 7812500000) = -Real.log (7812500000 / 14882535461) := by
    rw [show ((14882535461 / 7812500000) : ℝ) = ((7812500000 / 14882535461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22448539 / 50000000) ≤ -Real.log (62500000000 / 97918679921) ∧
    -Real.log (62500000000 / 97918679921) ≤ (448970781 / 1000000000) := by
  have h := checkLog_sound (w := (35418679921 / 160418679921)) (n := 12)
    (lo := (22448539 / 50000000)) (hi := (448970781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97918679921 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97918679921 / 62500000000) = 1/(62500000000 / 97918679921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22448539 / 50000000) (448970781 / 1000000000) (Real.log (97918679921 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (97918679921 / 62500000000) = -Real.log (62500000000 / 97918679921) := by
    rw [show ((97918679921 / 62500000000) : ℝ) = ((62500000000 / 97918679921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (449853913 / 1000000000) ≤ -Real.log (500000000000 / 784041546449) ∧
    -Real.log (500000000000 / 784041546449) ≤ (224926957 / 500000000) := by
  have h := checkLog_sound (w := (284041546449 / 1284041546449)) (n := 12)
    (lo := (449853913 / 1000000000)) (hi := (224926957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784041546449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784041546449 / 500000000000) = 1/(500000000000 / 784041546449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (449853913 / 1000000000) (224926957 / 500000000) (Real.log (784041546449 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (784041546449 / 500000000000) = -Real.log (500000000000 / 784041546449) := by
    rw [show ((784041546449 / 500000000000) : ℝ) = ((500000000000 / 784041546449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (9975029 / 31250000) ≤ -Real.log (250000000000 / 344006945129) ∧
    -Real.log (250000000000 / 344006945129) ≤ (319200929 / 1000000000) := by
  have h := checkLog_sound (w := (94006945129 / 594006945129)) (n := 12)
    (lo := (9975029 / 31250000)) (hi := (319200929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344006945129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344006945129 / 250000000000) = 1/(250000000000 / 344006945129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9975029 / 31250000) (319200929 / 1000000000) (Real.log (344006945129 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (344006945129 / 250000000000) = -Real.log (250000000000 / 344006945129) := by
    rw [show ((344006945129 / 250000000000) : ℝ) = ((250000000000 / 344006945129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (39979611 / 125000000) ≤ -Real.log (125000000000 / 172112894581) ∧
    -Real.log (125000000000 / 172112894581) ≤ (319836889 / 1000000000) := by
  have h := checkLog_sound (w := (47112894581 / 297112894581)) (n := 12)
    (lo := (39979611 / 125000000)) (hi := (319836889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172112894581 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172112894581 / 125000000000) = 1/(125000000000 / 172112894581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (39979611 / 125000000) (319836889 / 1000000000) (Real.log (172112894581 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (172112894581 / 125000000000) = -Real.log (125000000000 / 172112894581) := by
    rw [show ((172112894581 / 125000000000) : ℝ) = ((125000000000 / 172112894581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (12732821 / 500000000) ≤ -Real.log (974855872239 / 1000000000000) ∧
    -Real.log (974855872239 / 1000000000000) ≤ (25465643 / 1000000000) := by
  have h := checkLog_sound (w := (25144127761 / 1974855872239)) (n := 12)
    (lo := (12732821 / 500000000)) (hi := (25465643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974855872239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974855872239) = 1/(974855872239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25465643 / 1000000000) (-12732821 / 500000000) (Real.log (974855872239 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (25364897 / 1000000000) ≤ -Real.log (974954088919 / 1000000000000) ∧
    -Real.log (974954088919 / 1000000000000) ≤ (12682449 / 500000000) := by
  have h := checkLog_sound (w := (25045911081 / 1974954088919)) (n := 12)
    (lo := (25364897 / 1000000000)) (hi := (12682449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974954088919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974954088919) = 1/(974954088919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-12682449 / 500000000) (-25364897 / 1000000000) (Real.log (974954088919 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell104

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell105Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell105
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

theorem reflection_log_1_neg : (67909013 / 250000000) ≤ -Real.log (2560 / 3359) ∧
    -Real.log (2560 / 3359) ≤ (271636053 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 5919)) (n := 12)
    (lo := (67909013 / 250000000)) (hi := (271636053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3359 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3359 / 2560) = 1/(2560 / 3359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67909013 / 250000000) (271636053 / 1000000000) (Real.log (3359 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3359 / 2560) = -Real.log (2560 / 3359) := by
    rw [show ((3359 / 2560) : ℝ) = ((2560 / 3359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (93531357 / 250000000) ≤ -Real.log (1761 / 2560) ∧
    -Real.log (1761 / 2560) ≤ (374125429 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 4321)) (n := 12)
    (lo := (93531357 / 250000000)) (hi := (374125429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1761) = 1/(1761 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-374125429 / 1000000000) (-93531357 / 250000000) (Real.log (1761 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27118939 / 100000000) ≤ -Real.log (1024 / 1343) ∧
    -Real.log (1024 / 1343) ≤ (271189391 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 2367)) (n := 12)
    (lo := (27118939 / 100000000)) (hi := (271189391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1343 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1343 / 1024) = 1/(1024 / 1343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27118939 / 100000000) (271189391 / 1000000000) (Real.log (1343 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1343 / 1024) = -Real.log (1024 / 1343) := by
    rw [show ((1343 / 1024) : ℝ) = ((1024 / 1343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (186637001 / 500000000) ≤ -Real.log (705 / 1024) ∧
    -Real.log (705 / 1024) ≤ (373274003 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1729)) (n := 12)
    (lo := (186637001 / 500000000)) (hi := (373274003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 705) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 705) = 1/(705 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-373274003 / 1000000000) (-186637001 / 500000000) (Real.log (705 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49960133 / 250000000) ≤ -Real.log (125000 / 152651) ∧
    -Real.log (125000 / 152651) ≤ (199840533 / 1000000000) := by
  have h := checkLog_sound (w := (27651 / 277651)) (n := 12)
    (lo := (49960133 / 250000000)) (hi := (199840533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152651 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152651 / 125000) = 1/(125000 / 152651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49960133 / 250000000) (199840533 / 1000000000) (Real.log (152651 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (152651 / 125000) = -Real.log (125000 / 152651) := by
    rw [show ((152651 / 125000) : ℝ) = ((125000 / 152651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (250011277 / 1000000000) ≤ -Real.log (97349 / 125000) ∧
    -Real.log (97349 / 125000) ≤ (125005639 / 500000000) := by
  have h := checkLog_sound (w := (27651 / 222349)) (n := 12)
    (lo := (250011277 / 1000000000)) (hi := (125005639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97349) = 1/(97349 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-125005639 / 500000000) (-250011277 / 1000000000) (Real.log (97349 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (200185213 / 1000000000) ≤ -Real.log (1000000 / 1221629) ∧
    -Real.log (1000000 / 1221629) ≤ (100092607 / 500000000) := by
  have h := checkLog_sound (w := (221629 / 2221629)) (n := 12)
    (lo := (200185213 / 1000000000)) (hi := (100092607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221629 / 1000000) = 1/(1000000 / 1221629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (200185213 / 1000000000) (100092607 / 500000000) (Real.log (1221629 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1221629 / 1000000) = -Real.log (1000000 / 1221629) := by
    rw [show ((1221629 / 1000000) : ℝ) = ((1000000 / 1221629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62638001 / 250000000) ≤ -Real.log (778371 / 1000000) ∧
    -Real.log (778371 / 1000000) ≤ (50110401 / 200000000) := by
  have h := checkLog_sound (w := (221629 / 1778371)) (n := 12)
    (lo := (62638001 / 250000000)) (hi := (50110401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778371) = 1/(778371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50110401 / 200000000) (-62638001 / 250000000) (Real.log (778371 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (147184759 / 1000000000) ≤ -Real.log (125000 / 144821) ∧
    -Real.log (125000 / 144821) ≤ (3679619 / 25000000) := by
  have h := checkLog_sound (w := (19821 / 269821)) (n := 12)
    (lo := (147184759 / 1000000000)) (hi := (3679619 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144821 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144821 / 125000) = 1/(125000 / 144821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (147184759 / 1000000000) (3679619 / 25000000) (Real.log (144821 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (144821 / 125000) = -Real.log (125000 / 144821) := by
    rw [show ((144821 / 125000) : ℝ) = ((125000 / 144821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (43162519 / 250000000) ≤ -Real.log (105179 / 125000) ∧
    -Real.log (105179 / 125000) ≤ (172650077 / 1000000000) := by
  have h := checkLog_sound (w := (19821 / 230179)) (n := 12)
    (lo := (43162519 / 250000000)) (hi := (172650077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 105179) = 1/(105179 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-172650077 / 1000000000) (-43162519 / 250000000) (Real.log (105179 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (29490459 / 200000000) ≤ -Real.log (500000 / 579439) ∧
    -Real.log (500000 / 579439) ≤ (18431537 / 125000000) := by
  have h := checkLog_sound (w := (79439 / 1079439)) (n := 12)
    (lo := (29490459 / 200000000)) (hi := (18431537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579439 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579439 / 500000) = 1/(500000 / 579439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (29490459 / 200000000) (18431537 / 125000000) (Real.log (579439 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (579439 / 500000) = -Real.log (500000 / 579439) := by
    rw [show ((579439 / 500000) : ℝ) = ((500000 / 579439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (43254641 / 250000000) ≤ -Real.log (420561 / 500000) ∧
    -Real.log (420561 / 500000) ≤ (34603713 / 200000000) := by
  have h := checkLog_sound (w := (79439 / 920561)) (n := 12)
    (lo := (43254641 / 250000000)) (hi := (34603713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420561) = 1/(420561 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-34603713 / 200000000) (-43254641 / 250000000) (Real.log (420561 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (644463393 / 1000000000) ≤ -Real.log (500000000000 / 952482269503) ∧
    -Real.log (500000000000 / 952482269503) ≤ (322231697 / 500000000) := by
  have h := checkLog_sound (w := (452482269503 / 1452482269503)) (n := 12)
    (lo := (644463393 / 1000000000)) (hi := (322231697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((952482269503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(952482269503 / 500000000000) = 1/(500000000000 / 952482269503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (644463393 / 1000000000) (322231697 / 500000000) (Real.log (952482269503 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (952482269503 / 500000000000) = -Real.log (500000000000 / 952482269503) := by
    rw [show ((952482269503 / 500000000000) : ℝ) = ((500000000000 / 952482269503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (645761481 / 1000000000) ≤ -Real.log (50000000000 / 95371947757) ∧
    -Real.log (50000000000 / 95371947757) ≤ (322880741 / 500000000) := by
  have h := checkLog_sound (w := (45371947757 / 145371947757)) (n := 12)
    (lo := (645761481 / 1000000000)) (hi := (322880741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95371947757 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95371947757 / 50000000000) = 1/(50000000000 / 95371947757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (645761481 / 1000000000) (322880741 / 500000000) (Real.log (95371947757 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (95371947757 / 50000000000) = -Real.log (50000000000 / 95371947757) := by
    rw [show ((95371947757 / 50000000000) : ℝ) = ((50000000000 / 95371947757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (44985181 / 100000000) ≤ -Real.log (500000000000 / 784039897687) ∧
    -Real.log (500000000000 / 784039897687) ≤ (449851811 / 1000000000) := by
  have h := checkLog_sound (w := (284039897687 / 1284039897687)) (n := 12)
    (lo := (44985181 / 100000000)) (hi := (449851811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784039897687 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784039897687 / 500000000000) = 1/(500000000000 / 784039897687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (44985181 / 100000000) (449851811 / 1000000000) (Real.log (784039897687 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (784039897687 / 500000000000) = -Real.log (500000000000 / 784039897687) := by
    rw [show ((784039897687 / 500000000000) : ℝ) = ((500000000000 / 784039897687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (225368609 / 500000000) ≤ -Real.log (250000000000 / 392367200217) ∧
    -Real.log (250000000000 / 392367200217) ≤ (450737219 / 1000000000) := by
  have h := checkLog_sound (w := (142367200217 / 642367200217)) (n := 12)
    (lo := (225368609 / 500000000)) (hi := (450737219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392367200217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392367200217 / 250000000000) = 1/(250000000000 / 392367200217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (225368609 / 500000000) (450737219 / 1000000000) (Real.log (392367200217 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (392367200217 / 250000000000) = -Real.log (250000000000 / 392367200217) := by
    rw [show ((392367200217 / 250000000000) : ℝ) = ((250000000000 / 392367200217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (79958709 / 250000000) ≤ -Real.log (500000000000 / 688450165907) ∧
    -Real.log (500000000000 / 688450165907) ≤ (319834837 / 1000000000) := by
  have h := checkLog_sound (w := (188450165907 / 1188450165907)) (n := 12)
    (lo := (79958709 / 250000000)) (hi := (319834837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688450165907 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688450165907 / 500000000000) = 1/(500000000000 / 688450165907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79958709 / 250000000) (319834837 / 1000000000) (Real.log (688450165907 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (688450165907 / 500000000000) = -Real.log (500000000000 / 688450165907) := by
    rw [show ((688450165907 / 500000000000) : ℝ) = ((500000000000 / 688450165907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (320470859 / 1000000000) ≤ -Real.log (125000000000 / 172222043889) ∧
    -Real.log (125000000000 / 172222043889) ≤ (16023543 / 50000000) := by
  have h := checkLog_sound (w := (47222043889 / 297222043889)) (n := 12)
    (lo := (320470859 / 1000000000)) (hi := (16023543 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172222043889 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172222043889 / 125000000000) = 1/(125000000000 / 172222043889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (320470859 / 1000000000) (16023543 / 50000000) (Real.log (172222043889 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (172222043889 / 125000000000) = -Real.log (125000000000 / 172222043889) := by
    rw [show ((172222043889 / 125000000000) : ℝ) = ((125000000000 / 172222043889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6391567 / 250000000) ≤ -Real.log (243689445279 / 250000000000) ∧
    -Real.log (243689445279 / 250000000000) ≤ (25566269 / 1000000000) := by
  have h := checkLog_sound (w := (6310554721 / 493689445279)) (n := 12)
    (lo := (6391567 / 250000000)) (hi := (25566269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243689445279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243689445279) = 1/(243689445279 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25566269 / 1000000000) (-6391567 / 250000000) (Real.log (243689445279 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6366329 / 250000000) ≤ -Real.log (15232127959 / 15625000000) ∧
    -Real.log (15232127959 / 15625000000) ≤ (25465317 / 1000000000) := by
  have h := checkLog_sound (w := (392872041 / 30857127959)) (n := 12)
    (lo := (6366329 / 250000000)) (hi := (25465317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15232127959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15232127959) = 1/(15232127959 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-25465317 / 1000000000) (-6366329 / 250000000) (Real.log (15232127959 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell105

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell106Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell106
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

theorem reflection_log_1_neg : (272082513 / 1000000000) ≤ -Real.log (5120 / 6721) ∧
    -Real.log (5120 / 6721) ≤ (136041257 / 500000000) := by
  have h := checkLog_sound (w := (1601 / 11841)) (n := 12)
    (lo := (272082513 / 1000000000)) (hi := (136041257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6721 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6721 / 5120) = 1/(5120 / 6721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (272082513 / 1000000000) (136041257 / 500000000) (Real.log (6721 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6721 / 5120) = -Real.log (5120 / 6721) := by
    rw [show ((6721 / 5120) : ℝ) = ((5120 / 6721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (18748879 / 50000000) ≤ -Real.log (3519 / 5120) ∧
    -Real.log (3519 / 5120) ≤ (374977581 / 1000000000) := by
  have h := checkLog_sound (w := (1601 / 8639)) (n := 12)
    (lo := (18748879 / 50000000)) (hi := (374977581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3519) = 1/(3519 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-374977581 / 1000000000) (-18748879 / 50000000) (Real.log (3519 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67909013 / 250000000) ≤ -Real.log (2560 / 3359) ∧
    -Real.log (2560 / 3359) ≤ (271636053 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 5919)) (n := 12)
    (lo := (67909013 / 250000000)) (hi := (271636053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3359 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3359 / 2560) = 1/(2560 / 3359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67909013 / 250000000) (271636053 / 1000000000) (Real.log (3359 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3359 / 2560) = -Real.log (2560 / 3359) := by
    rw [show ((3359 / 2560) : ℝ) = ((2560 / 3359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (93531357 / 250000000) ≤ -Real.log (1761 / 2560) ∧
    -Real.log (1761 / 2560) ≤ (374125429 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 4321)) (n := 12)
    (lo := (93531357 / 250000000)) (hi := (374125429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1761) = 1/(1761 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-374125429 / 1000000000) (-93531357 / 250000000) (Real.log (1761 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (40036879 / 200000000) ≤ -Real.log (250000 / 305407) ∧
    -Real.log (250000 / 305407) ≤ (50046099 / 250000000) := by
  have h := checkLog_sound (w := (55407 / 555407)) (n := 12)
    (lo := (40036879 / 200000000)) (hi := (50046099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305407 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305407 / 250000) = 1/(250000 / 305407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (40036879 / 200000000) (50046099 / 250000000) (Real.log (305407 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (305407 / 250000) = -Real.log (250000 / 305407) := by
    rw [show ((305407 / 250000) : ℝ) = ((250000 / 305407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (250550719 / 1000000000) ≤ -Real.log (194593 / 250000) ∧
    -Real.log (194593 / 250000) ≤ (782971 / 3125000) := by
  have h := checkLog_sound (w := (55407 / 444593)) (n := 12)
    (lo := (250550719 / 1000000000)) (hi := (782971 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194593) = 1/(194593 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-782971 / 3125000) (-250550719 / 1000000000) (Real.log (194593 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (100264479 / 500000000) ≤ -Real.log (1000000 / 1222049) ∧
    -Real.log (1000000 / 1222049) ≤ (200528959 / 1000000000) := by
  have h := checkLog_sound (w := (222049 / 2222049)) (n := 12)
    (lo := (100264479 / 500000000)) (hi := (200528959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222049 / 1000000) = 1/(1000000 / 1222049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (100264479 / 500000000) (200528959 / 1000000000) (Real.log (1222049 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1222049 / 1000000) = -Real.log (1000000 / 1222049) := by
    rw [show ((1222049 / 1000000) : ℝ) = ((1000000 / 1222049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (125545869 / 500000000) ≤ -Real.log (777951 / 1000000) ∧
    -Real.log (777951 / 1000000) ≤ (251091739 / 1000000000) := by
  have h := checkLog_sound (w := (222049 / 1777951)) (n := 12)
    (lo := (125545869 / 500000000)) (hi := (251091739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777951) = 1/(777951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-251091739 / 1000000000) (-125545869 / 500000000) (Real.log (777951 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18431429 / 125000000) ≤ -Real.log (1000000 / 1158877) ∧
    -Real.log (1000000 / 1158877) ≤ (147451433 / 1000000000) := by
  have h := checkLog_sound (w := (158877 / 2158877)) (n := 12)
    (lo := (18431429 / 125000000)) (hi := (147451433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158877 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158877 / 1000000) = 1/(1000000 / 1158877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18431429 / 125000000) (147451433 / 1000000000) (Real.log (1158877 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1158877 / 1000000) = -Real.log (1000000 / 1158877) := by
    rw [show ((1158877 / 1000000) : ℝ) = ((1000000 / 1158877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1384139 / 8000000) ≤ -Real.log (841123 / 1000000) ∧
    -Real.log (841123 / 1000000) ≤ (5406793 / 31250000) := by
  have h := checkLog_sound (w := (158877 / 1841123)) (n := 12)
    (lo := (1384139 / 8000000)) (hi := (5406793 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841123) = 1/(841123 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5406793 / 31250000) (-1384139 / 8000000) (Real.log (841123 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (147718897 / 1000000000) ≤ -Real.log (1000000 / 1159187) ∧
    -Real.log (1000000 / 1159187) ≤ (73859449 / 500000000) := by
  have h := checkLog_sound (w := (159187 / 2159187)) (n := 12)
    (lo := (147718897 / 1000000000)) (hi := (73859449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1159187 / 1000000) = 1/(1000000 / 1159187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (147718897 / 1000000000) (73859449 / 500000000) (Real.log (1159187 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1159187 / 1000000) = -Real.log (1000000 / 1159187) := by
    rw [show ((1159187 / 1000000) : ℝ) = ((1000000 / 1159187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (86692999 / 500000000) ≤ -Real.log (840813 / 1000000) ∧
    -Real.log (840813 / 1000000) ≤ (173385999 / 1000000000) := by
  have h := checkLog_sound (w := (159187 / 1840813)) (n := 12)
    (lo := (86692999 / 500000000)) (hi := (173385999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 840813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 840813) = 1/(840813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-173385999 / 1000000000) (-86692999 / 500000000) (Real.log (840813 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (645761481 / 1000000000) ≤ -Real.log (500000000000 / 953719477569) ∧
    -Real.log (500000000000 / 953719477569) ≤ (322880741 / 500000000) := by
  have h := checkLog_sound (w := (453719477569 / 1453719477569)) (n := 12)
    (lo := (645761481 / 1000000000)) (hi := (322880741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953719477569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953719477569 / 500000000000) = 1/(500000000000 / 953719477569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (645761481 / 1000000000) (322880741 / 500000000) (Real.log (953719477569 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (953719477569 / 500000000000) = -Real.log (500000000000 / 953719477569) := by
    rw [show ((953719477569 / 500000000000) : ℝ) = ((500000000000 / 953719477569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (323530047 / 500000000) ≤ -Real.log (500000000000 / 954958795113) ∧
    -Real.log (500000000000 / 954958795113) ≤ (129412019 / 200000000) := by
  have h := checkLog_sound (w := (454958795113 / 1454958795113)) (n := 12)
    (lo := (323530047 / 500000000)) (hi := (129412019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((954958795113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(954958795113 / 500000000000) = 1/(500000000000 / 954958795113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (323530047 / 500000000) (129412019 / 200000000) (Real.log (954958795113 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (954958795113 / 500000000000) = -Real.log (500000000000 / 954958795113) := by
    rw [show ((954958795113 / 500000000000) : ℝ) = ((500000000000 / 954958795113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (90147023 / 200000000) ≤ -Real.log (500000000000 / 784732749893) ∧
    -Real.log (500000000000 / 784732749893) ≤ (112683779 / 250000000) := by
  have h := checkLog_sound (w := (284732749893 / 1284732749893)) (n := 12)
    (lo := (90147023 / 200000000)) (hi := (112683779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784732749893 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784732749893 / 500000000000) = 1/(500000000000 / 784732749893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (90147023 / 200000000) (112683779 / 250000000) (Real.log (784732749893 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (784732749893 / 500000000000) = -Real.log (500000000000 / 784732749893) := by
    rw [show ((784732749893 / 500000000000) : ℝ) = ((500000000000 / 784732749893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (56452587 / 125000000) ≤ -Real.log (100000000000 / 157085600507) ∧
    -Real.log (100000000000 / 157085600507) ≤ (451620697 / 1000000000) := by
  have h := checkLog_sound (w := (57085600507 / 257085600507)) (n := 12)
    (lo := (56452587 / 125000000)) (hi := (451620697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157085600507 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157085600507 / 100000000000) = 1/(100000000000 / 157085600507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (56452587 / 125000000) (451620697 / 1000000000) (Real.log (157085600507 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (157085600507 / 100000000000) = -Real.log (100000000000 / 157085600507) := by
    rw [show ((157085600507 / 100000000000) : ℝ) = ((100000000000 / 157085600507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (320468807 / 1000000000) ≤ -Real.log (250000000000 / 344443381051) ∧
    -Real.log (250000000000 / 344443381051) ≤ (40058601 / 125000000) := by
  have h := checkLog_sound (w := (94443381051 / 594443381051)) (n := 12)
    (lo := (320468807 / 1000000000)) (hi := (40058601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344443381051 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344443381051 / 250000000000) = 1/(250000000000 / 344443381051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (320468807 / 1000000000) (40058601 / 125000000) (Real.log (344443381051 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (344443381051 / 250000000000) = -Real.log (250000000000 / 344443381051) := by
    rw [show ((344443381051 / 250000000000) : ℝ) = ((250000000000 / 344443381051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (64220979 / 200000000) ≤ -Real.log (50000000000 / 68932509369) ∧
    -Real.log (50000000000 / 68932509369) ≤ (627158 / 1953125) := by
  have h := checkLog_sound (w := (18932509369 / 118932509369)) (n := 12)
    (lo := (64220979 / 200000000)) (hi := (627158 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68932509369 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68932509369 / 50000000000) = 1/(50000000000 / 68932509369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (64220979 / 200000000) (627158 / 1953125) (Real.log (68932509369 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (68932509369 / 50000000000) = -Real.log (50000000000 / 68932509369) := by
    rw [show ((68932509369 / 50000000000) : ℝ) = ((50000000000 / 68932509369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (256671 / 10000000) ≤ -Real.log (974659499031 / 1000000000000) ∧
    -Real.log (974659499031 / 1000000000000) ≤ (25667101 / 1000000000) := by
  have h := checkLog_sound (w := (25340500969 / 1974659499031)) (n := 12)
    (lo := (256671 / 10000000)) (hi := (25667101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974659499031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974659499031) = 1/(974659499031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25667101 / 1000000000) (-256671 / 10000000) (Real.log (974659499031 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12782971 / 500000000) ≤ -Real.log (974758098871 / 1000000000000) ∧
    -Real.log (974758098871 / 1000000000000) ≤ (25565943 / 1000000000) := by
  have h := checkLog_sound (w := (25241901129 / 1974758098871)) (n := 12)
    (lo := (12782971 / 500000000)) (hi := (25565943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974758098871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974758098871) = 1/(974758098871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-25565943 / 1000000000) (-12782971 / 500000000) (Real.log (974758098871 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell106

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell107Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell107
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

theorem reflection_log_1_neg : (34066097 / 125000000) ≤ -Real.log (1280 / 1681) ∧
    -Real.log (1280 / 1681) ≤ (272528777 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 2961)) (n := 12)
    (lo := (34066097 / 125000000)) (hi := (272528777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1681 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1681 / 1280) = 1/(1280 / 1681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (34066097 / 125000000) (272528777 / 1000000000) (Real.log (1681 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1681 / 1280) = -Real.log (1280 / 1681) := by
    rw [show ((1681 / 1280) : ℝ) = ((1280 / 1681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (375830459 / 1000000000) ≤ -Real.log (879 / 1280) ∧
    -Real.log (879 / 1280) ≤ (18791523 / 50000000) := by
  have h := checkLog_sound (w := (401 / 2159)) (n := 12)
    (lo := (375830459 / 1000000000)) (hi := (18791523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 879) = 1/(879 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18791523 / 50000000) (-375830459 / 1000000000) (Real.log (879 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (272082513 / 1000000000) ≤ -Real.log (5120 / 6721) ∧
    -Real.log (5120 / 6721) ≤ (136041257 / 500000000) := by
  have h := checkLog_sound (w := (1601 / 11841)) (n := 12)
    (lo := (272082513 / 1000000000)) (hi := (136041257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6721 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6721 / 5120) = 1/(5120 / 6721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (272082513 / 1000000000) (136041257 / 500000000) (Real.log (6721 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6721 / 5120) = -Real.log (5120 / 6721) := by
    rw [show ((6721 / 5120) : ℝ) = ((5120 / 6721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (18748879 / 50000000) ≤ -Real.log (3519 / 5120) ∧
    -Real.log (3519 / 5120) ≤ (374977581 / 1000000000) := by
  have h := checkLog_sound (w := (1601 / 8639)) (n := 12)
    (lo := (18748879 / 50000000)) (hi := (374977581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3519) = 1/(3519 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-374977581 / 1000000000) (-18748879 / 50000000) (Real.log (3519 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (200528139 / 1000000000) ≤ -Real.log (31250 / 38189) ∧
    -Real.log (31250 / 38189) ≤ (10026407 / 50000000) := by
  have h := checkLog_sound (w := (6939 / 69439)) (n := 12)
    (lo := (200528139 / 1000000000)) (hi := (10026407 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38189 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38189 / 31250) = 1/(31250 / 38189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (200528139 / 1000000000) (10026407 / 50000000) (Real.log (38189 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (38189 / 31250) = -Real.log (31250 / 38189) := by
    rw [show ((38189 / 31250) : ℝ) = ((31250 / 38189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (251090453 / 1000000000) ≤ -Real.log (24311 / 31250) ∧
    -Real.log (24311 / 31250) ≤ (125545227 / 500000000) := by
  have h := checkLog_sound (w := (6939 / 55561)) (n := 12)
    (lo := (251090453 / 1000000000)) (hi := (125545227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24311) = 1/(24311 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-125545227 / 500000000) (-251090453 / 1000000000) (Real.log (24311 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25109073 / 125000000) ≤ -Real.log (1000000 / 1222469) ∧
    -Real.log (1000000 / 1222469) ≤ (40174517 / 200000000) := by
  have h := checkLog_sound (w := (222469 / 2222469)) (n := 12)
    (lo := (25109073 / 125000000)) (hi := (40174517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222469 / 1000000) = 1/(1000000 / 1222469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25109073 / 125000000) (40174517 / 200000000) (Real.log (1222469 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1222469 / 1000000) = -Real.log (1000000 / 1222469) := by
    rw [show ((1222469 / 1000000) : ℝ) = ((1000000 / 1222469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62907941 / 250000000) ≤ -Real.log (777531 / 1000000) ∧
    -Real.log (777531 / 1000000) ≤ (50326353 / 200000000) := by
  have h := checkLog_sound (w := (222469 / 1777531)) (n := 12)
    (lo := (62907941 / 250000000)) (hi := (50326353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777531) = 1/(777531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50326353 / 200000000) (-62907941 / 250000000) (Real.log (777531 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (73859017 / 500000000) ≤ -Real.log (500000 / 579593) ∧
    -Real.log (500000 / 579593) ≤ (29543607 / 200000000) := by
  have h := checkLog_sound (w := (79593 / 1079593)) (n := 12)
    (lo := (73859017 / 500000000)) (hi := (29543607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579593 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579593 / 500000) = 1/(500000 / 579593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (73859017 / 500000000) (29543607 / 200000000) (Real.log (579593 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (579593 / 500000) = -Real.log (500000 / 579593) := by
    rw [show ((579593 / 500000) : ℝ) = ((500000 / 579593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21673101 / 125000000) ≤ -Real.log (420407 / 500000) ∧
    -Real.log (420407 / 500000) ≤ (173384809 / 1000000000) := by
  have h := checkLog_sound (w := (79593 / 920407)) (n := 12)
    (lo := (21673101 / 125000000)) (hi := (173384809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420407) = 1/(420407 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-173384809 / 1000000000) (-21673101 / 125000000) (Real.log (420407 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (147985427 / 1000000000) ≤ -Real.log (125000 / 144937) ∧
    -Real.log (125000 / 144937) ≤ (36996357 / 250000000) := by
  have h := checkLog_sound (w := (19937 / 269937)) (n := 12)
    (lo := (147985427 / 1000000000)) (hi := (36996357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144937 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144937 / 125000) = 1/(125000 / 144937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (147985427 / 1000000000) (36996357 / 250000000) (Real.log (144937 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (144937 / 125000) = -Real.log (125000 / 144937) := by
    rw [show ((144937 / 125000) : ℝ) = ((125000 / 144937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (173753567 / 1000000000) ≤ -Real.log (105063 / 125000) ∧
    -Real.log (105063 / 125000) ≤ (5429799 / 31250000) := by
  have h := checkLog_sound (w := (19937 / 230063)) (n := 12)
    (lo := (173753567 / 1000000000)) (hi := (5429799 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 105063) = 1/(105063 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5429799 / 31250000) (-173753567 / 1000000000) (Real.log (105063 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (323530047 / 500000000) ≤ -Real.log (62500000000 / 119369849389) ∧
    -Real.log (62500000000 / 119369849389) ≤ (129412019 / 200000000) := by
  have h := checkLog_sound (w := (56869849389 / 181869849389)) (n := 12)
    (lo := (323530047 / 500000000)) (hi := (129412019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119369849389 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119369849389 / 62500000000) = 1/(62500000000 / 119369849389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (323530047 / 500000000) (129412019 / 200000000) (Real.log (119369849389 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (119369849389 / 62500000000) = -Real.log (62500000000 / 119369849389) := by
    rw [show ((119369849389 / 62500000000) : ℝ) = ((62500000000 / 119369849389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (129671847 / 200000000) ≤ -Real.log (125000000000 / 239050056883) ∧
    -Real.log (125000000000 / 239050056883) ≤ (162089809 / 250000000) := by
  have h := checkLog_sound (w := (114050056883 / 364050056883)) (n := 12)
    (lo := (129671847 / 200000000)) (hi := (162089809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239050056883 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239050056883 / 125000000000) = 1/(125000000000 / 239050056883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (129671847 / 200000000) (162089809 / 250000000) (Real.log (239050056883 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (239050056883 / 125000000000) = -Real.log (125000000000 / 239050056883) := by
    rw [show ((239050056883 / 125000000000) : ℝ) = ((125000000000 / 239050056883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (451618593 / 1000000000) ≤ -Real.log (500000000000 / 785426350211) ∧
    -Real.log (500000000000 / 785426350211) ≤ (225809297 / 500000000) := by
  have h := checkLog_sound (w := (285426350211 / 1285426350211)) (n := 12)
    (lo := (451618593 / 1000000000)) (hi := (225809297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((785426350211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(785426350211 / 500000000000) = 1/(500000000000 / 785426350211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (451618593 / 1000000000) (225809297 / 500000000) (Real.log (785426350211 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (785426350211 / 500000000000) = -Real.log (500000000000 / 785426350211) := by
    rw [show ((785426350211 / 500000000000) : ℝ) = ((500000000000 / 785426350211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (113126087 / 250000000) ≤ -Real.log (100000000000 / 157224470793) ∧
    -Real.log (100000000000 / 157224470793) ≤ (452504349 / 1000000000) := by
  have h := checkLog_sound (w := (57224470793 / 257224470793)) (n := 12)
    (lo := (113126087 / 250000000)) (hi := (452504349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157224470793 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157224470793 / 100000000000) = 1/(100000000000 / 157224470793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (113126087 / 250000000) (452504349 / 1000000000) (Real.log (157224470793 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (157224470793 / 100000000000) = -Real.log (100000000000 / 157224470793) := by
    rw [show ((157224470793 / 100000000000) : ℝ) = ((100000000000 / 157224470793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (321102843 / 1000000000) ≤ -Real.log (125000000000 / 172330919799) ∧
    -Real.log (125000000000 / 172330919799) ≤ (80275711 / 250000000) := by
  have h := checkLog_sound (w := (47330919799 / 297330919799)) (n := 12)
    (lo := (321102843 / 1000000000)) (hi := (80275711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172330919799 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172330919799 / 125000000000) = 1/(125000000000 / 172330919799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (321102843 / 1000000000) (80275711 / 250000000) (Real.log (172330919799 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (172330919799 / 125000000000) = -Real.log (125000000000 / 172330919799) := by
    rw [show ((172330919799 / 125000000000) : ℝ) = ((125000000000 / 172330919799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (64347799 / 200000000) ≤ -Real.log (500000000000 / 689762333077) ∧
    -Real.log (500000000000 / 689762333077) ≤ (80434749 / 250000000) := by
  have h := checkLog_sound (w := (189762333077 / 1189762333077)) (n := 12)
    (lo := (64347799 / 200000000)) (hi := (80434749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689762333077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689762333077 / 500000000000) = 1/(500000000000 / 689762333077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (64347799 / 200000000) (80434749 / 250000000) (Real.log (689762333077 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (689762333077 / 500000000000) = -Real.log (500000000000 / 689762333077) := by
    rw [show ((689762333077 / 500000000000) : ℝ) = ((500000000000 / 689762333077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25768139 / 1000000000) ≤ -Real.log (15227516031 / 15625000000) ∧
    -Real.log (15227516031 / 15625000000) ≤ (1288407 / 50000000) := by
  have h := checkLog_sound (w := (397483969 / 30852516031)) (n := 12)
    (lo := (25768139 / 1000000000)) (hi := (1288407 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15227516031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15227516031) = 1/(15227516031 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1288407 / 50000000) (-25768139 / 1000000000) (Real.log (15227516031 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12833387 / 500000000) ≤ -Real.log (243664954351 / 250000000000) ∧
    -Real.log (243664954351 / 250000000000) ≤ (1026671 / 40000000) := by
  have h := checkLog_sound (w := (6335045649 / 493664954351)) (n := 12)
    (lo := (12833387 / 500000000)) (hi := (1026671 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243664954351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243664954351) = 1/(243664954351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1026671 / 40000000) (-12833387 / 500000000) (Real.log (243664954351 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell107

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell108Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell108
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

theorem reflection_log_1_neg : (272974839 / 1000000000) ≤ -Real.log (5120 / 6727) ∧
    -Real.log (5120 / 6727) ≤ (6824371 / 25000000) := by
  have h := checkLog_sound (w := (1607 / 11847)) (n := 12)
    (lo := (272974839 / 1000000000)) (hi := (6824371 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6727 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6727 / 5120) = 1/(5120 / 6727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (272974839 / 1000000000) (6824371 / 25000000) (Real.log (6727 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6727 / 5120) = -Real.log (5120 / 6727) := by
    rw [show ((6727 / 5120) : ℝ) = ((5120 / 6727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (75336813 / 200000000) ≤ -Real.log (3513 / 5120) ∧
    -Real.log (3513 / 5120) ≤ (188342033 / 500000000) := by
  have h := checkLog_sound (w := (1607 / 8633)) (n := 12)
    (lo := (75336813 / 200000000)) (hi := (188342033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3513) = 1/(3513 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-188342033 / 500000000) (-75336813 / 200000000) (Real.log (3513 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (34066097 / 125000000) ≤ -Real.log (1280 / 1681) ∧
    -Real.log (1280 / 1681) ≤ (272528777 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 2961)) (n := 12)
    (lo := (34066097 / 125000000)) (hi := (272528777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1681 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1681 / 1280) = 1/(1280 / 1681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (34066097 / 125000000) (272528777 / 1000000000) (Real.log (1681 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1681 / 1280) = -Real.log (1280 / 1681) := by
    rw [show ((1681 / 1280) : ℝ) = ((1280 / 1681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (375830459 / 1000000000) ≤ -Real.log (879 / 1280) ∧
    -Real.log (879 / 1280) ≤ (18791523 / 50000000) := by
  have h := checkLog_sound (w := (401 / 2159)) (n := 12)
    (lo := (375830459 / 1000000000)) (hi := (18791523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 879) = 1/(879 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18791523 / 50000000) (-375830459 / 1000000000) (Real.log (879 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50217737 / 250000000) ≤ -Real.log (1000000 / 1222467) ∧
    -Real.log (1000000 / 1222467) ≤ (200870949 / 1000000000) := by
  have h := checkLog_sound (w := (222467 / 2222467)) (n := 12)
    (lo := (50217737 / 250000000)) (hi := (200870949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222467 / 1000000) = 1/(1000000 / 1222467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50217737 / 250000000) (200870949 / 1000000000) (Real.log (1222467 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1222467 / 1000000) = -Real.log (1000000 / 1222467) := by
    rw [show ((1222467 / 1000000) : ℝ) = ((1000000 / 1222467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31453649 / 125000000) ≤ -Real.log (777533 / 1000000) ∧
    -Real.log (777533 / 1000000) ≤ (251629193 / 1000000000) := by
  have h := checkLog_sound (w := (222467 / 1777533)) (n := 12)
    (lo := (31453649 / 125000000)) (hi := (251629193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777533) = 1/(777533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-251629193 / 1000000000) (-31453649 / 125000000) (Real.log (777533 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (100607637 / 500000000) ≤ -Real.log (125000 / 152861) ∧
    -Real.log (125000 / 152861) ≤ (8048611 / 40000000) := by
  have h := checkLog_sound (w := (27861 / 277861)) (n := 12)
    (lo := (100607637 / 500000000)) (hi := (8048611 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152861 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152861 / 125000) = 1/(125000 / 152861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (100607637 / 500000000) (8048611 / 40000000) (Real.log (152861 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (152861 / 125000) = -Real.log (125000 / 152861) := by
    rw [show ((152861 / 125000) : ℝ) = ((125000 / 152861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126085397 / 500000000) ≤ -Real.log (97139 / 125000) ∧
    -Real.log (97139 / 125000) ≤ (50434159 / 200000000) := by
  have h := checkLog_sound (w := (27861 / 222139)) (n := 12)
    (lo := (126085397 / 500000000)) (hi := (50434159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97139) = 1/(97139 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50434159 / 200000000) (-126085397 / 500000000) (Real.log (97139 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29596913 / 200000000) ≤ -Real.log (200000 / 231899) ∧
    -Real.log (200000 / 231899) ≤ (73992283 / 500000000) := by
  have h := checkLog_sound (w := (31899 / 431899)) (n := 12)
    (lo := (29596913 / 200000000)) (hi := (73992283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231899 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231899 / 200000) = 1/(200000 / 231899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29596913 / 200000000) (73992283 / 500000000) (Real.log (231899 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (231899 / 200000) = -Real.log (200000 / 231899) := by
    rw [show ((231899 / 200000) : ℝ) = ((200000 / 231899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (173752377 / 1000000000) ≤ -Real.log (168101 / 200000) ∧
    -Real.log (168101 / 200000) ≤ (86876189 / 500000000) := by
  have h := checkLog_sound (w := (31899 / 368101)) (n := 12)
    (lo := (173752377 / 1000000000)) (hi := (86876189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168101) = 1/(168101 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86876189 / 500000000) (-173752377 / 1000000000) (Real.log (168101 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (148252749 / 1000000000) ≤ -Real.log (500000 / 579903) ∧
    -Real.log (500000 / 579903) ≤ (593011 / 4000000) := by
  have h := checkLog_sound (w := (79903 / 1079903)) (n := 12)
    (lo := (148252749 / 1000000000)) (hi := (593011 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579903 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579903 / 500000) = 1/(500000 / 579903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (148252749 / 1000000000) (593011 / 4000000) (Real.log (579903 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (579903 / 500000) = -Real.log (500000 / 579903) := by
    rw [show ((579903 / 500000) : ℝ) = ((500000 / 579903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174122461 / 1000000000) ≤ -Real.log (420097 / 500000) ∧
    -Real.log (420097 / 500000) ≤ (87061231 / 500000000) := by
  have h := checkLog_sound (w := (79903 / 920097)) (n := 12)
    (lo := (174122461 / 1000000000)) (hi := (87061231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420097) = 1/(420097 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87061231 / 500000000) (-174122461 / 1000000000) (Real.log (420097 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (129671847 / 200000000) ≤ -Real.log (500000000000 / 956200227531) ∧
    -Real.log (500000000000 / 956200227531) ≤ (162089809 / 250000000) := by
  have h := checkLog_sound (w := (456200227531 / 1456200227531)) (n := 12)
    (lo := (129671847 / 200000000)) (hi := (162089809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956200227531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956200227531 / 500000000000) = 1/(500000000000 / 956200227531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (129671847 / 200000000) (162089809 / 250000000) (Real.log (956200227531 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (956200227531 / 500000000000) = -Real.log (500000000000 / 956200227531) := by
    rw [show ((956200227531 / 500000000000) : ℝ) = ((500000000000 / 956200227531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (129931781 / 200000000) ≤ -Real.log (100000000000 / 191488756049) ∧
    -Real.log (100000000000 / 191488756049) ≤ (324829453 / 500000000) := by
  have h := checkLog_sound (w := (91488756049 / 291488756049)) (n := 12)
    (lo := (129931781 / 200000000)) (hi := (324829453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191488756049 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191488756049 / 100000000000) = 1/(100000000000 / 191488756049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (129931781 / 200000000) (324829453 / 500000000) (Real.log (191488756049 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (191488756049 / 100000000000) = -Real.log (100000000000 / 191488756049) := by
    rw [show ((191488756049 / 100000000000) : ℝ) = ((100000000000 / 191488756049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22625007 / 50000000) ≤ -Real.log (500000000000 / 786119045751) ∧
    -Real.log (500000000000 / 786119045751) ≤ (452500141 / 1000000000) := by
  have h := checkLog_sound (w := (286119045751 / 1286119045751)) (n := 12)
    (lo := (22625007 / 50000000)) (hi := (452500141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786119045751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786119045751 / 500000000000) = 1/(500000000000 / 786119045751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22625007 / 50000000) (452500141 / 1000000000) (Real.log (786119045751 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (786119045751 / 500000000000) = -Real.log (500000000000 / 786119045751) := by
    rw [show ((786119045751 / 500000000000) : ℝ) = ((500000000000 / 786119045751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (453386069 / 1000000000) ≤ -Real.log (12500000000 / 19670395001) ∧
    -Real.log (12500000000 / 19670395001) ≤ (45338607 / 100000000) := by
  have h := checkLog_sound (w := (7170395001 / 32170395001)) (n := 12)
    (lo := (453386069 / 1000000000)) (hi := (45338607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19670395001 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19670395001 / 12500000000) = 1/(12500000000 / 19670395001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (453386069 / 1000000000) (45338607 / 100000000) (Real.log (19670395001 / 12500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (19670395001 / 12500000000) = -Real.log (12500000000 / 19670395001) := by
    rw [show ((19670395001 / 12500000000) : ℝ) = ((12500000000 / 19670395001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (160868471 / 500000000) ≤ -Real.log (500000000000 / 689760917543) ∧
    -Real.log (500000000000 / 689760917543) ≤ (321736943 / 1000000000) := by
  have h := checkLog_sound (w := (189760917543 / 1189760917543)) (n := 12)
    (lo := (160868471 / 500000000)) (hi := (321736943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689760917543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689760917543 / 500000000000) = 1/(500000000000 / 689760917543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (160868471 / 500000000) (321736943 / 1000000000) (Real.log (689760917543 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (689760917543 / 500000000000) = -Real.log (500000000000 / 689760917543) := by
    rw [show ((689760917543 / 500000000000) : ℝ) = ((500000000000 / 689760917543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (322375211 / 1000000000) ≤ -Real.log (10000000000 / 13804026213) ∧
    -Real.log (10000000000 / 13804026213) ≤ (80593803 / 250000000) := by
  have h := checkLog_sound (w := (3804026213 / 23804026213)) (n := 12)
    (lo := (322375211 / 1000000000)) (hi := (80593803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13804026213 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13804026213 / 10000000000) = 1/(10000000000 / 13804026213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (322375211 / 1000000000) (80593803 / 250000000) (Real.log (13804026213 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13804026213 / 10000000000) = -Real.log (10000000000 / 13804026213) := by
    rw [show ((13804026213 / 10000000000) : ℝ) = ((10000000000 / 13804026213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25869711 / 1000000000) ≤ -Real.log (243615510591 / 250000000000) ∧
    -Real.log (243615510591 / 250000000000) ≤ (1616857 / 62500000) := by
  have h := checkLog_sound (w := (6384489409 / 493615510591)) (n := 12)
    (lo := (25869711 / 1000000000)) (hi := (1616857 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243615510591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243615510591) = 1/(243615510591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1616857 / 62500000) (-25869711 / 1000000000) (Real.log (243615510591 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (25767811 / 1000000000) ≤ -Real.log (38982453799 / 40000000000) ∧
    -Real.log (38982453799 / 40000000000) ≤ (6441953 / 250000000) := by
  have h := checkLog_sound (w := (1017546201 / 78982453799)) (n := 12)
    (lo := (25767811 / 1000000000)) (hi := (6441953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38982453799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38982453799) = 1/(38982453799 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6441953 / 250000000) (-25767811 / 1000000000) (Real.log (38982453799 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell108

end


