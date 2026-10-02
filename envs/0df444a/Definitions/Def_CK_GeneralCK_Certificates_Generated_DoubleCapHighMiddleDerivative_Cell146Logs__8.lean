-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell146Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell146Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:57:34.643929+00:00
-- url     : https://prove2.me/theorems/83b83d04-88ad-44a8-9589-e2356d2a851b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell146Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell147…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell146Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell147Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell148Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell149Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell150Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell151Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell152Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell153Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell146Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell147Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell148Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell149Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell150Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell151Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell152Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell153Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell146Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell147Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell148Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell149Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell150Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell151Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell152Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell153Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell146Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell147Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell148Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell149Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell150Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell151Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell152Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell153Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell146Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell146
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

theorem reflection_log_1_neg : (7244487 / 25000000) ≤ -Real.log (5120 / 6841) ∧
    -Real.log (5120 / 6841) ≤ (289779481 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 11961)) (n := 12)
    (lo := (7244487 / 25000000)) (hi := (289779481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6841 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6841 / 5120) = 1/(5120 / 6841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (7244487 / 25000000) (289779481 / 1000000000) (Real.log (6841 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6841 / 5120) = -Real.log (5120 / 6841) := by
    rw [show ((6841 / 5120) : ℝ) = ((5120 / 6841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (25604573 / 62500000) ≤ -Real.log (3399 / 5120) ∧
    -Real.log (3399 / 5120) ≤ (409673169 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 8519)) (n := 12)
    (lo := (25604573 / 62500000)) (hi := (409673169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3399) = 1/(3399 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-409673169 / 1000000000) (-25604573 / 62500000) (Real.log (3399 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (72335213 / 250000000) ≤ -Real.log (2560 / 3419) ∧
    -Real.log (2560 / 3419) ≤ (289340853 / 1000000000) := by
  have h := checkLog_sound (w := (859 / 5979)) (n := 12)
    (lo := (72335213 / 250000000)) (hi := (289340853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3419 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3419 / 2560) = 1/(2560 / 3419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (72335213 / 250000000) (289340853 / 1000000000) (Real.log (3419 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3419 / 2560) = -Real.log (2560 / 3419) := by
    rw [show ((3419 / 2560) : ℝ) = ((2560 / 3419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (81758189 / 200000000) ≤ -Real.log (1701 / 2560) ∧
    -Real.log (1701 / 2560) ≤ (204395473 / 500000000) := by
  have h := checkLog_sound (w := (859 / 4261)) (n := 12)
    (lo := (81758189 / 200000000)) (hi := (204395473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1701) = 1/(1701 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-204395473 / 500000000) (-81758189 / 200000000) (Real.log (1701 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21384687 / 100000000) ≤ -Real.log (1000000 / 1238433) ∧
    -Real.log (1000000 / 1238433) ≤ (213846871 / 1000000000) := by
  have h := checkLog_sound (w := (238433 / 2238433)) (n := 12)
    (lo := (21384687 / 100000000)) (hi := (213846871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238433 / 1000000) = 1/(1000000 / 1238433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21384687 / 100000000) (213846871 / 1000000000) (Real.log (1238433 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1238433 / 1000000) = -Real.log (1000000 / 1238433) := by
    rw [show ((1238433 / 1000000) : ℝ) = ((1000000 / 1238433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (136188563 / 500000000) ≤ -Real.log (761567 / 1000000) ∧
    -Real.log (761567 / 1000000) ≤ (272377127 / 1000000000) := by
  have h := checkLog_sound (w := (238433 / 1761567)) (n := 12)
    (lo := (136188563 / 500000000)) (hi := (272377127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761567) = 1/(761567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-272377127 / 1000000000) (-136188563 / 500000000) (Real.log (761567 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10709459 / 50000000) ≤ -Real.log (1000000 / 1238857) ∧
    -Real.log (1000000 / 1238857) ≤ (214189181 / 1000000000) := by
  have h := checkLog_sound (w := (238857 / 2238857)) (n := 12)
    (lo := (10709459 / 50000000)) (hi := (214189181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238857 / 1000000) = 1/(1000000 / 1238857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10709459 / 50000000) (214189181 / 1000000000) (Real.log (1238857 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1238857 / 1000000) = -Real.log (1000000 / 1238857) := by
    rw [show ((1238857 / 1000000) : ℝ) = ((1000000 / 1238857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68233507 / 250000000) ≤ -Real.log (761143 / 1000000) ∧
    -Real.log (761143 / 1000000) ≤ (272934029 / 1000000000) := by
  have h := checkLog_sound (w := (238857 / 1761143)) (n := 12)
    (lo := (68233507 / 250000000)) (hi := (272934029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761143) = 1/(761143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-272934029 / 1000000000) (-68233507 / 250000000) (Real.log (761143 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (158111681 / 1000000000) ≤ -Real.log (1000000 / 1171297) ∧
    -Real.log (1000000 / 1171297) ≤ (79055841 / 500000000) := by
  have h := checkLog_sound (w := (171297 / 2171297)) (n := 12)
    (lo := (158111681 / 1000000000)) (hi := (79055841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1171297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1171297 / 1000000) = 1/(1000000 / 1171297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (158111681 / 1000000000) (79055841 / 500000000) (Real.log (1171297 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1171297 / 1000000) = -Real.log (1000000 / 1171297) := by
    rw [show ((1171297 / 1000000) : ℝ) = ((1000000 / 1171297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (187893451 / 1000000000) ≤ -Real.log (828703 / 1000000) ∧
    -Real.log (828703 / 1000000) ≤ (46973363 / 250000000) := by
  have h := checkLog_sound (w := (171297 / 1828703)) (n := 12)
    (lo := (187893451 / 1000000000)) (hi := (46973363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 828703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 828703) = 1/(828703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-46973363 / 250000000) (-187893451 / 1000000000) (Real.log (828703 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (158378871 / 1000000000) ≤ -Real.log (100000 / 117161) ∧
    -Real.log (100000 / 117161) ≤ (19797359 / 125000000) := by
  have h := checkLog_sound (w := (17161 / 217161)) (n := 12)
    (lo := (158378871 / 1000000000)) (hi := (19797359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117161 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117161 / 100000) = 1/(100000 / 117161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (158378871 / 1000000000) (19797359 / 125000000) (Real.log (117161 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (117161 / 100000) = -Real.log (100000 / 117161) := by
    rw [show ((117161 / 100000) : ℝ) = ((100000 / 117161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (9413561 / 50000000) ≤ -Real.log (82839 / 100000) ∧
    -Real.log (82839 / 100000) ≤ (188271221 / 1000000000) := by
  have h := checkLog_sound (w := (17161 / 182839)) (n := 12)
    (lo := (9413561 / 50000000)) (hi := (188271221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82839) = 1/(82839 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-188271221 / 1000000000) (-9413561 / 50000000) (Real.log (82839 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (174532949 / 250000000) ≤ -Real.log (62500000000 / 125624632569) ∧
    -Real.log (62500000000 / 125624632569) ≤ (349065899 / 500000000) := by
  have h := checkLog_sound (w := (624632569 / 250624632569)) (n := 12)
    (lo := (623077 / 125000000)) (hi := (4984617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125624632569 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125624632569 / 125000000000) = 1/(62500000000 / 125624632569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (174532949 / 250000000) (349065899 / 500000000) (Real.log (125624632569 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (125624632569 / 62500000000) = -Real.log (62500000000 / 125624632569) := by
    rw [show ((125624632569 / 62500000000) : ℝ) = ((62500000000 / 125624632569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (87431581 / 125000000) ≤ -Real.log (500000000000 / 1006325389821) ∧
    -Real.log (500000000000 / 1006325389821) ≤ (13989053 / 20000000) := by
  have h := checkLog_sound (w := (6325389821 / 2006325389821)) (n := 12)
    (lo := (1576367 / 250000000)) (hi := (6305469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006325389821 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1006325389821 / 1000000000000) = 1/(500000000000 / 1006325389821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (87431581 / 125000000) (13989053 / 20000000) (Real.log (1006325389821 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1006325389821 / 500000000000) = -Real.log (500000000000 / 1006325389821) := by
    rw [show ((1006325389821 / 500000000000) : ℝ) = ((500000000000 / 1006325389821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (486223997 / 1000000000) ≤ -Real.log (50000000000 / 81308210571) ∧
    -Real.log (50000000000 / 81308210571) ≤ (243111999 / 500000000) := by
  have h := checkLog_sound (w := (31308210571 / 131308210571)) (n := 12)
    (lo := (486223997 / 1000000000)) (hi := (243111999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81308210571 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81308210571 / 50000000000) = 1/(50000000000 / 81308210571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (486223997 / 1000000000) (243111999 / 500000000) (Real.log (81308210571 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (81308210571 / 50000000000) = -Real.log (50000000000 / 81308210571) := by
    rw [show ((81308210571 / 50000000000) : ℝ) = ((50000000000 / 81308210571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (60890401 / 125000000) ≤ -Real.log (125000000000 / 203453391807) ∧
    -Real.log (125000000000 / 203453391807) ≤ (487123209 / 1000000000) := by
  have h := checkLog_sound (w := (78453391807 / 328453391807)) (n := 12)
    (lo := (60890401 / 125000000)) (hi := (487123209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203453391807 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203453391807 / 125000000000) = 1/(125000000000 / 203453391807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (60890401 / 125000000) (487123209 / 1000000000) (Real.log (203453391807 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (203453391807 / 125000000000) = -Real.log (125000000000 / 203453391807) := by
    rw [show ((203453391807 / 125000000000) : ℝ) = ((125000000000 / 203453391807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (86501283 / 250000000) ≤ -Real.log (250000000000 / 353352467651) ∧
    -Real.log (250000000000 / 353352467651) ≤ (346005133 / 1000000000) := by
  have h := checkLog_sound (w := (103352467651 / 603352467651)) (n := 12)
    (lo := (86501283 / 250000000)) (hi := (346005133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353352467651 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353352467651 / 250000000000) = 1/(250000000000 / 353352467651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (86501283 / 250000000) (346005133 / 1000000000) (Real.log (353352467651 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (353352467651 / 250000000000) = -Real.log (250000000000 / 353352467651) := by
    rw [show ((353352467651 / 250000000000) : ℝ) = ((250000000000 / 353352467651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (86662523 / 250000000) ≤ -Real.log (500000000000 / 707160878331) ∧
    -Real.log (500000000000 / 707160878331) ≤ (346650093 / 1000000000) := by
  have h := checkLog_sound (w := (207160878331 / 1207160878331)) (n := 12)
    (lo := (86662523 / 250000000)) (hi := (346650093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707160878331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707160878331 / 500000000000) = 1/(500000000000 / 707160878331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (86662523 / 250000000) (346650093 / 1000000000) (Real.log (707160878331 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (707160878331 / 500000000000) = -Real.log (500000000000 / 707160878331) := by
    rw [show ((707160878331 / 500000000000) : ℝ) = ((500000000000 / 707160878331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (29892349 / 1000000000) ≤ -Real.log (9705500079 / 10000000000) ∧
    -Real.log (9705500079 / 10000000000) ≤ (597847 / 20000000) := by
  have h := checkLog_sound (w := (294499921 / 19705500079)) (n := 12)
    (lo := (29892349 / 1000000000)) (hi := (597847 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9705500079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9705500079) = 1/(9705500079 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-597847 / 20000000) (-29892349 / 1000000000) (Real.log (9705500079 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (29781769 / 1000000000) ≤ -Real.log (970657337791 / 1000000000000) ∧
    -Real.log (970657337791 / 1000000000000) ≤ (2978177 / 100000000) := by
  have h := checkLog_sound (w := (29342662209 / 1970657337791)) (n := 12)
    (lo := (29781769 / 1000000000)) (hi := (2978177 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970657337791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970657337791) = 1/(970657337791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2978177 / 100000000) (-29781769 / 1000000000) (Real.log (970657337791 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell146

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell147Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell147
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

theorem reflection_log_1_neg : (72554479 / 250000000) ≤ -Real.log (1280 / 1711) ∧
    -Real.log (1280 / 1711) ≤ (290217917 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2991)) (n := 12)
    (lo := (72554479 / 250000000)) (hi := (290217917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1711 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1711 / 1280) = 1/(1280 / 1711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (72554479 / 250000000) (290217917 / 1000000000) (Real.log (1711 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1711 / 1280) = -Real.log (1280 / 1711) := by
    rw [show ((1711 / 1280) : ℝ) = ((1280 / 1711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (41055617 / 100000000) ≤ -Real.log (849 / 1280) ∧
    -Real.log (849 / 1280) ≤ (410556171 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2129)) (n := 12)
    (lo := (41055617 / 100000000)) (hi := (410556171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 849) = 1/(849 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-410556171 / 1000000000) (-41055617 / 100000000) (Real.log (849 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (7244487 / 25000000) ≤ -Real.log (5120 / 6841) ∧
    -Real.log (5120 / 6841) ≤ (289779481 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 11961)) (n := 12)
    (lo := (7244487 / 25000000)) (hi := (289779481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6841 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6841 / 5120) = 1/(5120 / 6841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (7244487 / 25000000) (289779481 / 1000000000) (Real.log (6841 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6841 / 5120) = -Real.log (5120 / 6841) := by
    rw [show ((6841 / 5120) : ℝ) = ((5120 / 6841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (25604573 / 62500000) ≤ -Real.log (3399 / 5120) ∧
    -Real.log (3399 / 5120) ≤ (409673169 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 8519)) (n := 12)
    (lo := (25604573 / 62500000)) (hi := (409673169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3399) = 1/(3399 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-409673169 / 1000000000) (-25604573 / 62500000) (Real.log (3399 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (214188373 / 1000000000) ≤ -Real.log (125000 / 154857) ∧
    -Real.log (125000 / 154857) ≤ (107094187 / 500000000) := by
  have h := checkLog_sound (w := (29857 / 279857)) (n := 12)
    (lo := (214188373 / 1000000000)) (hi := (107094187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154857 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154857 / 125000) = 1/(125000 / 154857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (214188373 / 1000000000) (107094187 / 500000000) (Real.log (154857 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (154857 / 125000) = -Real.log (125000 / 154857) := by
    rw [show ((154857 / 125000) : ℝ) = ((125000 / 154857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (136466357 / 500000000) ≤ -Real.log (95143 / 125000) ∧
    -Real.log (95143 / 125000) ≤ (54586543 / 200000000) := by
  have h := checkLog_sound (w := (29857 / 220143)) (n := 12)
    (lo := (136466357 / 500000000)) (hi := (54586543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95143) = 1/(95143 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-54586543 / 200000000) (-136466357 / 500000000) (Real.log (95143 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (214528951 / 1000000000) ≤ -Real.log (500000 / 619639) ∧
    -Real.log (500000 / 619639) ≤ (26816119 / 125000000) := by
  have h := checkLog_sound (w := (119639 / 1119639)) (n := 12)
    (lo := (214528951 / 1000000000)) (hi := (26816119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619639 / 500000) = 1/(500000 / 619639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (214528951 / 1000000000) (26816119 / 125000000) (Real.log (619639 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (619639 / 500000) = -Real.log (500000 / 619639) := by
    rw [show ((619639 / 500000) : ℝ) = ((500000 / 619639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4273239 / 15625000) ≤ -Real.log (380361 / 500000) ∧
    -Real.log (380361 / 500000) ≤ (273487297 / 1000000000) := by
  have h := checkLog_sound (w := (119639 / 880361)) (n := 12)
    (lo := (4273239 / 15625000)) (hi := (273487297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380361) = 1/(380361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-273487297 / 1000000000) (-4273239 / 15625000) (Real.log (380361 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (158378017 / 1000000000) ≤ -Real.log (1000000 / 1171609) ∧
    -Real.log (1000000 / 1171609) ≤ (79189009 / 500000000) := by
  have h := checkLog_sound (w := (171609 / 2171609)) (n := 12)
    (lo := (158378017 / 1000000000)) (hi := (79189009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1171609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1171609 / 1000000) = 1/(1000000 / 1171609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (158378017 / 1000000000) (79189009 / 500000000) (Real.log (1171609 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1171609 / 1000000) = -Real.log (1000000 / 1171609) := by
    rw [show ((1171609 / 1000000) : ℝ) = ((1000000 / 1171609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (188270013 / 1000000000) ≤ -Real.log (828391 / 1000000) ∧
    -Real.log (828391 / 1000000) ≤ (94135007 / 500000000) := by
  have h := checkLog_sound (w := (171609 / 1828391)) (n := 12)
    (lo := (188270013 / 1000000000)) (hi := (94135007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 828391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 828391) = 1/(828391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-94135007 / 500000000) (-188270013 / 1000000000) (Real.log (828391 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9915321 / 62500000) ≤ -Real.log (500000 / 585961) ∧
    -Real.log (500000 / 585961) ≤ (158645137 / 1000000000) := by
  have h := checkLog_sound (w := (85961 / 1085961)) (n := 12)
    (lo := (9915321 / 62500000)) (hi := (158645137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585961 / 500000) = 1/(500000 / 585961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9915321 / 62500000) (158645137 / 1000000000) (Real.log (585961 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (585961 / 500000) = -Real.log (500000 / 585961) := by
    rw [show ((585961 / 500000) : ℝ) = ((500000 / 585961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (94323963 / 500000000) ≤ -Real.log (414039 / 500000) ∧
    -Real.log (414039 / 500000) ≤ (188647927 / 1000000000) := by
  have h := checkLog_sound (w := (85961 / 914039)) (n := 12)
    (lo := (94323963 / 500000000)) (hi := (188647927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414039) = 1/(414039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-188647927 / 1000000000) (-94323963 / 500000000) (Real.log (414039 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (87431581 / 125000000) ≤ -Real.log (25000000000 / 50316269491) ∧
    -Real.log (25000000000 / 50316269491) ≤ (13989053 / 20000000) := by
  have h := checkLog_sound (w := (316269491 / 100316269491)) (n := 12)
    (lo := (1576367 / 250000000)) (hi := (6305469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50316269491 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50316269491 / 50000000000) = 1/(25000000000 / 50316269491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (87431581 / 125000000) (13989053 / 20000000) (Real.log (50316269491 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (50316269491 / 25000000000) = -Real.log (25000000000 / 50316269491) := by
    rw [show ((50316269491 / 25000000000) : ℝ) = ((25000000000 / 50316269491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (700774087 / 1000000000) ≤ -Real.log (12500000000 / 25191401649) ∧
    -Real.log (12500000000 / 25191401649) ≤ (700774089 / 1000000000) := by
  have h := checkLog_sound (w := (191401649 / 50191401649)) (n := 12)
    (lo := (7626907 / 1000000000)) (hi := (1906727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25191401649 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25191401649 / 25000000000) = 1/(12500000000 / 25191401649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (700774087 / 1000000000) (700774089 / 1000000000) (Real.log (25191401649 / 12500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (25191401649 / 12500000000) = -Real.log (12500000000 / 25191401649) := by
    rw [show ((25191401649 / 12500000000) : ℝ) = ((12500000000 / 25191401649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (487121087 / 1000000000) ≤ -Real.log (500000000000 / 813811841123) ∧
    -Real.log (500000000000 / 813811841123) ≤ (7611267 / 15625000) := by
  have h := checkLog_sound (w := (313811841123 / 1313811841123)) (n := 12)
    (lo := (487121087 / 1000000000)) (hi := (7611267 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813811841123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813811841123 / 500000000000) = 1/(500000000000 / 813811841123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (487121087 / 1000000000) (7611267 / 15625000) (Real.log (813811841123 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (813811841123 / 500000000000) = -Real.log (500000000000 / 813811841123) := by
    rw [show ((813811841123 / 500000000000) : ℝ) = ((500000000000 / 813811841123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61002031 / 125000000) ≤ -Real.log (250000000000 / 407270330029) ∧
    -Real.log (250000000000 / 407270330029) ≤ (488016249 / 1000000000) := by
  have h := checkLog_sound (w := (157270330029 / 657270330029)) (n := 12)
    (lo := (61002031 / 125000000)) (hi := (488016249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407270330029 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407270330029 / 250000000000) = 1/(250000000000 / 407270330029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (61002031 / 125000000) (488016249 / 1000000000) (Real.log (407270330029 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (407270330029 / 250000000000) = -Real.log (250000000000 / 407270330029) := by
    rw [show ((407270330029 / 250000000000) : ℝ) = ((250000000000 / 407270330029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (346648031 / 1000000000) ≤ -Real.log (250000000000 / 353579710547) ∧
    -Real.log (250000000000 / 353579710547) ≤ (10832751 / 31250000) := by
  have h := checkLog_sound (w := (103579710547 / 603579710547)) (n := 12)
    (lo := (346648031 / 1000000000)) (hi := (10832751 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353579710547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353579710547 / 250000000000) = 1/(250000000000 / 353579710547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (346648031 / 1000000000) (10832751 / 31250000) (Real.log (353579710547 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (353579710547 / 250000000000) = -Real.log (250000000000 / 353579710547) := by
    rw [show ((353579710547 / 250000000000) : ℝ) = ((250000000000 / 353579710547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (173646531 / 500000000) ≤ -Real.log (5000000000 / 7076157077) ∧
    -Real.log (5000000000 / 7076157077) ≤ (347293063 / 1000000000) := by
  have h := checkLog_sound (w := (2076157077 / 12076157077)) (n := 12)
    (lo := (173646531 / 500000000)) (hi := (347293063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7076157077 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7076157077 / 5000000000) = 1/(5000000000 / 7076157077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (173646531 / 500000000) (347293063 / 1000000000) (Real.log (7076157077 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7076157077 / 5000000000) = -Real.log (5000000000 / 7076157077) := by
    rw [show ((7076157077 / 5000000000) : ℝ) = ((5000000000 / 7076157077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3000279 / 100000000) ≤ -Real.log (242610706479 / 250000000000) ∧
    -Real.log (242610706479 / 250000000000) ≤ (30002791 / 1000000000) := by
  have h := checkLog_sound (w := (7389293521 / 492610706479)) (n := 12)
    (lo := (3000279 / 100000000)) (hi := (30002791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242610706479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242610706479) = 1/(242610706479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-30002791 / 1000000000) (-3000279 / 100000000) (Real.log (242610706479 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7472999 / 250000000) ≤ -Real.log (970550351119 / 1000000000000) ∧
    -Real.log (970550351119 / 1000000000000) ≤ (29891997 / 1000000000) := by
  have h := checkLog_sound (w := (29449648881 / 1970550351119)) (n := 12)
    (lo := (7472999 / 250000000)) (hi := (29891997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970550351119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970550351119) = 1/(970550351119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-29891997 / 1000000000) (-7472999 / 250000000) (Real.log (970550351119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell147

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell148Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell148
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

theorem reflection_log_1_neg : (290656161 / 1000000000) ≤ -Real.log (5120 / 6847) ∧
    -Real.log (5120 / 6847) ≤ (145328081 / 500000000) := by
  have h := checkLog_sound (w := (1727 / 11967)) (n := 12)
    (lo := (290656161 / 1000000000)) (hi := (145328081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6847 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6847 / 5120) = 1/(5120 / 6847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (290656161 / 1000000000) (145328081 / 500000000) (Real.log (6847 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6847 / 5120) = -Real.log (5120 / 6847) := by
    rw [show ((6847 / 5120) : ℝ) = ((5120 / 6847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (411439953 / 1000000000) ≤ -Real.log (3393 / 5120) ∧
    -Real.log (3393 / 5120) ≤ (205719977 / 500000000) := by
  have h := checkLog_sound (w := (1727 / 8513)) (n := 12)
    (lo := (411439953 / 1000000000)) (hi := (205719977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3393) = 1/(3393 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-205719977 / 500000000) (-411439953 / 1000000000) (Real.log (3393 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (72554479 / 250000000) ≤ -Real.log (1280 / 1711) ∧
    -Real.log (1280 / 1711) ≤ (290217917 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2991)) (n := 12)
    (lo := (72554479 / 250000000)) (hi := (290217917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1711 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1711 / 1280) = 1/(1280 / 1711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (72554479 / 250000000) (290217917 / 1000000000) (Real.log (1711 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1711 / 1280) = -Real.log (1280 / 1711) := by
    rw [show ((1711 / 1280) : ℝ) = ((1280 / 1711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (41055617 / 100000000) ≤ -Real.log (849 / 1280) ∧
    -Real.log (849 / 1280) ≤ (410556171 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2129)) (n := 12)
    (lo := (41055617 / 100000000)) (hi := (410556171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 849) = 1/(849 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-410556171 / 1000000000) (-41055617 / 100000000) (Real.log (849 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42905629 / 200000000) ≤ -Real.log (1000000 / 1239277) ∧
    -Real.log (1000000 / 1239277) ≤ (107264073 / 500000000) := by
  have h := checkLog_sound (w := (239277 / 2239277)) (n := 12)
    (lo := (42905629 / 200000000)) (hi := (107264073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239277 / 1000000) = 1/(1000000 / 1239277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42905629 / 200000000) (107264073 / 500000000) (Real.log (1239277 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1239277 / 1000000) = -Real.log (1000000 / 1239277) := by
    rw [show ((1239277 / 1000000) : ℝ) = ((1000000 / 1239277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (136742991 / 500000000) ≤ -Real.log (760723 / 1000000) ∧
    -Real.log (760723 / 1000000) ≤ (273485983 / 1000000000) := by
  have h := checkLog_sound (w := (239277 / 1760723)) (n := 12)
    (lo := (136742991 / 500000000)) (hi := (273485983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760723) = 1/(760723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-273485983 / 1000000000) (-136742991 / 500000000) (Real.log (760723 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (214867801 / 1000000000) ≤ -Real.log (500000 / 619849) ∧
    -Real.log (500000 / 619849) ≤ (107433901 / 500000000) := by
  have h := checkLog_sound (w := (119849 / 1119849)) (n := 12)
    (lo := (214867801 / 1000000000)) (hi := (107433901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619849 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619849 / 500000) = 1/(500000 / 619849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (214867801 / 1000000000) (107433901 / 500000000) (Real.log (619849 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (619849 / 500000) = -Real.log (500000 / 619849) := by
    rw [show ((619849 / 500000) : ℝ) = ((500000 / 619849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68509889 / 250000000) ≤ -Real.log (380151 / 500000) ∧
    -Real.log (380151 / 500000) ≤ (274039557 / 1000000000) := by
  have h := checkLog_sound (w := (119849 / 880151)) (n := 12)
    (lo := (68509889 / 250000000)) (hi := (274039557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380151) = 1/(380151 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-274039557 / 1000000000) (-68509889 / 250000000) (Real.log (380151 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79322141 / 500000000) ≤ -Real.log (1000000 / 1171921) ∧
    -Real.log (1000000 / 1171921) ≤ (158644283 / 1000000000) := by
  have h := checkLog_sound (w := (171921 / 2171921)) (n := 12)
    (lo := (79322141 / 500000000)) (hi := (158644283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1171921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1171921 / 1000000) = 1/(1000000 / 1171921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79322141 / 500000000) (158644283 / 1000000000) (Real.log (1171921 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1171921 / 1000000) = -Real.log (1000000 / 1171921) := by
    rw [show ((1171921 / 1000000) : ℝ) = ((1000000 / 1171921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (94323359 / 500000000) ≤ -Real.log (828079 / 1000000) ∧
    -Real.log (828079 / 1000000) ≤ (188646719 / 1000000000) := by
  have h := checkLog_sound (w := (171921 / 1828079)) (n := 12)
    (lo := (94323359 / 500000000)) (hi := (188646719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 828079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 828079) = 1/(828079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-188646719 / 1000000000) (-94323359 / 500000000) (Real.log (828079 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (158911329 / 1000000000) ≤ -Real.log (500000 / 586117) ∧
    -Real.log (500000 / 586117) ≤ (15891133 / 100000000) := by
  have h := checkLog_sound (w := (86117 / 1086117)) (n := 12)
    (lo := (158911329 / 1000000000)) (hi := (15891133 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586117 / 500000) = 1/(500000 / 586117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (158911329 / 1000000000) (15891133 / 100000000) (Real.log (586117 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (586117 / 500000) = -Real.log (500000 / 586117) := by
    rw [show ((586117 / 500000) : ℝ) = ((500000 / 586117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (189024773 / 1000000000) ≤ -Real.log (413883 / 500000) ∧
    -Real.log (413883 / 500000) ≤ (94512387 / 500000000) := by
  have h := checkLog_sound (w := (86117 / 913883)) (n := 12)
    (lo := (189024773 / 1000000000)) (hi := (94512387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413883) = 1/(413883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-94512387 / 500000000) (-189024773 / 1000000000) (Real.log (413883 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (700774087 / 1000000000) ≤ -Real.log (500000000000 / 1007656065959) ∧
    -Real.log (500000000000 / 1007656065959) ≤ (700774089 / 1000000000) := by
  have h := checkLog_sound (w := (7656065959 / 2007656065959)) (n := 12)
    (lo := (7626907 / 1000000000)) (hi := (1906727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1007656065959 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1007656065959 / 1000000000000) = 1/(500000000000 / 1007656065959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (700774087 / 1000000000) (700774089 / 1000000000) (Real.log (1007656065959 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1007656065959 / 500000000000) = -Real.log (500000000000 / 1007656065959) := by
    rw [show ((1007656065959 / 500000000000) : ℝ) = ((500000000000 / 1007656065959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (702096113 / 1000000000) ≤ -Real.log (125000000000 / 252247273799) ∧
    -Real.log (125000000000 / 252247273799) ≤ (140419223 / 200000000) := by
  have h := checkLog_sound (w := (2247273799 / 502247273799)) (n := 12)
    (lo := (8948933 / 1000000000)) (hi := (4474467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252247273799 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(252247273799 / 250000000000) = 1/(125000000000 / 252247273799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (702096113 / 1000000000) (140419223 / 200000000) (Real.log (252247273799 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (252247273799 / 125000000000) = -Real.log (125000000000 / 252247273799) := by
    rw [show ((252247273799 / 125000000000) : ℝ) = ((125000000000 / 252247273799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (488014127 / 1000000000) ≤ -Real.log (250000000000 / 407269466021) ∧
    -Real.log (250000000000 / 407269466021) ≤ (30500883 / 62500000) := by
  have h := checkLog_sound (w := (157269466021 / 657269466021)) (n := 12)
    (lo := (488014127 / 1000000000)) (hi := (30500883 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407269466021 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407269466021 / 250000000000) = 1/(250000000000 / 407269466021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (488014127 / 1000000000) (30500883 / 62500000) (Real.log (407269466021 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (407269466021 / 250000000000) = -Real.log (250000000000 / 407269466021) := by
    rw [show ((407269466021 / 250000000000) : ℝ) = ((250000000000 / 407269466021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (488907357 / 1000000000) ≤ -Real.log (250000000000 / 407633414091) ∧
    -Real.log (250000000000 / 407633414091) ≤ (244453679 / 500000000) := by
  have h := checkLog_sound (w := (157633414091 / 657633414091)) (n := 12)
    (lo := (488907357 / 1000000000)) (hi := (244453679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407633414091 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407633414091 / 250000000000) = 1/(250000000000 / 407633414091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (488907357 / 1000000000) (244453679 / 500000000) (Real.log (407633414091 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (407633414091 / 250000000000) = -Real.log (250000000000 / 407633414091) := by
    rw [show ((407633414091 / 250000000000) : ℝ) = ((250000000000 / 407633414091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (347291001 / 1000000000) ≤ -Real.log (100000000000 / 141522849873) ∧
    -Real.log (100000000000 / 141522849873) ≤ (173645501 / 500000000) := by
  have h := checkLog_sound (w := (41522849873 / 241522849873)) (n := 12)
    (lo := (347291001 / 1000000000)) (hi := (173645501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141522849873 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141522849873 / 100000000000) = 1/(100000000000 / 141522849873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (347291001 / 1000000000) (173645501 / 500000000) (Real.log (141522849873 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (141522849873 / 100000000000) = -Real.log (100000000000 / 141522849873) := by
    rw [show ((141522849873 / 100000000000) : ℝ) = ((100000000000 / 141522849873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (347936103 / 1000000000) ≤ -Real.log (100000000000 / 141614175987) ∧
    -Real.log (100000000000 / 141614175987) ≤ (43492013 / 125000000) := by
  have h := checkLog_sound (w := (41614175987 / 241614175987)) (n := 12)
    (lo := (347936103 / 1000000000)) (hi := (43492013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141614175987 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141614175987 / 100000000000) = 1/(100000000000 / 141614175987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (347936103 / 1000000000) (43492013 / 125000000) (Real.log (141614175987 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (141614175987 / 100000000000) = -Real.log (100000000000 / 141614175987) := by
    rw [show ((141614175987 / 100000000000) : ℝ) = ((100000000000 / 141614175987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (30113443 / 1000000000) ≤ -Real.log (242583862311 / 250000000000) ∧
    -Real.log (242583862311 / 250000000000) ≤ (7528361 / 250000000) := by
  have h := checkLog_sound (w := (7416137689 / 492583862311)) (n := 12)
    (lo := (30113443 / 1000000000)) (hi := (7528361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242583862311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242583862311) = 1/(242583862311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-7528361 / 250000000) (-30113443 / 1000000000) (Real.log (242583862311 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6000487 / 200000000) ≤ -Real.log (970443169759 / 1000000000000) ∧
    -Real.log (970443169759 / 1000000000000) ≤ (7500609 / 250000000) := by
  have h := checkLog_sound (w := (29556830241 / 1970443169759)) (n := 12)
    (lo := (6000487 / 200000000)) (hi := (7500609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970443169759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970443169759) = 1/(970443169759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7500609 / 250000000) (-6000487 / 200000000) (Real.log (970443169759 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell148

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell149Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell149
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

theorem reflection_log_1_neg : (291094213 / 1000000000) ≤ -Real.log (512 / 685) ∧
    -Real.log (512 / 685) ≤ (145547107 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1197)) (n := 12)
    (lo := (291094213 / 1000000000)) (hi := (145547107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685 / 512) = 1/(512 / 685) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (291094213 / 1000000000) (145547107 / 500000000) (Real.log (685 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (685 / 512) = -Real.log (512 / 685) := by
    rw [show ((685 / 512) : ℝ) = ((512 / 685) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (412324517 / 1000000000) ≤ -Real.log (339 / 512) ∧
    -Real.log (339 / 512) ≤ (206162259 / 500000000) := by
  have h := checkLog_sound (w := (173 / 851)) (n := 12)
    (lo := (412324517 / 1000000000)) (hi := (206162259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 339) = 1/(339 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-206162259 / 500000000) (-412324517 / 1000000000) (Real.log (339 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (290656161 / 1000000000) ≤ -Real.log (5120 / 6847) ∧
    -Real.log (5120 / 6847) ≤ (145328081 / 500000000) := by
  have h := checkLog_sound (w := (1727 / 11967)) (n := 12)
    (lo := (290656161 / 1000000000)) (hi := (145328081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6847 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6847 / 5120) = 1/(5120 / 6847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (290656161 / 1000000000) (145328081 / 500000000) (Real.log (6847 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6847 / 5120) = -Real.log (5120 / 6847) := by
    rw [show ((6847 / 5120) : ℝ) = ((5120 / 6847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (411439953 / 1000000000) ≤ -Real.log (3393 / 5120) ∧
    -Real.log (3393 / 5120) ≤ (205719977 / 500000000) := by
  have h := checkLog_sound (w := (1727 / 8513)) (n := 12)
    (lo := (411439953 / 1000000000)) (hi := (205719977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3393) = 1/(3393 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-205719977 / 500000000) (-411439953 / 1000000000) (Real.log (3393 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (107433497 / 500000000) ≤ -Real.log (1000000 / 1239697) ∧
    -Real.log (1000000 / 1239697) ≤ (42973399 / 200000000) := by
  have h := checkLog_sound (w := (239697 / 2239697)) (n := 12)
    (lo := (107433497 / 500000000)) (hi := (42973399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239697 / 1000000) = 1/(1000000 / 1239697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (107433497 / 500000000) (42973399 / 200000000) (Real.log (1239697 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1239697 / 1000000) = -Real.log (1000000 / 1239697) := by
    rw [show ((1239697 / 1000000) : ℝ) = ((1000000 / 1239697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1712739 / 6250000) ≤ -Real.log (760303 / 1000000) ∧
    -Real.log (760303 / 1000000) ≤ (274038241 / 1000000000) := by
  have h := checkLog_sound (w := (239697 / 1760303)) (n := 12)
    (lo := (1712739 / 6250000)) (hi := (274038241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760303) = 1/(760303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-274038241 / 1000000000) (-1712739 / 6250000) (Real.log (760303 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (107603671 / 500000000) ≤ -Real.log (1000000 / 1240119) ∧
    -Real.log (1000000 / 1240119) ≤ (215207343 / 1000000000) := by
  have h := checkLog_sound (w := (240119 / 2240119)) (n := 12)
    (lo := (107603671 / 500000000)) (hi := (215207343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240119 / 1000000) = 1/(1000000 / 1240119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (107603671 / 500000000) (215207343 / 1000000000) (Real.log (1240119 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1240119 / 1000000) = -Real.log (1000000 / 1240119) := by
    rw [show ((1240119 / 1000000) : ℝ) = ((1000000 / 1240119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68648359 / 250000000) ≤ -Real.log (759881 / 1000000) ∧
    -Real.log (759881 / 1000000) ≤ (274593437 / 1000000000) := by
  have h := checkLog_sound (w := (240119 / 1759881)) (n := 12)
    (lo := (68648359 / 250000000)) (hi := (274593437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759881) = 1/(759881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-274593437 / 1000000000) (-68648359 / 250000000) (Real.log (759881 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (39727619 / 250000000) ≤ -Real.log (1000000 / 1172233) ∧
    -Real.log (1000000 / 1172233) ≤ (158910477 / 1000000000) := by
  have h := checkLog_sound (w := (172233 / 2172233)) (n := 12)
    (lo := (39727619 / 250000000)) (hi := (158910477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1172233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1172233 / 1000000) = 1/(1000000 / 1172233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (39727619 / 250000000) (158910477 / 1000000000) (Real.log (1172233 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1172233 / 1000000) = -Real.log (1000000 / 1172233) := by
    rw [show ((1172233 / 1000000) : ℝ) = ((1000000 / 1172233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (37804713 / 200000000) ≤ -Real.log (827767 / 1000000) ∧
    -Real.log (827767 / 1000000) ≤ (94511783 / 500000000) := by
  have h := checkLog_sound (w := (172233 / 1827767)) (n := 12)
    (lo := (37804713 / 200000000)) (hi := (94511783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 827767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 827767) = 1/(827767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-94511783 / 500000000) (-37804713 / 200000000) (Real.log (827767 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (39794363 / 250000000) ≤ -Real.log (500000 / 586273) ∧
    -Real.log (500000 / 586273) ≤ (159177453 / 1000000000) := by
  have h := checkLog_sound (w := (86273 / 1086273)) (n := 12)
    (lo := (39794363 / 250000000)) (hi := (159177453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586273 / 500000) = 1/(500000 / 586273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (39794363 / 250000000) (159177453 / 1000000000) (Real.log (586273 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (586273 / 500000) = -Real.log (500000 / 586273) := by
    rw [show ((586273 / 500000) : ℝ) = ((500000 / 586273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (94700881 / 500000000) ≤ -Real.log (413727 / 500000) ∧
    -Real.log (413727 / 500000) ≤ (189401763 / 1000000000) := by
  have h := checkLog_sound (w := (86273 / 913727)) (n := 12)
    (lo := (94700881 / 500000000)) (hi := (189401763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413727) = 1/(413727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-189401763 / 1000000000) (-94700881 / 500000000) (Real.log (413727 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (702096113 / 1000000000) ≤ -Real.log (100000000000 / 201797819039) ∧
    -Real.log (100000000000 / 201797819039) ≤ (140419223 / 200000000) := by
  have h := checkLog_sound (w := (1797819039 / 401797819039)) (n := 12)
    (lo := (8948933 / 1000000000)) (hi := (4474467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201797819039 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(201797819039 / 200000000000) = 1/(100000000000 / 201797819039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (702096113 / 1000000000) (140419223 / 200000000) (Real.log (201797819039 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (201797819039 / 100000000000) = -Real.log (100000000000 / 201797819039) := by
    rw [show ((201797819039 / 100000000000) : ℝ) = ((100000000000 / 201797819039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (70341873 / 100000000) ≤ -Real.log (7812500000 / 15786320059) ∧
    -Real.log (7812500000 / 15786320059) ≤ (175854683 / 250000000) := by
  have h := checkLog_sound (w := (161320059 / 31411320059)) (n := 12)
    (lo := (205431 / 20000000)) (hi := (10271551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15786320059 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15786320059 / 15625000000) = 1/(7812500000 / 15786320059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (70341873 / 100000000) (175854683 / 250000000) (Real.log (15786320059 / 7812500000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (15786320059 / 7812500000) = -Real.log (7812500000 / 15786320059) := by
    rw [show ((15786320059 / 7812500000) : ℝ) = ((7812500000 / 15786320059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (97781047 / 200000000) ≤ -Real.log (31250000000 / 50954068641) ∧
    -Real.log (31250000000 / 50954068641) ≤ (122226309 / 250000000) := by
  have h := checkLog_sound (w := (19704068641 / 82204068641)) (n := 12)
    (lo := (97781047 / 200000000)) (hi := (122226309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50954068641 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50954068641 / 31250000000) = 1/(31250000000 / 50954068641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (97781047 / 200000000) (122226309 / 250000000) (Real.log (50954068641 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (50954068641 / 31250000000) = -Real.log (31250000000 / 50954068641) := by
    rw [show ((50954068641 / 31250000000) : ℝ) = ((31250000000 / 50954068641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (489800779 / 1000000000) ≤ -Real.log (781250000 / 1274993017) ∧
    -Real.log (781250000 / 1274993017) ≤ (24490039 / 50000000) := by
  have h := checkLog_sound (w := (493743017 / 2056243017)) (n := 12)
    (lo := (489800779 / 1000000000)) (hi := (24490039 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274993017 / 781250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274993017 / 781250000) = 1/(781250000 / 1274993017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (489800779 / 1000000000) (24490039 / 50000000) (Real.log (1274993017 / 781250000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (1274993017 / 781250000) = -Real.log (781250000 / 1274993017) := by
    rw [show ((1274993017 / 781250000) : ℝ) = ((781250000 / 1274993017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (173967021 / 500000000) ≤ -Real.log (500000000000 / 708069420501) ∧
    -Real.log (500000000000 / 708069420501) ≤ (347934043 / 1000000000) := by
  have h := checkLog_sound (w := (208069420501 / 1208069420501)) (n := 12)
    (lo := (173967021 / 500000000)) (hi := (347934043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708069420501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708069420501 / 500000000000) = 1/(500000000000 / 708069420501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (173967021 / 500000000) (347934043 / 1000000000) (Real.log (708069420501 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (708069420501 / 500000000000) = -Real.log (500000000000 / 708069420501) := by
    rw [show ((708069420501 / 500000000000) : ℝ) = ((500000000000 / 708069420501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (69715843 / 200000000) ≤ -Real.log (250000000000 / 354263197713) ∧
    -Real.log (250000000000 / 354263197713) ≤ (21786201 / 62500000) := by
  have h := checkLog_sound (w := (104263197713 / 604263197713)) (n := 12)
    (lo := (69715843 / 200000000)) (hi := (21786201 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354263197713 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354263197713 / 250000000000) = 1/(250000000000 / 354263197713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (69715843 / 200000000) (21786201 / 62500000) (Real.log (354263197713 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (354263197713 / 250000000000) = -Real.log (250000000000 / 354263197713) := by
    rw [show ((354263197713 / 250000000000) : ℝ) = ((250000000000 / 354263197713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (30224309 / 1000000000) ≤ -Real.log (242556969471 / 250000000000) ∧
    -Real.log (242556969471 / 250000000000) ≤ (3022431 / 100000000) := by
  have h := checkLog_sound (w := (7443030529 / 492556969471)) (n := 12)
    (lo := (30224309 / 1000000000)) (hi := (3022431 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242556969471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242556969471) = 1/(242556969471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3022431 / 100000000) (-30224309 / 1000000000) (Real.log (242556969471 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (470517 / 15625000) ≤ -Real.log (970335793711 / 1000000000000) ∧
    -Real.log (970335793711 / 1000000000000) ≤ (30113089 / 1000000000) := by
  have h := checkLog_sound (w := (29664206289 / 1970335793711)) (n := 12)
    (lo := (470517 / 15625000)) (hi := (30113089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970335793711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970335793711) = 1/(970335793711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-30113089 / 1000000000) (-470517 / 15625000) (Real.log (970335793711 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell149

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell150Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell150
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

theorem reflection_log_1_neg : (291532073 / 1000000000) ≤ -Real.log (5120 / 6853) ∧
    -Real.log (5120 / 6853) ≤ (145766037 / 500000000) := by
  have h := checkLog_sound (w := (1733 / 11973)) (n := 12)
    (lo := (291532073 / 1000000000)) (hi := (145766037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6853 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6853 / 5120) = 1/(5120 / 6853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (291532073 / 1000000000) (145766037 / 500000000) (Real.log (6853 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6853 / 5120) = -Real.log (5120 / 6853) := by
    rw [show ((6853 / 5120) : ℝ) = ((5120 / 6853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (82641973 / 200000000) ≤ -Real.log (3387 / 5120) ∧
    -Real.log (3387 / 5120) ≤ (206604933 / 500000000) := by
  have h := checkLog_sound (w := (1733 / 8507)) (n := 12)
    (lo := (82641973 / 200000000)) (hi := (206604933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3387) = 1/(3387 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-206604933 / 500000000) (-82641973 / 200000000) (Real.log (3387 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (291094213 / 1000000000) ≤ -Real.log (512 / 685) ∧
    -Real.log (512 / 685) ≤ (145547107 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1197)) (n := 12)
    (lo := (291094213 / 1000000000)) (hi := (145547107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685 / 512) = 1/(512 / 685) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (291094213 / 1000000000) (145547107 / 500000000) (Real.log (685 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (685 / 512) = -Real.log (512 / 685) := by
    rw [show ((685 / 512) : ℝ) = ((512 / 685) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (412324517 / 1000000000) ≤ -Real.log (339 / 512) ∧
    -Real.log (339 / 512) ≤ (206162259 / 500000000) := by
  have h := checkLog_sound (w := (173 / 851)) (n := 12)
    (lo := (412324517 / 1000000000)) (hi := (206162259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 339) = 1/(339 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-206162259 / 500000000) (-412324517 / 1000000000) (Real.log (339 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (26900817 / 125000000) ≤ -Real.log (500000 / 620059) ∧
    -Real.log (500000 / 620059) ≤ (215206537 / 1000000000) := by
  have h := checkLog_sound (w := (120059 / 1120059)) (n := 12)
    (lo := (26900817 / 125000000)) (hi := (215206537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620059 / 500000) = 1/(500000 / 620059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (26900817 / 125000000) (215206537 / 1000000000) (Real.log (620059 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (620059 / 500000) = -Real.log (500000 / 620059) := by
    rw [show ((620059 / 500000) : ℝ) = ((500000 / 620059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6864803 / 25000000) ≤ -Real.log (379941 / 500000) ∧
    -Real.log (379941 / 500000) ≤ (274592121 / 1000000000) := by
  have h := checkLog_sound (w := (120059 / 879941)) (n := 12)
    (lo := (6864803 / 25000000)) (hi := (274592121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379941) = 1/(379941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-274592121 / 1000000000) (-6864803 / 25000000) (Real.log (379941 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13471673 / 62500000) ≤ -Real.log (50000 / 62027) ∧
    -Real.log (50000 / 62027) ≤ (215546769 / 1000000000) := by
  have h := checkLog_sound (w := (12027 / 112027)) (n := 12)
    (lo := (13471673 / 62500000)) (hi := (215546769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62027 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62027 / 50000) = 1/(50000 / 62027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13471673 / 62500000) (215546769 / 1000000000) (Real.log (62027 / 50000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (62027 / 50000) = -Real.log (50000 / 62027) := by
    rw [show ((62027 / 50000) : ℝ) = ((50000 / 62027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (34393453 / 125000000) ≤ -Real.log (37973 / 50000) ∧
    -Real.log (37973 / 50000) ≤ (2201181 / 8000000) := by
  have h := checkLog_sound (w := (12027 / 87973)) (n := 12)
    (lo := (34393453 / 125000000)) (hi := (2201181 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37973) = 1/(37973 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2201181 / 8000000) (-34393453 / 125000000) (Real.log (37973 / 50000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (795883 / 5000000) ≤ -Real.log (200000 / 234509) ∧
    -Real.log (200000 / 234509) ≤ (159176601 / 1000000000) := by
  have h := checkLog_sound (w := (34509 / 434509)) (n := 12)
    (lo := (795883 / 5000000)) (hi := (159176601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234509 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234509 / 200000) = 1/(200000 / 234509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (795883 / 5000000) (159176601 / 1000000000) (Real.log (234509 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (234509 / 200000) = -Real.log (200000 / 234509) := by
    rw [show ((234509 / 200000) : ℝ) = ((200000 / 234509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (189400553 / 1000000000) ≤ -Real.log (165491 / 200000) ∧
    -Real.log (165491 / 200000) ≤ (94700277 / 500000000) := by
  have h := checkLog_sound (w := (34509 / 365491)) (n := 12)
    (lo := (189400553 / 1000000000)) (hi := (94700277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 165491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 165491) = 1/(165491 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-94700277 / 500000000) (-189400553 / 1000000000) (Real.log (165491 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31888701 / 200000000) ≤ -Real.log (500000 / 586429) ∧
    -Real.log (500000 / 586429) ≤ (79721753 / 500000000) := by
  have h := checkLog_sound (w := (86429 / 1086429)) (n := 12)
    (lo := (31888701 / 200000000)) (hi := (79721753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586429 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586429 / 500000) = 1/(500000 / 586429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31888701 / 200000000) (79721753 / 500000000) (Real.log (586429 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (586429 / 500000) = -Real.log (500000 / 586429) := by
    rw [show ((586429 / 500000) : ℝ) = ((500000 / 586429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (189778893 / 1000000000) ≤ -Real.log (413571 / 500000) ∧
    -Real.log (413571 / 500000) ≤ (94889447 / 500000000) := by
  have h := checkLog_sound (w := (86429 / 913571)) (n := 12)
    (lo := (189778893 / 1000000000)) (hi := (94889447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413571) = 1/(413571 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-94889447 / 500000000) (-189778893 / 1000000000) (Real.log (413571 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (70341873 / 100000000) ≤ -Real.log (20000000000 / 40412979351) ∧
    -Real.log (20000000000 / 40412979351) ≤ (175854683 / 250000000) := by
  have h := checkLog_sound (w := (412979351 / 80412979351)) (n := 12)
    (lo := (205431 / 20000000)) (hi := (10271551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40412979351 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40412979351 / 40000000000) = 1/(20000000000 / 40412979351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (70341873 / 100000000) (175854683 / 250000000) (Real.log (40412979351 / 20000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (40412979351 / 20000000000) = -Real.log (20000000000 / 40412979351) := by
    rw [show ((40412979351 / 20000000000) : ℝ) = ((20000000000 / 40412979351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (352370969 / 500000000) ≤ -Real.log (500000000000 / 1011662237969) ∧
    -Real.log (500000000000 / 1011662237969) ≤ (35237097 / 50000000) := by
  have h := checkLog_sound (w := (11662237969 / 2011662237969)) (n := 12)
    (lo := (5797379 / 500000000)) (hi := (11594759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1011662237969 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1011662237969 / 1000000000000) = 1/(500000000000 / 1011662237969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (352370969 / 500000000) (35237097 / 50000000) (Real.log (1011662237969 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1011662237969 / 500000000000) = -Real.log (500000000000 / 1011662237969) := by
    rw [show ((1011662237969 / 500000000000) : ℝ) = ((500000000000 / 1011662237969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (489798657 / 1000000000) ≤ -Real.log (500000000000 / 815993799037) ∧
    -Real.log (500000000000 / 815993799037) ≤ (244899329 / 500000000) := by
  have h := checkLog_sound (w := (315993799037 / 1315993799037)) (n := 12)
    (lo := (489798657 / 1000000000)) (hi := (244899329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((815993799037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(815993799037 / 500000000000) = 1/(500000000000 / 815993799037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (489798657 / 1000000000) (244899329 / 500000000) (Real.log (815993799037 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (815993799037 / 500000000000) = -Real.log (500000000000 / 815993799037) := by
    rw [show ((815993799037 / 500000000000) : ℝ) = ((500000000000 / 815993799037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (490694393 / 1000000000) ≤ -Real.log (500000000000 / 816725041477) ∧
    -Real.log (500000000000 / 816725041477) ≤ (245347197 / 500000000) := by
  have h := checkLog_sound (w := (316725041477 / 1316725041477)) (n := 12)
    (lo := (490694393 / 1000000000)) (hi := (245347197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((816725041477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(816725041477 / 500000000000) = 1/(500000000000 / 816725041477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (490694393 / 1000000000) (245347197 / 500000000) (Real.log (816725041477 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (816725041477 / 500000000000) = -Real.log (500000000000 / 816725041477) := by
    rw [show ((816725041477 / 500000000000) : ℝ) = ((500000000000 / 816725041477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (174288577 / 500000000) ≤ -Real.log (50000000000 / 70852493489) ∧
    -Real.log (50000000000 / 70852493489) ≤ (69715431 / 200000000) := by
  have h := checkLog_sound (w := (20852493489 / 120852493489)) (n := 12)
    (lo := (174288577 / 500000000)) (hi := (69715431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70852493489 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70852493489 / 50000000000) = 1/(50000000000 / 70852493489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (174288577 / 500000000) (69715431 / 200000000) (Real.log (70852493489 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (70852493489 / 50000000000) = -Real.log (50000000000 / 70852493489) := by
    rw [show ((70852493489 / 50000000000) : ℝ) = ((50000000000 / 70852493489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (174611199 / 500000000) ≤ -Real.log (500000000000 / 708982254559) ∧
    -Real.log (500000000000 / 708982254559) ≤ (349222399 / 1000000000) := by
  have h := checkLog_sound (w := (208982254559 / 1208982254559)) (n := 12)
    (lo := (174611199 / 500000000)) (hi := (349222399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708982254559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708982254559 / 500000000000) = 1/(500000000000 / 708982254559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (174611199 / 500000000) (349222399 / 1000000000) (Real.log (708982254559 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (708982254559 / 500000000000) = -Real.log (500000000000 / 708982254559) := by
    rw [show ((708982254559 / 500000000000) : ℝ) = ((500000000000 / 708982254559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7583847 / 250000000) ≤ -Real.log (242530027959 / 250000000000) ∧
    -Real.log (242530027959 / 250000000000) ≤ (30335389 / 1000000000) := by
  have h := checkLog_sound (w := (7469972041 / 492530027959)) (n := 12)
    (lo := (7583847 / 250000000)) (hi := (30335389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242530027959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242530027959) = 1/(242530027959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-30335389 / 1000000000) (-7583847 / 250000000) (Real.log (242530027959 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (30223953 / 1000000000) ≤ -Real.log (38809128919 / 40000000000) ∧
    -Real.log (38809128919 / 40000000000) ≤ (15111977 / 500000000) := by
  have h := checkLog_sound (w := (1190871081 / 78809128919)) (n := 12)
    (lo := (30223953 / 1000000000)) (hi := (15111977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38809128919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38809128919) = 1/(38809128919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-15111977 / 500000000) (-30223953 / 1000000000) (Real.log (38809128919 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell150

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell151Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell151
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

theorem reflection_log_1_neg : (145984871 / 500000000) ≤ -Real.log (640 / 857) ∧
    -Real.log (640 / 857) ≤ (291969743 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1497)) (n := 12)
    (lo := (145984871 / 500000000)) (hi := (291969743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857 / 640) = 1/(640 / 857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (145984871 / 500000000) (291969743 / 1000000000) (Real.log (857 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (857 / 640) = -Real.log (640 / 857) := by
    rw [show ((857 / 640) : ℝ) = ((640 / 857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (414095997 / 1000000000) ≤ -Real.log (423 / 640) ∧
    -Real.log (423 / 640) ≤ (207047999 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1063)) (n := 12)
    (lo := (414095997 / 1000000000)) (hi := (207047999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 423) = 1/(423 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-207047999 / 500000000) (-414095997 / 1000000000) (Real.log (423 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (291532073 / 1000000000) ≤ -Real.log (5120 / 6853) ∧
    -Real.log (5120 / 6853) ≤ (145766037 / 500000000) := by
  have h := checkLog_sound (w := (1733 / 11973)) (n := 12)
    (lo := (291532073 / 1000000000)) (hi := (145766037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6853 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6853 / 5120) = 1/(5120 / 6853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (291532073 / 1000000000) (145766037 / 500000000) (Real.log (6853 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6853 / 5120) = -Real.log (5120 / 6853) := by
    rw [show ((6853 / 5120) : ℝ) = ((5120 / 6853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (82641973 / 200000000) ≤ -Real.log (3387 / 5120) ∧
    -Real.log (3387 / 5120) ≤ (206604933 / 500000000) := by
  have h := checkLog_sound (w := (1733 / 8507)) (n := 12)
    (lo := (82641973 / 200000000)) (hi := (206604933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3387) = 1/(3387 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-206604933 / 500000000) (-82641973 / 200000000) (Real.log (3387 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (107772981 / 500000000) ≤ -Real.log (1000000 / 1240539) ∧
    -Real.log (1000000 / 1240539) ≤ (215545963 / 1000000000) := by
  have h := checkLog_sound (w := (240539 / 2240539)) (n := 12)
    (lo := (107772981 / 500000000)) (hi := (215545963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240539 / 1000000) = 1/(1000000 / 1240539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (107772981 / 500000000) (215545963 / 1000000000) (Real.log (1240539 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1240539 / 1000000) = -Real.log (1000000 / 1240539) := by
    rw [show ((1240539 / 1000000) : ℝ) = ((1000000 / 1240539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (275146307 / 1000000000) ≤ -Real.log (759461 / 1000000) ∧
    -Real.log (759461 / 1000000) ≤ (68786577 / 250000000) := by
  have h := checkLog_sound (w := (240539 / 1759461)) (n := 12)
    (lo := (275146307 / 1000000000)) (hi := (68786577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759461) = 1/(759461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-68786577 / 250000000) (-275146307 / 1000000000) (Real.log (759461 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (215886079 / 1000000000) ≤ -Real.log (1000000 / 1240961) ∧
    -Real.log (1000000 / 1240961) ≤ (168661 / 781250) := by
  have h := checkLog_sound (w := (240961 / 2240961)) (n := 12)
    (lo := (215886079 / 1000000000)) (hi := (168661 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240961 / 1000000) = 1/(1000000 / 1240961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (215886079 / 1000000000) (168661 / 781250) (Real.log (1240961 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1240961 / 1000000) = -Real.log (1000000 / 1240961) := by
    rw [show ((1240961 / 1000000) : ℝ) = ((1000000 / 1240961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (275702119 / 1000000000) ≤ -Real.log (759039 / 1000000) ∧
    -Real.log (759039 / 1000000) ≤ (6892553 / 25000000) := by
  have h := checkLog_sound (w := (240961 / 1759039)) (n := 12)
    (lo := (275702119 / 1000000000)) (hi := (6892553 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759039) = 1/(759039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6892553 / 25000000) (-275702119 / 1000000000) (Real.log (759039 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (39860663 / 250000000) ≤ -Real.log (1000000 / 1172857) ∧
    -Real.log (1000000 / 1172857) ≤ (159442653 / 1000000000) := by
  have h := checkLog_sound (w := (172857 / 2172857)) (n := 12)
    (lo := (39860663 / 250000000)) (hi := (159442653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1172857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1172857 / 1000000) = 1/(1000000 / 1172857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (39860663 / 250000000) (159442653 / 1000000000) (Real.log (1172857 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1172857 / 1000000) = -Real.log (1000000 / 1172857) := by
    rw [show ((1172857 / 1000000) : ℝ) = ((1000000 / 1172857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (47444421 / 250000000) ≤ -Real.log (827143 / 1000000) ∧
    -Real.log (827143 / 1000000) ≤ (37955537 / 200000000) := by
  have h := checkLog_sound (w := (172857 / 1827143)) (n := 12)
    (lo := (47444421 / 250000000)) (hi := (37955537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 827143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 827143) = 1/(827143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37955537 / 200000000) (-47444421 / 250000000) (Real.log (827143 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (159710339 / 1000000000) ≤ -Real.log (1000000 / 1173171) ∧
    -Real.log (1000000 / 1173171) ≤ (7985517 / 50000000) := by
  have h := checkLog_sound (w := (173171 / 2173171)) (n := 12)
    (lo := (159710339 / 1000000000)) (hi := (7985517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1173171 / 1000000) = 1/(1000000 / 1173171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (159710339 / 1000000000) (7985517 / 50000000) (Real.log (1173171 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1173171 / 1000000) = -Real.log (1000000 / 1173171) := by
    rw [show ((1173171 / 1000000) : ℝ) = ((1000000 / 1173171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2971209 / 15625000) ≤ -Real.log (826829 / 1000000) ∧
    -Real.log (826829 / 1000000) ≤ (190157377 / 1000000000) := by
  have h := checkLog_sound (w := (173171 / 1826829)) (n := 12)
    (lo := (2971209 / 15625000)) (hi := (190157377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 826829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 826829) = 1/(826829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-190157377 / 1000000000) (-2971209 / 15625000) (Real.log (826829 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (352370969 / 500000000) ≤ -Real.log (31250000000 / 63228889873) ∧
    -Real.log (31250000000 / 63228889873) ≤ (35237097 / 50000000) := by
  have h := checkLog_sound (w := (728889873 / 125728889873)) (n := 12)
    (lo := (5797379 / 500000000)) (hi := (11594759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63228889873 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63228889873 / 62500000000) = 1/(31250000000 / 63228889873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (352370969 / 500000000) (35237097 / 50000000) (Real.log (63228889873 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (63228889873 / 31250000000) = -Real.log (31250000000 / 63228889873) := by
    rw [show ((63228889873 / 31250000000) : ℝ) = ((31250000000 / 63228889873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (353032869 / 500000000) ≤ -Real.log (500000000000 / 1013002364067) ∧
    -Real.log (500000000000 / 1013002364067) ≤ (35303287 / 50000000) := by
  have h := checkLog_sound (w := (13002364067 / 2013002364067)) (n := 12)
    (lo := (6459279 / 500000000)) (hi := (12918559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1013002364067 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1013002364067 / 1000000000000) = 1/(500000000000 / 1013002364067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (353032869 / 500000000) (35303287 / 50000000) (Real.log (1013002364067 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1013002364067 / 500000000000) = -Real.log (500000000000 / 1013002364067) := by
    rw [show ((1013002364067 / 500000000000) : ℝ) = ((500000000000 / 1013002364067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (49069227 / 100000000) ≤ -Real.log (250000000000 / 408361653857) ∧
    -Real.log (250000000000 / 408361653857) ≤ (490692271 / 1000000000) := by
  have h := checkLog_sound (w := (158361653857 / 658361653857)) (n := 12)
    (lo := (49069227 / 100000000)) (hi := (490692271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408361653857 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408361653857 / 250000000000) = 1/(250000000000 / 408361653857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (49069227 / 100000000) (490692271 / 1000000000) (Real.log (408361653857 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (408361653857 / 250000000000) = -Real.log (250000000000 / 408361653857) := by
    rw [show ((408361653857 / 250000000000) : ℝ) = ((250000000000 / 408361653857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (245794099 / 500000000) ≤ -Real.log (500000000000 / 817455361319) ∧
    -Real.log (500000000000 / 817455361319) ≤ (491588199 / 1000000000) := by
  have h := checkLog_sound (w := (317455361319 / 1317455361319)) (n := 12)
    (lo := (245794099 / 500000000)) (hi := (491588199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817455361319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817455361319 / 500000000000) = 1/(500000000000 / 817455361319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (245794099 / 500000000) (491588199 / 1000000000) (Real.log (817455361319 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (817455361319 / 500000000000) = -Real.log (500000000000 / 817455361319) := by
    rw [show ((817455361319 / 500000000000) : ℝ) = ((500000000000 / 817455361319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (349220337 / 1000000000) ≤ -Real.log (250000000000 / 354490396461) ∧
    -Real.log (250000000000 / 354490396461) ≤ (174610169 / 500000000) := by
  have h := checkLog_sound (w := (104490396461 / 604490396461)) (n := 12)
    (lo := (349220337 / 1000000000)) (hi := (174610169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354490396461 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354490396461 / 250000000000) = 1/(250000000000 / 354490396461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (349220337 / 1000000000) (174610169 / 500000000) (Real.log (354490396461 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (354490396461 / 250000000000) = -Real.log (250000000000 / 354490396461) := by
    rw [show ((354490396461 / 250000000000) : ℝ) = ((250000000000 / 354490396461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (69973543 / 200000000) ≤ -Real.log (125000000000 / 177359980117) ∧
    -Real.log (125000000000 / 177359980117) ≤ (87466929 / 250000000) := by
  have h := checkLog_sound (w := (52359980117 / 302359980117)) (n := 12)
    (lo := (69973543 / 200000000)) (hi := (87466929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177359980117 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177359980117 / 125000000000) = 1/(125000000000 / 177359980117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (69973543 / 200000000) (87466929 / 250000000) (Real.log (177359980117 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (177359980117 / 125000000000) = -Real.log (125000000000 / 177359980117) := by
    rw [show ((177359980117 / 125000000000) : ℝ) = ((125000000000 / 177359980117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (30447037 / 1000000000) ≤ -Real.log (970011804759 / 1000000000000) ∧
    -Real.log (970011804759 / 1000000000000) ≤ (15223519 / 500000000) := by
  have h := checkLog_sound (w := (29988195241 / 1970011804759)) (n := 12)
    (lo := (30447037 / 1000000000)) (hi := (15223519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970011804759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970011804759) = 1/(970011804759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-15223519 / 500000000) (-30447037 / 1000000000) (Real.log (970011804759 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3791879 / 125000000) ≤ -Real.log (970120457551 / 1000000000000) ∧
    -Real.log (970120457551 / 1000000000000) ≤ (30335033 / 1000000000) := by
  have h := checkLog_sound (w := (29879542449 / 1970120457551)) (n := 12)
    (lo := (3791879 / 125000000)) (hi := (30335033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970120457551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970120457551) = 1/(970120457551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-30335033 / 1000000000) (-3791879 / 125000000) (Real.log (970120457551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell151

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell152Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell152
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

theorem reflection_log_1_neg : (292407219 / 1000000000) ≤ -Real.log (5120 / 6859) ∧
    -Real.log (5120 / 6859) ≤ (14620361 / 50000000) := by
  have h := checkLog_sound (w := (1739 / 11979)) (n := 12)
    (lo := (292407219 / 1000000000)) (hi := (14620361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6859 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6859 / 5120) = 1/(5120 / 6859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (292407219 / 1000000000) (14620361 / 50000000) (Real.log (6859 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6859 / 5120) = -Real.log (5120 / 6859) := by
    rw [show ((6859 / 5120) : ℝ) = ((5120 / 6859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (82996583 / 200000000) ≤ -Real.log (3381 / 5120) ∧
    -Real.log (3381 / 5120) ≤ (103745729 / 250000000) := by
  have h := checkLog_sound (w := (1739 / 8501)) (n := 12)
    (lo := (82996583 / 200000000)) (hi := (103745729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3381) = 1/(3381 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-103745729 / 250000000) (-82996583 / 200000000) (Real.log (3381 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (145984871 / 500000000) ≤ -Real.log (640 / 857) ∧
    -Real.log (640 / 857) ≤ (291969743 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1497)) (n := 12)
    (lo := (145984871 / 500000000)) (hi := (291969743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857 / 640) = 1/(640 / 857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (145984871 / 500000000) (291969743 / 1000000000) (Real.log (857 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (857 / 640) = -Real.log (640 / 857) := by
    rw [show ((857 / 640) : ℝ) = ((640 / 857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (414095997 / 1000000000) ≤ -Real.log (423 / 640) ∧
    -Real.log (423 / 640) ≤ (207047999 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1063)) (n := 12)
    (lo := (414095997 / 1000000000)) (hi := (207047999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 423) = 1/(423 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-207047999 / 500000000) (-414095997 / 1000000000) (Real.log (423 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (215885273 / 1000000000) ≤ -Real.log (3125 / 3878) ∧
    -Real.log (3125 / 3878) ≤ (107942637 / 500000000) := by
  have h := checkLog_sound (w := (753 / 7003)) (n := 12)
    (lo := (215885273 / 1000000000)) (hi := (107942637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3878 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3878 / 3125) = 1/(3125 / 3878) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (215885273 / 1000000000) (107942637 / 500000000) (Real.log (3878 / 3125)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3878 / 3125) = -Real.log (3125 / 3878) := by
    rw [show ((3878 / 3125) : ℝ) = ((3125 / 3878) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (137850401 / 500000000) ≤ -Real.log (2372 / 3125) ∧
    -Real.log (2372 / 3125) ≤ (275700803 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 5497)) (n := 12)
    (lo := (137850401 / 500000000)) (hi := (275700803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2372) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2372) = 1/(2372 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-275700803 / 1000000000) (-137850401 / 500000000) (Real.log (2372 / 3125)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (216224469 / 1000000000) ≤ -Real.log (1000000 / 1241381) ∧
    -Real.log (1000000 / 1241381) ≤ (21622447 / 100000000) := by
  have h := checkLog_sound (w := (241381 / 2241381)) (n := 12)
    (lo := (216224469 / 1000000000)) (hi := (21622447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241381 / 1000000) = 1/(1000000 / 1241381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (216224469 / 1000000000) (21622447 / 100000000) (Real.log (1241381 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1241381 / 1000000) = -Real.log (1000000 / 1241381) := by
    rw [show ((1241381 / 1000000) : ℝ) = ((1000000 / 1241381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (276255603 / 1000000000) ≤ -Real.log (758619 / 1000000) ∧
    -Real.log (758619 / 1000000) ≤ (69063901 / 250000000) := by
  have h := checkLog_sound (w := (241381 / 1758619)) (n := 12)
    (lo := (276255603 / 1000000000)) (hi := (69063901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758619) = 1/(758619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-69063901 / 250000000) (-276255603 / 1000000000) (Real.log (758619 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79854743 / 500000000) ≤ -Real.log (100000 / 117317) ∧
    -Real.log (100000 / 117317) ≤ (159709487 / 1000000000) := by
  have h := checkLog_sound (w := (17317 / 217317)) (n := 12)
    (lo := (79854743 / 500000000)) (hi := (159709487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117317 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117317 / 100000) = 1/(100000 / 117317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79854743 / 500000000) (159709487 / 1000000000) (Real.log (117317 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (117317 / 100000) = -Real.log (100000 / 117317) := by
    rw [show ((117317 / 100000) : ℝ) = ((100000 / 117317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (190156167 / 1000000000) ≤ -Real.log (82683 / 100000) ∧
    -Real.log (82683 / 100000) ≤ (23769521 / 125000000) := by
  have h := checkLog_sound (w := (17317 / 182683)) (n := 12)
    (lo := (190156167 / 1000000000)) (hi := (23769521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82683) = 1/(82683 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23769521 / 125000000) (-190156167 / 1000000000) (Real.log (82683 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (159976249 / 1000000000) ≤ -Real.log (1000000 / 1173483) ∧
    -Real.log (1000000 / 1173483) ≤ (127981 / 800000) := by
  have h := checkLog_sound (w := (173483 / 2173483)) (n := 12)
    (lo := (159976249 / 1000000000)) (hi := (127981 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1173483 / 1000000) = 1/(1000000 / 1173483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (159976249 / 1000000000) (127981 / 800000) (Real.log (1173483 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1173483 / 1000000) = -Real.log (1000000 / 1173483) := by
    rw [show ((1173483 / 1000000) : ℝ) = ((1000000 / 1173483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (190534793 / 1000000000) ≤ -Real.log (826517 / 1000000) ∧
    -Real.log (826517 / 1000000) ≤ (95267397 / 500000000) := by
  have h := checkLog_sound (w := (173483 / 1826517)) (n := 12)
    (lo := (190534793 / 1000000000)) (hi := (95267397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 826517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 826517) = 1/(826517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-95267397 / 500000000) (-190534793 / 1000000000) (Real.log (826517 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (353032869 / 500000000) ≤ -Real.log (250000000000 / 506501182033) ∧
    -Real.log (250000000000 / 506501182033) ≤ (35303287 / 50000000) := by
  have h := checkLog_sound (w := (6501182033 / 1006501182033)) (n := 12)
    (lo := (6459279 / 500000000)) (hi := (12918559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((506501182033 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(506501182033 / 500000000000) = 1/(250000000000 / 506501182033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (353032869 / 500000000) (35303287 / 50000000) (Real.log (506501182033 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (506501182033 / 250000000000) = -Real.log (250000000000 / 506501182033) := by
    rw [show ((506501182033 / 250000000000) : ℝ) = ((250000000000 / 506501182033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (353695067 / 500000000) ≤ -Real.log (500000000000 / 1014344868383) ∧
    -Real.log (500000000000 / 1014344868383) ≤ (88423767 / 125000000) := by
  have h := checkLog_sound (w := (14344868383 / 2014344868383)) (n := 12)
    (lo := (7121477 / 500000000)) (hi := (2848591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1014344868383 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1014344868383 / 1000000000000) = 1/(500000000000 / 1014344868383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (353695067 / 500000000) (88423767 / 125000000) (Real.log (1014344868383 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1014344868383 / 500000000000) = -Real.log (500000000000 / 1014344868383) := by
    rw [show ((1014344868383 / 500000000000) : ℝ) = ((500000000000 / 1014344868383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (19663443 / 40000000) ≤ -Real.log (15625000000 / 25545425801) ∧
    -Real.log (15625000000 / 25545425801) ≤ (122896519 / 250000000) := by
  have h := checkLog_sound (w := (9920425801 / 41170425801)) (n := 12)
    (lo := (19663443 / 40000000)) (hi := (122896519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25545425801 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25545425801 / 15625000000) = 1/(15625000000 / 25545425801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19663443 / 40000000) (122896519 / 250000000) (Real.log (25545425801 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25545425801 / 15625000000) = -Real.log (15625000000 / 25545425801) := by
    rw [show ((25545425801 / 15625000000) : ℝ) = ((15625000000 / 25545425801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (492480073 / 1000000000) ≤ -Real.log (500000000000 / 818184754139) ∧
    -Real.log (500000000000 / 818184754139) ≤ (246240037 / 500000000) := by
  have h := checkLog_sound (w := (318184754139 / 1318184754139)) (n := 12)
    (lo := (492480073 / 1000000000)) (hi := (246240037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818184754139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818184754139 / 500000000000) = 1/(500000000000 / 818184754139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (492480073 / 1000000000) (246240037 / 500000000) (Real.log (818184754139 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (818184754139 / 500000000000) = -Real.log (500000000000 / 818184754139) := by
    rw [show ((818184754139 / 500000000000) : ℝ) = ((500000000000 / 818184754139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (174932827 / 500000000) ≤ -Real.log (125000000000 / 177359614431) ∧
    -Real.log (125000000000 / 177359614431) ≤ (69973131 / 200000000) := by
  have h := checkLog_sound (w := (52359614431 / 302359614431)) (n := 12)
    (lo := (174932827 / 500000000)) (hi := (69973131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177359614431 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177359614431 / 125000000000) = 1/(125000000000 / 177359614431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (174932827 / 500000000) (69973131 / 200000000) (Real.log (177359614431 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (177359614431 / 125000000000) = -Real.log (125000000000 / 177359614431) := by
    rw [show ((177359614431 / 125000000000) : ℝ) = ((125000000000 / 177359614431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (175255521 / 500000000) ≤ -Real.log (12500000000 / 17747411729) ∧
    -Real.log (12500000000 / 17747411729) ≤ (350511043 / 1000000000) := by
  have h := checkLog_sound (w := (5247411729 / 30247411729)) (n := 12)
    (lo := (175255521 / 500000000)) (hi := (350511043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17747411729 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17747411729 / 12500000000) = 1/(12500000000 / 17747411729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (175255521 / 500000000) (350511043 / 1000000000) (Real.log (17747411729 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17747411729 / 12500000000) = -Real.log (12500000000 / 17747411729) := by
    rw [show ((17747411729 / 12500000000) : ℝ) = ((12500000000 / 17747411729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (30558543 / 1000000000) ≤ -Real.log (969903648711 / 1000000000000) ∧
    -Real.log (969903648711 / 1000000000000) ≤ (1909909 / 62500000) := by
  have h := checkLog_sound (w := (30096351289 / 1969903648711)) (n := 12)
    (lo := (30558543 / 1000000000)) (hi := (1909909 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969903648711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969903648711) = 1/(969903648711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1909909 / 62500000) (-30558543 / 1000000000) (Real.log (969903648711 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (761167 / 25000000) ≤ -Real.log (9700121511 / 10000000000) ∧
    -Real.log (9700121511 / 10000000000) ≤ (30446681 / 1000000000) := by
  have h := checkLog_sound (w := (299878489 / 19700121511)) (n := 12)
    (lo := (761167 / 25000000)) (hi := (30446681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9700121511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9700121511) = 1/(9700121511 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-30446681 / 1000000000) (-761167 / 25000000) (Real.log (9700121511 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell152

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell153Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell153
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

theorem reflection_log_1_neg : (58568901 / 200000000) ≤ -Real.log (2560 / 3431) ∧
    -Real.log (2560 / 3431) ≤ (146422253 / 500000000) := by
  have h := checkLog_sound (w := (871 / 5991)) (n := 12)
    (lo := (58568901 / 200000000)) (hi := (146422253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3431 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3431 / 2560) = 1/(2560 / 3431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (58568901 / 200000000) (146422253 / 500000000) (Real.log (3431 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3431 / 2560) = -Real.log (2560 / 3431) := by
    rw [show ((3431 / 2560) : ℝ) = ((2560 / 3431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20793531 / 50000000) ≤ -Real.log (1689 / 2560) ∧
    -Real.log (1689 / 2560) ≤ (415870621 / 1000000000) := by
  have h := checkLog_sound (w := (871 / 4249)) (n := 12)
    (lo := (20793531 / 50000000)) (hi := (415870621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1689) = 1/(1689 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-415870621 / 1000000000) (-20793531 / 50000000) (Real.log (1689 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (292407219 / 1000000000) ≤ -Real.log (5120 / 6859) ∧
    -Real.log (5120 / 6859) ≤ (14620361 / 50000000) := by
  have h := checkLog_sound (w := (1739 / 11979)) (n := 12)
    (lo := (292407219 / 1000000000)) (hi := (14620361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6859 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6859 / 5120) = 1/(5120 / 6859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (292407219 / 1000000000) (14620361 / 50000000) (Real.log (6859 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6859 / 5120) = -Real.log (5120 / 6859) := by
    rw [show ((6859 / 5120) : ℝ) = ((5120 / 6859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (82996583 / 200000000) ≤ -Real.log (3381 / 5120) ∧
    -Real.log (3381 / 5120) ≤ (103745729 / 250000000) := by
  have h := checkLog_sound (w := (1739 / 8501)) (n := 12)
    (lo := (82996583 / 200000000)) (hi := (103745729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3381) = 1/(3381 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-103745729 / 250000000) (-82996583 / 200000000) (Real.log (3381 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (13513979 / 62500000) ≤ -Real.log (50000 / 62069) ∧
    -Real.log (50000 / 62069) ≤ (43244733 / 200000000) := by
  have h := checkLog_sound (w := (12069 / 112069)) (n := 12)
    (lo := (13513979 / 62500000)) (hi := (43244733 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62069 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62069 / 50000) = 1/(50000 / 62069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (13513979 / 62500000) (43244733 / 200000000) (Real.log (62069 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (62069 / 50000) = -Real.log (50000 / 62069) := by
    rw [show ((62069 / 50000) : ℝ) = ((50000 / 62069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (55250857 / 200000000) ≤ -Real.log (37931 / 50000) ∧
    -Real.log (37931 / 50000) ≤ (138127143 / 500000000) := by
  have h := checkLog_sound (w := (12069 / 87931)) (n := 12)
    (lo := (55250857 / 200000000)) (hi := (138127143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37931) = 1/(37931 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-138127143 / 500000000) (-55250857 / 200000000) (Real.log (37931 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (4331271 / 20000000) ≤ -Real.log (500000 / 620901) ∧
    -Real.log (500000 / 620901) ≤ (216563551 / 1000000000) := by
  have h := checkLog_sound (w := (120901 / 1120901)) (n := 12)
    (lo := (4331271 / 20000000)) (hi := (216563551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620901 / 500000) = 1/(500000 / 620901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (4331271 / 20000000) (216563551 / 1000000000) (Real.log (620901 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (620901 / 500000) = -Real.log (500000 / 620901) := by
    rw [show ((620901 / 500000) : ℝ) = ((500000 / 620901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (276810713 / 1000000000) ≤ -Real.log (379099 / 500000) ∧
    -Real.log (379099 / 500000) ≤ (138405357 / 500000000) := by
  have h := checkLog_sound (w := (120901 / 879099)) (n := 12)
    (lo := (276810713 / 1000000000)) (hi := (138405357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379099) = 1/(379099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-138405357 / 500000000) (-276810713 / 1000000000) (Real.log (379099 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (159975397 / 1000000000) ≤ -Real.log (500000 / 586741) ∧
    -Real.log (500000 / 586741) ≤ (79987699 / 500000000) := by
  have h := checkLog_sound (w := (86741 / 1086741)) (n := 12)
    (lo := (159975397 / 1000000000)) (hi := (79987699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586741 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586741 / 500000) = 1/(500000 / 586741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (159975397 / 1000000000) (79987699 / 500000000) (Real.log (586741 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (586741 / 500000) = -Real.log (500000 / 586741) := by
    rw [show ((586741 / 500000) : ℝ) = ((500000 / 586741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (190533583 / 1000000000) ≤ -Real.log (413259 / 500000) ∧
    -Real.log (413259 / 500000) ≤ (11908349 / 62500000) := by
  have h := checkLog_sound (w := (86741 / 913259)) (n := 12)
    (lo := (190533583 / 1000000000)) (hi := (11908349 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413259) = 1/(413259 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-11908349 / 62500000) (-190533583 / 1000000000) (Real.log (413259 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (160242089 / 1000000000) ≤ -Real.log (200000 / 234759) ∧
    -Real.log (200000 / 234759) ≤ (16024209 / 100000000) := by
  have h := checkLog_sound (w := (34759 / 434759)) (n := 12)
    (lo := (160242089 / 1000000000)) (hi := (16024209 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234759 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234759 / 200000) = 1/(200000 / 234759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (160242089 / 1000000000) (16024209 / 100000000) (Real.log (234759 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (234759 / 200000) = -Real.log (200000 / 234759) := by
    rw [show ((234759 / 200000) : ℝ) = ((200000 / 234759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (5966011 / 31250000) ≤ -Real.log (165241 / 200000) ∧
    -Real.log (165241 / 200000) ≤ (190912353 / 1000000000) := by
  have h := checkLog_sound (w := (34759 / 365241)) (n := 12)
    (lo := (5966011 / 31250000)) (hi := (190912353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 165241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 165241) = 1/(165241 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-190912353 / 1000000000) (-5966011 / 31250000) (Real.log (165241 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (353695067 / 500000000) ≤ -Real.log (250000000000 / 507172434191) ∧
    -Real.log (250000000000 / 507172434191) ≤ (88423767 / 125000000) := by
  have h := checkLog_sound (w := (7172434191 / 1007172434191)) (n := 12)
    (lo := (7121477 / 500000000)) (hi := (2848591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((507172434191 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(507172434191 / 500000000000) = 1/(250000000000 / 507172434191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (353695067 / 500000000) (88423767 / 125000000) (Real.log (507172434191 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (507172434191 / 250000000000) = -Real.log (250000000000 / 507172434191) := by
    rw [show ((507172434191 / 250000000000) : ℝ) = ((250000000000 / 507172434191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (5669721 / 8000000) ≤ -Real.log (500000000000 / 1015689757253) ∧
    -Real.log (500000000000 / 1015689757253) ≤ (708715127 / 1000000000) := by
  have h := checkLog_sound (w := (15689757253 / 2015689757253)) (n := 12)
    (lo := (3113589 / 200000000)) (hi := (7783973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1015689757253 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1015689757253 / 1000000000000) = 1/(500000000000 / 1015689757253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (5669721 / 8000000) (708715127 / 1000000000) (Real.log (1015689757253 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1015689757253 / 500000000000) = -Real.log (500000000000 / 1015689757253) := by
    rw [show ((1015689757253 / 500000000000) : ℝ) = ((500000000000 / 1015689757253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (492477949 / 1000000000) ≤ -Real.log (50000000000 / 81818301653) ∧
    -Real.log (50000000000 / 81818301653) ≤ (9849559 / 20000000) := by
  have h := checkLog_sound (w := (31818301653 / 131818301653)) (n := 12)
    (lo := (492477949 / 1000000000)) (hi := (9849559 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81818301653 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81818301653 / 50000000000) = 1/(50000000000 / 81818301653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (492477949 / 1000000000) (9849559 / 20000000) (Real.log (81818301653 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (81818301653 / 50000000000) = -Real.log (50000000000 / 81818301653) := by
    rw [show ((81818301653 / 50000000000) : ℝ) = ((50000000000 / 81818301653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61671783 / 125000000) ≤ -Real.log (62500000000 / 102364586823) ∧
    -Real.log (62500000000 / 102364586823) ≤ (98674853 / 200000000) := by
  have h := checkLog_sound (w := (39864586823 / 164864586823)) (n := 12)
    (lo := (61671783 / 125000000)) (hi := (98674853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102364586823 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102364586823 / 62500000000) = 1/(62500000000 / 102364586823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (61671783 / 125000000) (98674853 / 200000000) (Real.log (102364586823 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (102364586823 / 62500000000) = -Real.log (62500000000 / 102364586823) := by
    rw [show ((102364586823 / 62500000000) : ℝ) = ((62500000000 / 102364586823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (17525449 / 50000000) ≤ -Real.log (500000000000 / 709895005311) ∧
    -Real.log (500000000000 / 709895005311) ≤ (350508981 / 1000000000) := by
  have h := checkLog_sound (w := (209895005311 / 1209895005311)) (n := 12)
    (lo := (17525449 / 50000000)) (hi := (350508981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709895005311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709895005311 / 500000000000) = 1/(500000000000 / 709895005311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (17525449 / 50000000) (350508981 / 1000000000) (Real.log (709895005311 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (709895005311 / 500000000000) = -Real.log (500000000000 / 709895005311) := by
    rw [show ((709895005311 / 500000000000) : ℝ) = ((500000000000 / 709895005311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (351154441 / 1000000000) ≤ -Real.log (100000000000 / 142070672533) ∧
    -Real.log (100000000000 / 142070672533) ≤ (175577221 / 500000000) := by
  have h := checkLog_sound (w := (42070672533 / 242070672533)) (n := 12)
    (lo := (351154441 / 1000000000)) (hi := (175577221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142070672533 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142070672533 / 100000000000) = 1/(100000000000 / 142070672533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (351154441 / 1000000000) (175577221 / 500000000) (Real.log (142070672533 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (142070672533 / 100000000000) = -Real.log (100000000000 / 142070672533) := by
    rw [show ((142070672533 / 100000000000) : ℝ) = ((100000000000 / 142070672533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15335131 / 500000000) ≤ -Real.log (38791811919 / 40000000000) ∧
    -Real.log (38791811919 / 40000000000) ≤ (30670263 / 1000000000) := by
  have h := checkLog_sound (w := (1208188081 / 78791811919)) (n := 12)
    (lo := (15335131 / 500000000)) (hi := (30670263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38791811919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38791811919) = 1/(38791811919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-30670263 / 1000000000) (-15335131 / 500000000) (Real.log (38791811919 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6111637 / 200000000) ≤ -Real.log (242475998919 / 250000000000) ∧
    -Real.log (242475998919 / 250000000000) ≤ (15279093 / 500000000) := by
  have h := checkLog_sound (w := (7524001081 / 492475998919)) (n := 12)
    (lo := (6111637 / 200000000)) (hi := (15279093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242475998919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242475998919) = 1/(242475998919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-15279093 / 500000000) (-6111637 / 200000000) (Real.log (242475998919 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell153

end


