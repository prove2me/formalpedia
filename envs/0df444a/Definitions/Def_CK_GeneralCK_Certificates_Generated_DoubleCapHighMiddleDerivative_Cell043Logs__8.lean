-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell043Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell043Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:52:58.841434+00:00
-- url     : https://prove2.me/theorems/b3d648ee-f152-459e-9be3-9c7505b37fb5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell043Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell044…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell043Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell044Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell045Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell046Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell047Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell048Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell049Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell050Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell043Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell044Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell045Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell046Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell047Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell048Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell049Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell050Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell043Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell044Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell045Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell046Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell047Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell048Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell049Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell050Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell043Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell044Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell045Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell046Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell047Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell048Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell049Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell050Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell043Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell043
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

theorem reflection_log_1_neg : (15222421 / 62500000) ≤ -Real.log (1280 / 1633) ∧
    -Real.log (1280 / 1633) ≤ (243558737 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 2913)) (n := 12)
    (lo := (15222421 / 62500000)) (hi := (243558737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1633 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1633 / 1280) = 1/(1280 / 1633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (15222421 / 62500000) (243558737 / 1000000000) (Real.log (1633 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1633 / 1280) = -Real.log (1280 / 1633) := by
    rw [show ((1633 / 1280) : ℝ) = ((1280 / 1633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (322661791 / 1000000000) ≤ -Real.log (927 / 1280) ∧
    -Real.log (927 / 1280) ≤ (10083181 / 31250000) := by
  have h := checkLog_sound (w := (353 / 2207)) (n := 12)
    (lo := (322661791 / 1000000000)) (hi := (10083181 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 927) = 1/(927 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10083181 / 31250000) (-322661791 / 1000000000) (Real.log (927 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (243099353 / 1000000000) ≤ -Real.log (5120 / 6529) ∧
    -Real.log (5120 / 6529) ≤ (121549677 / 500000000) := by
  have h := checkLog_sound (w := (1409 / 11649)) (n := 12)
    (lo := (243099353 / 1000000000)) (hi := (121549677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6529 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6529 / 5120) = 1/(5120 / 6529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (243099353 / 1000000000) (121549677 / 500000000) (Real.log (6529 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6529 / 5120) = -Real.log (5120 / 6529) := by
    rw [show ((6529 / 5120) : ℝ) = ((5120 / 6529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2514477 / 7812500) ≤ -Real.log (3711 / 5120) ∧
    -Real.log (3711 / 5120) ≤ (321853057 / 1000000000) := by
  have h := checkLog_sound (w := (1409 / 8831)) (n := 12)
    (lo := (2514477 / 7812500)) (hi := (321853057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3711) = 1/(3711 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-321853057 / 1000000000) (-2514477 / 7812500) (Real.log (3711 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (22291911 / 125000000) ≤ -Real.log (500000 / 597613) ∧
    -Real.log (500000 / 597613) ≤ (178335289 / 1000000000) := by
  have h := checkLog_sound (w := (97613 / 1097613)) (n := 12)
    (lo := (22291911 / 125000000)) (hi := (178335289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597613 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597613 / 500000) = 1/(500000 / 597613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (22291911 / 125000000) (178335289 / 1000000000) (Real.log (597613 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (597613 / 500000) = -Real.log (500000 / 597613) := by
    rw [show ((597613 / 500000) : ℝ) = ((500000 / 597613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (108596893 / 500000000) ≤ -Real.log (402387 / 500000) ∧
    -Real.log (402387 / 500000) ≤ (217193787 / 1000000000) := by
  have h := checkLog_sound (w := (97613 / 902387)) (n := 12)
    (lo := (108596893 / 500000000)) (hi := (217193787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 402387) = 1/(402387 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-217193787 / 1000000000) (-108596893 / 500000000) (Real.log (402387 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1429493 / 8000000) ≤ -Real.log (500000 / 597823) ∧
    -Real.log (500000 / 597823) ≤ (89343313 / 500000000) := by
  have h := checkLog_sound (w := (97823 / 1097823)) (n := 12)
    (lo := (1429493 / 8000000)) (hi := (89343313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597823 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597823 / 500000) = 1/(500000 / 597823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1429493 / 8000000) (89343313 / 500000000) (Real.log (597823 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (597823 / 500000) = -Real.log (500000 / 597823) := by
    rw [show ((597823 / 500000) : ℝ) = ((500000 / 597823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6803619 / 31250000) ≤ -Real.log (402177 / 500000) ∧
    -Real.log (402177 / 500000) ≤ (217715809 / 1000000000) := by
  have h := checkLog_sound (w := (97823 / 902177)) (n := 12)
    (lo := (6803619 / 31250000)) (hi := (217715809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 402177) = 1/(402177 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-217715809 / 1000000000) (-6803619 / 31250000) (Real.log (402177 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (130606243 / 1000000000) ≤ -Real.log (1000000 / 1139519) ∧
    -Real.log (1000000 / 1139519) ≤ (32651561 / 250000000) := by
  have h := checkLog_sound (w := (139519 / 2139519)) (n := 12)
    (lo := (130606243 / 1000000000)) (hi := (32651561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1139519 / 1000000) = 1/(1000000 / 1139519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (130606243 / 1000000000) (32651561 / 250000000) (Real.log (1139519 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1139519 / 1000000) = -Real.log (1000000 / 1139519) := by
    rw [show ((1139519 / 1000000) : ℝ) = ((1000000 / 1139519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (150263743 / 1000000000) ≤ -Real.log (860481 / 1000000) ∧
    -Real.log (860481 / 1000000) ≤ (2347871 / 15625000) := by
  have h := checkLog_sound (w := (139519 / 1860481)) (n := 12)
    (lo := (150263743 / 1000000000)) (hi := (2347871 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 860481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 860481) = 1/(860481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2347871 / 15625000) (-150263743 / 1000000000) (Real.log (860481 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130875619 / 1000000000) ≤ -Real.log (500000 / 569913) ∧
    -Real.log (500000 / 569913) ≤ (6543781 / 50000000) := by
  have h := checkLog_sound (w := (69913 / 1069913)) (n := 12)
    (lo := (130875619 / 1000000000)) (hi := (6543781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569913 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569913 / 500000) = 1/(500000 / 569913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130875619 / 1000000000) (6543781 / 50000000) (Real.log (569913 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (569913 / 500000) = -Real.log (500000 / 569913) := by
    rw [show ((569913 / 500000) : ℝ) = ((500000 / 569913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18827573 / 125000000) ≤ -Real.log (430087 / 500000) ∧
    -Real.log (430087 / 500000) ≤ (30124117 / 200000000) := by
  have h := checkLog_sound (w := (69913 / 930087)) (n := 12)
    (lo := (18827573 / 125000000)) (hi := (30124117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430087) = 1/(430087 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-30124117 / 200000000) (-18827573 / 125000000) (Real.log (430087 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (56495241 / 100000000) ≤ -Real.log (500000000000 / 879682026407) ∧
    -Real.log (500000000000 / 879682026407) ≤ (564952411 / 1000000000) := by
  have h := checkLog_sound (w := (379682026407 / 1379682026407)) (n := 12)
    (lo := (56495241 / 100000000)) (hi := (564952411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879682026407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879682026407 / 500000000000) = 1/(500000000000 / 879682026407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (56495241 / 100000000) (564952411 / 1000000000) (Real.log (879682026407 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (879682026407 / 500000000000) = -Real.log (500000000000 / 879682026407) := by
    rw [show ((879682026407 / 500000000000) : ℝ) = ((500000000000 / 879682026407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (566220527 / 1000000000) ≤ -Real.log (500000000000 / 880798274003) ∧
    -Real.log (500000000000 / 880798274003) ≤ (35388783 / 62500000) := by
  have h := checkLog_sound (w := (380798274003 / 1380798274003)) (n := 12)
    (lo := (566220527 / 1000000000)) (hi := (35388783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((880798274003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(880798274003 / 500000000000) = 1/(500000000000 / 880798274003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (566220527 / 1000000000) (35388783 / 62500000) (Real.log (880798274003 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (880798274003 / 500000000000) = -Real.log (500000000000 / 880798274003) := by
    rw [show ((880798274003 / 500000000000) : ℝ) = ((500000000000 / 880798274003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (15821163 / 40000000) ≤ -Real.log (500000000000 / 742584874759) ∧
    -Real.log (500000000000 / 742584874759) ≤ (98882269 / 250000000) := by
  have h := checkLog_sound (w := (242584874759 / 1242584874759)) (n := 12)
    (lo := (15821163 / 40000000)) (hi := (98882269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742584874759 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742584874759 / 500000000000) = 1/(500000000000 / 742584874759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (15821163 / 40000000) (98882269 / 250000000) (Real.log (742584874759 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (742584874759 / 500000000000) = -Real.log (500000000000 / 742584874759) := by
    rw [show ((742584874759 / 500000000000) : ℝ) = ((500000000000 / 742584874759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (396402433 / 1000000000) ≤ -Real.log (100000000000 / 148646740117) ∧
    -Real.log (100000000000 / 148646740117) ≤ (198201217 / 500000000) := by
  have h := checkLog_sound (w := (48646740117 / 248646740117)) (n := 12)
    (lo := (396402433 / 1000000000)) (hi := (198201217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148646740117 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148646740117 / 100000000000) = 1/(100000000000 / 148646740117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (396402433 / 1000000000) (198201217 / 500000000) (Real.log (148646740117 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (148646740117 / 100000000000) = -Real.log (100000000000 / 148646740117) := by
    rw [show ((148646740117 / 100000000000) : ℝ) = ((100000000000 / 148646740117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (280869987 / 1000000000) ≤ -Real.log (62500000000 / 82767588709) ∧
    -Real.log (62500000000 / 82767588709) ≤ (70217497 / 250000000) := by
  have h := checkLog_sound (w := (20267588709 / 145267588709)) (n := 12)
    (lo := (280869987 / 1000000000)) (hi := (70217497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82767588709 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82767588709 / 62500000000) = 1/(62500000000 / 82767588709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (280869987 / 1000000000) (70217497 / 250000000) (Real.log (82767588709 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (82767588709 / 62500000000) = -Real.log (62500000000 / 82767588709) := by
    rw [show ((82767588709 / 62500000000) : ℝ) = ((62500000000 / 82767588709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (281496203 / 1000000000) ≤ -Real.log (500000000000 / 662555482961) ∧
    -Real.log (500000000000 / 662555482961) ≤ (70374051 / 250000000) := by
  have h := checkLog_sound (w := (162555482961 / 1162555482961)) (n := 12)
    (lo := (281496203 / 1000000000)) (hi := (70374051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662555482961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(662555482961 / 500000000000) = 1/(500000000000 / 662555482961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (281496203 / 1000000000) (70374051 / 250000000) (Real.log (662555482961 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (662555482961 / 500000000000) = -Real.log (500000000000 / 662555482961) := by
    rw [show ((662555482961 / 500000000000) : ℝ) = ((500000000000 / 662555482961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3948993 / 200000000) ≤ -Real.log (245112172431 / 250000000000) ∧
    -Real.log (245112172431 / 250000000000) ≤ (9872483 / 500000000) := by
  have h := checkLog_sound (w := (4887827569 / 495112172431)) (n := 12)
    (lo := (3948993 / 200000000)) (hi := (9872483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245112172431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245112172431) = 1/(245112172431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9872483 / 500000000) (-3948993 / 200000000) (Real.log (245112172431 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7863 / 400000) ≤ -Real.log (980534448639 / 1000000000000) ∧
    -Real.log (980534448639 / 1000000000000) ≤ (19657501 / 1000000000) := by
  have h := checkLog_sound (w := (19465551361 / 1980534448639)) (n := 12)
    (lo := (7863 / 400000)) (hi := (19657501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980534448639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980534448639) = 1/(980534448639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19657501 / 1000000000) (-7863 / 400000) (Real.log (980534448639 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell043

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell044Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell044
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

theorem reflection_log_1_neg : (61004477 / 250000000) ≤ -Real.log (1024 / 1307) ∧
    -Real.log (1024 / 1307) ≤ (244017909 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 2331)) (n := 12)
    (lo := (61004477 / 250000000)) (hi := (244017909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307 / 1024) = 1/(1024 / 1307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (61004477 / 250000000) (244017909 / 1000000000) (Real.log (1307 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1307 / 1024) = -Real.log (1024 / 1307) := by
    rw [show ((1307 / 1024) : ℝ) = ((1024 / 1307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16173559 / 50000000) ≤ -Real.log (741 / 1024) ∧
    -Real.log (741 / 1024) ≤ (323471181 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1765)) (n := 12)
    (lo := (16173559 / 50000000)) (hi := (323471181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 741) = 1/(741 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-323471181 / 1000000000) (-16173559 / 50000000) (Real.log (741 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (15222421 / 62500000) ≤ -Real.log (1280 / 1633) ∧
    -Real.log (1280 / 1633) ≤ (243558737 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 2913)) (n := 12)
    (lo := (15222421 / 62500000)) (hi := (243558737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1633 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1633 / 1280) = 1/(1280 / 1633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (15222421 / 62500000) (243558737 / 1000000000) (Real.log (1633 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1633 / 1280) = -Real.log (1280 / 1633) := by
    rw [show ((1633 / 1280) : ℝ) = ((1280 / 1633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (322661791 / 1000000000) ≤ -Real.log (927 / 1280) ∧
    -Real.log (927 / 1280) ≤ (10083181 / 31250000) := by
  have h := checkLog_sound (w := (353 / 2207)) (n := 12)
    (lo := (322661791 / 1000000000)) (hi := (10083181 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 927) = 1/(927 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10083181 / 31250000) (-322661791 / 1000000000) (Real.log (927 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (22335619 / 125000000) ≤ -Real.log (250000 / 298911) ∧
    -Real.log (250000 / 298911) ≤ (178684953 / 1000000000) := by
  have h := checkLog_sound (w := (48911 / 548911)) (n := 12)
    (lo := (22335619 / 125000000)) (hi := (178684953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298911 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298911 / 250000) = 1/(250000 / 298911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (22335619 / 125000000) (178684953 / 1000000000) (Real.log (298911 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (298911 / 250000) = -Real.log (250000 / 298911) := by
    rw [show ((298911 / 250000) : ℝ) = ((250000 / 298911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (217713321 / 1000000000) ≤ -Real.log (201089 / 250000) ∧
    -Real.log (201089 / 250000) ≤ (108856661 / 500000000) := by
  have h := checkLog_sound (w := (48911 / 451089)) (n := 12)
    (lo := (217713321 / 1000000000)) (hi := (108856661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201089) = 1/(201089 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-108856661 / 500000000) (-217713321 / 1000000000) (Real.log (201089 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (35807233 / 200000000) ≤ -Real.log (31250 / 37377) ∧
    -Real.log (31250 / 37377) ≤ (89518083 / 500000000) := by
  have h := checkLog_sound (w := (6127 / 68627)) (n := 12)
    (lo := (35807233 / 200000000)) (hi := (89518083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37377 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37377 / 31250) = 1/(31250 / 37377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (35807233 / 200000000) (89518083 / 500000000) (Real.log (37377 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (37377 / 31250) = -Real.log (31250 / 37377) := by
    rw [show ((37377 / 31250) : ℝ) = ((31250 / 37377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (109117807 / 500000000) ≤ -Real.log (25123 / 31250) ∧
    -Real.log (25123 / 31250) ≤ (43647123 / 200000000) := by
  have h := checkLog_sound (w := (6127 / 56373)) (n := 12)
    (lo := (109117807 / 500000000)) (hi := (43647123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25123) = 1/(25123 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-43647123 / 200000000) (-109117807 / 500000000) (Real.log (25123 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (130874741 / 1000000000) ≤ -Real.log (40000 / 45593) ∧
    -Real.log (40000 / 45593) ≤ (65437371 / 500000000) := by
  have h := checkLog_sound (w := (5593 / 85593)) (n := 12)
    (lo := (130874741 / 1000000000)) (hi := (65437371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45593 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45593 / 40000) = 1/(40000 / 45593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (130874741 / 1000000000) (65437371 / 500000000) (Real.log (45593 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (45593 / 40000) = -Real.log (40000 / 45593) := by
    rw [show ((45593 / 40000) : ℝ) = ((40000 / 45593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (75309711 / 500000000) ≤ -Real.log (34407 / 40000) ∧
    -Real.log (34407 / 40000) ≤ (150619423 / 1000000000) := by
  have h := checkLog_sound (w := (5593 / 74407)) (n := 12)
    (lo := (75309711 / 500000000)) (hi := (150619423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34407) = 1/(34407 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-150619423 / 1000000000) (-75309711 / 500000000) (Real.log (34407 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256139 / 1953125) ≤ -Real.log (1000000 / 1140131) ∧
    -Real.log (1000000 / 1140131) ≤ (131143169 / 1000000000) := by
  have h := checkLog_sound (w := (140131 / 2140131)) (n := 12)
    (lo := (256139 / 1953125)) (hi := (131143169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1140131 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1140131 / 1000000) = 1/(1000000 / 1140131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256139 / 1953125) (131143169 / 1000000000) (Real.log (1140131 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1140131 / 1000000) = -Real.log (1000000 / 1140131) := by
    rw [show ((1140131 / 1000000) : ℝ) = ((1000000 / 1140131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (75487613 / 500000000) ≤ -Real.log (859869 / 1000000) ∧
    -Real.log (859869 / 1000000) ≤ (150975227 / 1000000000) := by
  have h := checkLog_sound (w := (140131 / 1859869)) (n := 12)
    (lo := (75487613 / 500000000)) (hi := (150975227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 859869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 859869) = 1/(859869 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-150975227 / 1000000000) (-75487613 / 500000000) (Real.log (859869 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (566220527 / 1000000000) ≤ -Real.log (250000000000 / 440399137001) ∧
    -Real.log (250000000000 / 440399137001) ≤ (35388783 / 62500000) := by
  have h := checkLog_sound (w := (190399137001 / 690399137001)) (n := 12)
    (lo := (566220527 / 1000000000)) (hi := (35388783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((440399137001 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(440399137001 / 250000000000) = 1/(250000000000 / 440399137001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (566220527 / 1000000000) (35388783 / 62500000) (Real.log (440399137001 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (440399137001 / 250000000000) = -Real.log (250000000000 / 440399137001) := by
    rw [show ((440399137001 / 250000000000) : ℝ) = ((250000000000 / 440399137001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (8867017 / 15625000) ≤ -Real.log (100000000000 / 176383265857) ∧
    -Real.log (100000000000 / 176383265857) ≤ (567489089 / 1000000000) := by
  have h := checkLog_sound (w := (76383265857 / 276383265857)) (n := 12)
    (lo := (8867017 / 15625000)) (hi := (567489089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176383265857 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176383265857 / 100000000000) = 1/(100000000000 / 176383265857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (8867017 / 15625000) (567489089 / 1000000000) (Real.log (176383265857 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (176383265857 / 100000000000) = -Real.log (100000000000 / 176383265857) := by
    rw [show ((176383265857 / 100000000000) : ℝ) = ((100000000000 / 176383265857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (198199137 / 500000000) ≤ -Real.log (125000000000 / 185807652333) ∧
    -Real.log (125000000000 / 185807652333) ≤ (15855931 / 40000000) := by
  have h := checkLog_sound (w := (60807652333 / 310807652333)) (n := 12)
    (lo := (198199137 / 500000000)) (hi := (15855931 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185807652333 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185807652333 / 125000000000) = 1/(125000000000 / 185807652333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (198199137 / 500000000) (15855931 / 40000000) (Real.log (185807652333 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (185807652333 / 125000000000) = -Real.log (125000000000 / 185807652333) := by
    rw [show ((185807652333 / 125000000000) : ℝ) = ((125000000000 / 185807652333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (19863589 / 50000000) ≤ -Real.log (25000000000 / 37194005493) ∧
    -Real.log (25000000000 / 37194005493) ≤ (397271781 / 1000000000) := by
  have h := checkLog_sound (w := (12194005493 / 62194005493)) (n := 12)
    (lo := (19863589 / 50000000)) (hi := (397271781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37194005493 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37194005493 / 25000000000) = 1/(25000000000 / 37194005493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (19863589 / 50000000) (397271781 / 1000000000) (Real.log (37194005493 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (37194005493 / 25000000000) = -Real.log (25000000000 / 37194005493) := by
    rw [show ((37194005493 / 25000000000) : ℝ) = ((25000000000 / 37194005493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (281494163 / 1000000000) ≤ -Real.log (250000000000 / 331277065713) ∧
    -Real.log (250000000000 / 331277065713) ≤ (70373541 / 250000000) := by
  have h := checkLog_sound (w := (81277065713 / 581277065713)) (n := 12)
    (lo := (281494163 / 1000000000)) (hi := (70373541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331277065713 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331277065713 / 250000000000) = 1/(250000000000 / 331277065713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (281494163 / 1000000000) (70373541 / 250000000) (Real.log (331277065713 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (331277065713 / 250000000000) = -Real.log (250000000000 / 331277065713) := by
    rw [show ((331277065713 / 250000000000) : ℝ) = ((250000000000 / 331277065713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (56423679 / 200000000) ≤ -Real.log (125000000000 / 165741961857) ∧
    -Real.log (125000000000 / 165741961857) ≤ (70529599 / 250000000) := by
  have h := checkLog_sound (w := (40741961857 / 290741961857)) (n := 12)
    (lo := (56423679 / 200000000)) (hi := (70529599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165741961857 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165741961857 / 125000000000) = 1/(125000000000 / 165741961857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (56423679 / 200000000) (70529599 / 250000000) (Real.log (165741961857 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (165741961857 / 125000000000) = -Real.log (125000000000 / 165741961857) := by
    rw [show ((165741961857 / 125000000000) : ℝ) = ((125000000000 / 165741961857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9916029 / 500000000) ≤ -Real.log (980363302839 / 1000000000000) ∧
    -Real.log (980363302839 / 1000000000000) ≤ (19832059 / 1000000000) := by
  have h := checkLog_sound (w := (19636697161 / 1980363302839)) (n := 12)
    (lo := (9916029 / 500000000)) (hi := (19832059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980363302839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980363302839) = 1/(980363302839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19832059 / 1000000000) (-9916029 / 500000000) (Real.log (980363302839 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (493617 / 25000000) ≤ -Real.log (1568718351 / 1600000000) ∧
    -Real.log (1568718351 / 1600000000) ≤ (19744681 / 1000000000) := by
  have h := checkLog_sound (w := (31281649 / 3168718351)) (n := 12)
    (lo := (493617 / 25000000)) (hi := (19744681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1568718351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1568718351) = 1/(1568718351 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19744681 / 1000000000) (-493617 / 25000000) (Real.log (1568718351 / 1600000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell044

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell045Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell045
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

theorem reflection_log_1_neg : (244476869 / 1000000000) ≤ -Real.log (2560 / 3269) ∧
    -Real.log (2560 / 3269) ≤ (24447687 / 100000000) := by
  have h := checkLog_sound (w := (709 / 5829)) (n := 12)
    (lo := (244476869 / 1000000000)) (hi := (24447687 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3269 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3269 / 2560) = 1/(2560 / 3269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (244476869 / 1000000000) (24447687 / 100000000) (Real.log (3269 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3269 / 2560) = -Real.log (2560 / 3269) := by
    rw [show ((3269 / 2560) : ℝ) = ((2560 / 3269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (40535153 / 125000000) ≤ -Real.log (1851 / 2560) ∧
    -Real.log (1851 / 2560) ≤ (12971249 / 40000000) := by
  have h := checkLog_sound (w := (709 / 4411)) (n := 12)
    (lo := (40535153 / 125000000)) (hi := (12971249 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1851) = 1/(1851 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12971249 / 40000000) (-40535153 / 125000000) (Real.log (1851 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (61004477 / 250000000) ≤ -Real.log (1024 / 1307) ∧
    -Real.log (1024 / 1307) ≤ (244017909 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 2331)) (n := 12)
    (lo := (61004477 / 250000000)) (hi := (244017909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307 / 1024) = 1/(1024 / 1307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (61004477 / 250000000) (244017909 / 1000000000) (Real.log (1307 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1307 / 1024) = -Real.log (1024 / 1307) := by
    rw [show ((1307 / 1024) : ℝ) = ((1024 / 1307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16173559 / 50000000) ≤ -Real.log (741 / 1024) ∧
    -Real.log (741 / 1024) ≤ (323471181 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1765)) (n := 12)
    (lo := (16173559 / 50000000)) (hi := (323471181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 741) = 1/(741 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-323471181 / 1000000000) (-16173559 / 50000000) (Real.log (741 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (179035329 / 1000000000) ≤ -Real.log (1000000 / 1196063) ∧
    -Real.log (1000000 / 1196063) ≤ (17903533 / 100000000) := by
  have h := checkLog_sound (w := (196063 / 2196063)) (n := 12)
    (lo := (179035329 / 1000000000)) (hi := (17903533 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196063 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196063 / 1000000) = 1/(1000000 / 1196063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (179035329 / 1000000000) (17903533 / 100000000) (Real.log (1196063 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1196063 / 1000000) = -Real.log (1000000 / 1196063) := by
    rw [show ((1196063 / 1000000) : ℝ) = ((1000000 / 1196063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (218234371 / 1000000000) ≤ -Real.log (803937 / 1000000) ∧
    -Real.log (803937 / 1000000) ≤ (54558593 / 250000000) := by
  have h := checkLog_sound (w := (196063 / 1803937)) (n := 12)
    (lo := (218234371 / 1000000000)) (hi := (54558593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803937) = 1/(803937 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-54558593 / 250000000) (-218234371 / 1000000000) (Real.log (803937 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8969321 / 50000000) ≤ -Real.log (1000000 / 1196483) ∧
    -Real.log (1000000 / 1196483) ≤ (179386421 / 1000000000) := by
  have h := checkLog_sound (w := (196483 / 2196483)) (n := 12)
    (lo := (8969321 / 50000000)) (hi := (179386421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196483 / 1000000) = 1/(1000000 / 1196483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8969321 / 50000000) (179386421 / 1000000000) (Real.log (1196483 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1196483 / 1000000) = -Real.log (1000000 / 1196483) := by
    rw [show ((1196483 / 1000000) : ℝ) = ((1000000 / 1196483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (27344617 / 125000000) ≤ -Real.log (803517 / 1000000) ∧
    -Real.log (803517 / 1000000) ≤ (218756937 / 1000000000) := by
  have h := checkLog_sound (w := (196483 / 1803517)) (n := 12)
    (lo := (27344617 / 125000000)) (hi := (218756937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803517) = 1/(803517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-218756937 / 1000000000) (-27344617 / 125000000) (Real.log (803517 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (13114229 / 100000000) ≤ -Real.log (100000 / 114013) ∧
    -Real.log (100000 / 114013) ≤ (131142291 / 1000000000) := by
  have h := checkLog_sound (w := (14013 / 214013)) (n := 12)
    (lo := (13114229 / 100000000)) (hi := (131142291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114013 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114013 / 100000) = 1/(100000 / 114013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (13114229 / 100000000) (131142291 / 1000000000) (Real.log (114013 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (114013 / 100000) = -Real.log (100000 / 114013) := by
    rw [show ((114013 / 100000) : ℝ) = ((100000 / 114013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (150974063 / 1000000000) ≤ -Real.log (85987 / 100000) ∧
    -Real.log (85987 / 100000) ≤ (9435879 / 62500000) := by
  have h := checkLog_sound (w := (14013 / 185987)) (n := 12)
    (lo := (150974063 / 1000000000)) (hi := (9435879 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85987) = 1/(85987 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9435879 / 62500000) (-150974063 / 1000000000) (Real.log (85987 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65705761 / 500000000) ≤ -Real.log (1000000 / 1140437) ∧
    -Real.log (1000000 / 1140437) ≤ (131411523 / 1000000000) := by
  have h := checkLog_sound (w := (140437 / 2140437)) (n := 12)
    (lo := (65705761 / 500000000)) (hi := (131411523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1140437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1140437 / 1000000) = 1/(1000000 / 1140437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65705761 / 500000000) (131411523 / 1000000000) (Real.log (1140437 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1140437 / 1000000) = -Real.log (1000000 / 1140437) := by
    rw [show ((1140437 / 1000000) : ℝ) = ((1000000 / 1140437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (75665579 / 500000000) ≤ -Real.log (859563 / 1000000) ∧
    -Real.log (859563 / 1000000) ≤ (151331159 / 1000000000) := by
  have h := checkLog_sound (w := (140437 / 1859563)) (n := 12)
    (lo := (75665579 / 500000000)) (hi := (151331159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 859563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 859563) = 1/(859563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-151331159 / 1000000000) (-75665579 / 500000000) (Real.log (859563 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8867017 / 15625000) ≤ -Real.log (125000000000 / 220479082321) ∧
    -Real.log (125000000000 / 220479082321) ≤ (567489089 / 1000000000) := by
  have h := checkLog_sound (w := (95479082321 / 345479082321)) (n := 12)
    (lo := (8867017 / 15625000)) (hi := (567489089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220479082321 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220479082321 / 125000000000) = 1/(125000000000 / 220479082321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8867017 / 15625000) (567489089 / 1000000000) (Real.log (220479082321 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (220479082321 / 125000000000) = -Real.log (125000000000 / 220479082321) := by
    rw [show ((220479082321 / 125000000000) : ℝ) = ((125000000000 / 220479082321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (284379047 / 500000000) ≤ -Real.log (500000000000 / 883036196651) ∧
    -Real.log (500000000000 / 883036196651) ≤ (113751619 / 200000000) := by
  have h := checkLog_sound (w := (383036196651 / 1383036196651)) (n := 12)
    (lo := (284379047 / 500000000)) (hi := (113751619 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((883036196651 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(883036196651 / 500000000000) = 1/(500000000000 / 883036196651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (284379047 / 500000000) (113751619 / 200000000) (Real.log (883036196651 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (883036196651 / 500000000000) = -Real.log (500000000000 / 883036196651) := by
    rw [show ((883036196651 / 500000000000) : ℝ) = ((500000000000 / 883036196651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (3972697 / 10000000) ≤ -Real.log (500000000000 / 743878562623) ∧
    -Real.log (500000000000 / 743878562623) ≤ (397269701 / 1000000000) := by
  have h := checkLog_sound (w := (243878562623 / 1243878562623)) (n := 12)
    (lo := (3972697 / 10000000)) (hi := (397269701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743878562623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743878562623 / 500000000000) = 1/(500000000000 / 743878562623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (3972697 / 10000000) (397269701 / 1000000000) (Real.log (743878562623 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (743878562623 / 500000000000) = -Real.log (500000000000 / 743878562623) := by
    rw [show ((743878562623 / 500000000000) : ℝ) = ((500000000000 / 743878562623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (99535839 / 250000000) ≤ -Real.log (20000000000 / 29781149621) ∧
    -Real.log (20000000000 / 29781149621) ≤ (398143357 / 1000000000) := by
  have h := checkLog_sound (w := (9781149621 / 49781149621)) (n := 12)
    (lo := (99535839 / 250000000)) (hi := (398143357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29781149621 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29781149621 / 20000000000) = 1/(20000000000 / 29781149621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (99535839 / 250000000) (398143357 / 1000000000) (Real.log (29781149621 / 20000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (29781149621 / 20000000000) = -Real.log (20000000000 / 29781149621) := by
    rw [show ((29781149621 / 20000000000) : ℝ) = ((20000000000 / 29781149621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (141058177 / 500000000) ≤ -Real.log (100000000000 / 132593298987) ∧
    -Real.log (100000000000 / 132593298987) ≤ (56423271 / 200000000) := by
  have h := checkLog_sound (w := (32593298987 / 232593298987)) (n := 12)
    (lo := (141058177 / 500000000)) (hi := (56423271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132593298987 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132593298987 / 100000000000) = 1/(100000000000 / 132593298987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (141058177 / 500000000) (56423271 / 200000000) (Real.log (132593298987 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (132593298987 / 100000000000) = -Real.log (100000000000 / 132593298987) := by
    rw [show ((132593298987 / 100000000000) : ℝ) = ((100000000000 / 132593298987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (7068567 / 25000000) ≤ -Real.log (500000000000 / 663381857991) ∧
    -Real.log (500000000000 / 663381857991) ≤ (282742681 / 1000000000) := by
  have h := checkLog_sound (w := (163381857991 / 1163381857991)) (n := 12)
    (lo := (7068567 / 25000000)) (hi := (282742681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663381857991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663381857991 / 500000000000) = 1/(500000000000 / 663381857991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (7068567 / 25000000) (282742681 / 1000000000) (Real.log (663381857991 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (663381857991 / 500000000000) = -Real.log (500000000000 / 663381857991) := by
    rw [show ((663381857991 / 500000000000) : ℝ) = ((500000000000 / 663381857991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4979909 / 250000000) ≤ -Real.log (980277449031 / 1000000000000) ∧
    -Real.log (980277449031 / 1000000000000) ≤ (19919637 / 1000000000) := by
  have h := checkLog_sound (w := (19722550969 / 1980277449031)) (n := 12)
    (lo := (4979909 / 250000000)) (hi := (19919637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980277449031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980277449031) = 1/(980277449031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19919637 / 1000000000) (-4979909 / 250000000) (Real.log (980277449031 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4957943 / 250000000) ≤ -Real.log (9803635831 / 10000000000) ∧
    -Real.log (9803635831 / 10000000000) ≤ (19831773 / 1000000000) := by
  have h := checkLog_sound (w := (196364169 / 19803635831)) (n := 12)
    (lo := (4957943 / 250000000)) (hi := (19831773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9803635831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9803635831) = 1/(9803635831 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19831773 / 1000000000) (-4957943 / 250000000) (Real.log (9803635831 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell045

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell046Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell046
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

theorem reflection_log_1_neg : (244935619 / 1000000000) ≤ -Real.log (5120 / 6541) ∧
    -Real.log (5120 / 6541) ≤ (12246781 / 50000000) := by
  have h := checkLog_sound (w := (1421 / 11661)) (n := 12)
    (lo := (244935619 / 1000000000)) (hi := (12246781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6541 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6541 / 5120) = 1/(5120 / 6541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (244935619 / 1000000000) (12246781 / 50000000) (Real.log (6541 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6541 / 5120) = -Real.log (5120 / 6541) := by
    rw [show ((6541 / 5120) : ℝ) = ((5120 / 6541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (162545963 / 500000000) ≤ -Real.log (3699 / 5120) ∧
    -Real.log (3699 / 5120) ≤ (325091927 / 1000000000) := by
  have h := checkLog_sound (w := (1421 / 8819)) (n := 12)
    (lo := (162545963 / 500000000)) (hi := (325091927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3699) = 1/(3699 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-325091927 / 1000000000) (-162545963 / 500000000) (Real.log (3699 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (244476869 / 1000000000) ≤ -Real.log (2560 / 3269) ∧
    -Real.log (2560 / 3269) ≤ (24447687 / 100000000) := by
  have h := checkLog_sound (w := (709 / 5829)) (n := 12)
    (lo := (244476869 / 1000000000)) (hi := (24447687 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3269 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3269 / 2560) = 1/(2560 / 3269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (244476869 / 1000000000) (24447687 / 100000000) (Real.log (3269 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3269 / 2560) = -Real.log (2560 / 3269) := by
    rw [show ((3269 / 2560) : ℝ) = ((2560 / 3269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (40535153 / 125000000) ≤ -Real.log (1851 / 2560) ∧
    -Real.log (1851 / 2560) ≤ (12971249 / 40000000) := by
  have h := checkLog_sound (w := (709 / 4411)) (n := 12)
    (lo := (40535153 / 125000000)) (hi := (12971249 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1851) = 1/(1851 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12971249 / 40000000) (-40535153 / 125000000) (Real.log (1851 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (44846187 / 250000000) ≤ -Real.log (1000000 / 1196481) ∧
    -Real.log (1000000 / 1196481) ≤ (179384749 / 1000000000) := by
  have h := checkLog_sound (w := (196481 / 2196481)) (n := 12)
    (lo := (44846187 / 250000000)) (hi := (179384749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196481 / 1000000) = 1/(1000000 / 1196481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (44846187 / 250000000) (179384749 / 1000000000) (Real.log (1196481 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1196481 / 1000000) = -Real.log (1000000 / 1196481) := by
    rw [show ((1196481 / 1000000) : ℝ) = ((1000000 / 1196481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (218754447 / 1000000000) ≤ -Real.log (803519 / 1000000) ∧
    -Real.log (803519 / 1000000) ≤ (13672153 / 62500000) := by
  have h := checkLog_sound (w := (196481 / 1803519)) (n := 12)
    (lo := (218754447 / 1000000000)) (hi := (13672153 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803519) = 1/(803519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-13672153 / 62500000) (-218754447 / 1000000000) (Real.log (803519 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44933929 / 250000000) ≤ -Real.log (1000000 / 1196901) ∧
    -Real.log (1000000 / 1196901) ≤ (179735717 / 1000000000) := by
  have h := checkLog_sound (w := (196901 / 2196901)) (n := 12)
    (lo := (44933929 / 250000000)) (hi := (179735717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196901 / 1000000) = 1/(1000000 / 1196901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44933929 / 250000000) (179735717 / 1000000000) (Real.log (1196901 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1196901 / 1000000) = -Real.log (1000000 / 1196901) := by
    rw [show ((1196901 / 1000000) : ℝ) = ((1000000 / 1196901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (54819321 / 250000000) ≤ -Real.log (803099 / 1000000) ∧
    -Real.log (803099 / 1000000) ≤ (43855457 / 200000000) := by
  have h := checkLog_sound (w := (196901 / 1803099)) (n := 12)
    (lo := (54819321 / 250000000)) (hi := (43855457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803099) = 1/(803099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-43855457 / 200000000) (-54819321 / 250000000) (Real.log (803099 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (26282129 / 200000000) ≤ -Real.log (250000 / 285109) ∧
    -Real.log (250000 / 285109) ≤ (65705323 / 500000000) := by
  have h := checkLog_sound (w := (35109 / 535109)) (n := 12)
    (lo := (26282129 / 200000000)) (hi := (65705323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285109 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285109 / 250000) = 1/(250000 / 285109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (26282129 / 200000000) (65705323 / 500000000) (Real.log (285109 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (285109 / 250000) = -Real.log (250000 / 285109) := by
    rw [show ((285109 / 250000) : ℝ) = ((250000 / 285109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (30265999 / 200000000) ≤ -Real.log (214891 / 250000) ∧
    -Real.log (214891 / 250000) ≤ (37832499 / 250000000) := by
  have h := checkLog_sound (w := (35109 / 464891)) (n := 12)
    (lo := (30265999 / 200000000)) (hi := (37832499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 214891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 214891) = 1/(214891 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37832499 / 250000000) (-30265999 / 200000000) (Real.log (214891 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (131678927 / 1000000000) ≤ -Real.log (500000 / 570371) ∧
    -Real.log (500000 / 570371) ≤ (8229933 / 62500000) := by
  have h := checkLog_sound (w := (70371 / 1070371)) (n := 12)
    (lo := (131678927 / 1000000000)) (hi := (8229933 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570371 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570371 / 500000) = 1/(500000 / 570371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (131678927 / 1000000000) (8229933 / 62500000) (Real.log (570371 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (570371 / 500000) = -Real.log (500000 / 570371) := by
    rw [show ((570371 / 500000) : ℝ) = ((500000 / 570371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (37921513 / 250000000) ≤ -Real.log (429629 / 500000) ∧
    -Real.log (429629 / 500000) ≤ (151686053 / 1000000000) := by
  have h := checkLog_sound (w := (70371 / 929629)) (n := 12)
    (lo := (37921513 / 250000000)) (hi := (151686053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429629) = 1/(429629 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-151686053 / 1000000000) (-37921513 / 250000000) (Real.log (429629 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (284379047 / 500000000) ≤ -Real.log (10000000000 / 17660723933) ∧
    -Real.log (10000000000 / 17660723933) ≤ (113751619 / 200000000) := by
  have h := checkLog_sound (w := (7660723933 / 27660723933)) (n := 12)
    (lo := (284379047 / 500000000)) (hi := (113751619 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17660723933 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17660723933 / 10000000000) = 1/(10000000000 / 17660723933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (284379047 / 500000000) (113751619 / 200000000) (Real.log (17660723933 / 10000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (17660723933 / 10000000000) = -Real.log (10000000000 / 17660723933) := by
    rw [show ((17660723933 / 10000000000) : ℝ) = ((10000000000 / 17660723933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (285013773 / 500000000) ≤ -Real.log (500000000000 / 884157880509) ∧
    -Real.log (500000000000 / 884157880509) ≤ (570027547 / 1000000000) := by
  have h := checkLog_sound (w := (384157880509 / 1384157880509)) (n := 12)
    (lo := (285013773 / 500000000)) (hi := (570027547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884157880509 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884157880509 / 500000000000) = 1/(500000000000 / 884157880509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (285013773 / 500000000) (570027547 / 1000000000) (Real.log (884157880509 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (884157880509 / 500000000000) = -Real.log (500000000000 / 884157880509) := by
    rw [show ((884157880509 / 500000000000) : ℝ) = ((500000000000 / 884157880509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (99534799 / 250000000) ≤ -Real.log (125000000000 / 186131410707) ∧
    -Real.log (125000000000 / 186131410707) ≤ (398139197 / 1000000000) := by
  have h := checkLog_sound (w := (61131410707 / 311131410707)) (n := 12)
    (lo := (99534799 / 250000000)) (hi := (398139197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186131410707 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186131410707 / 125000000000) = 1/(125000000000 / 186131410707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (99534799 / 250000000) (398139197 / 1000000000) (Real.log (186131410707 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (186131410707 / 125000000000) = -Real.log (125000000000 / 186131410707) := by
    rw [show ((186131410707 / 125000000000) : ℝ) = ((125000000000 / 186131410707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (399013001 / 1000000000) ≤ -Real.log (500000000000 / 745176497543) ∧
    -Real.log (500000000000 / 745176497543) ≤ (199506501 / 500000000) := by
  have h := checkLog_sound (w := (245176497543 / 1245176497543)) (n := 12)
    (lo := (399013001 / 1000000000)) (hi := (199506501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745176497543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745176497543 / 500000000000) = 1/(500000000000 / 745176497543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (399013001 / 1000000000) (199506501 / 500000000) (Real.log (745176497543 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (745176497543 / 500000000000) = -Real.log (500000000000 / 745176497543) := by
    rw [show ((745176497543 / 500000000000) : ℝ) = ((500000000000 / 745176497543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (1767129 / 6250000) ≤ -Real.log (250000000000 / 331690252267) ∧
    -Real.log (250000000000 / 331690252267) ≤ (282740641 / 1000000000) := by
  have h := checkLog_sound (w := (81690252267 / 581690252267)) (n := 12)
    (lo := (1767129 / 6250000)) (hi := (282740641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331690252267 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331690252267 / 250000000000) = 1/(250000000000 / 331690252267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1767129 / 6250000) (282740641 / 1000000000) (Real.log (331690252267 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (331690252267 / 250000000000) = -Real.log (250000000000 / 331690252267) := by
    rw [show ((331690252267 / 250000000000) : ℝ) = ((250000000000 / 331690252267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (14168249 / 50000000) ≤ -Real.log (50000000000 / 66379480901) ∧
    -Real.log (50000000000 / 66379480901) ≤ (283364981 / 1000000000) := by
  have h := checkLog_sound (w := (16379480901 / 116379480901)) (n := 12)
    (lo := (14168249 / 50000000)) (hi := (283364981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66379480901 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66379480901 / 50000000000) = 1/(50000000000 / 66379480901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (14168249 / 50000000) (283364981 / 1000000000) (Real.log (66379480901 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (66379480901 / 50000000000) = -Real.log (50000000000 / 66379480901) := by
    rw [show ((66379480901 / 50000000000) : ℝ) = ((50000000000 / 66379480901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5001781 / 250000000) ≤ -Real.log (245047922359 / 250000000000) ∧
    -Real.log (245047922359 / 250000000000) ≤ (160057 / 8000000) := by
  have h := checkLog_sound (w := (4952077641 / 495047922359)) (n := 12)
    (lo := (5001781 / 250000000)) (hi := (160057 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245047922359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245047922359) = 1/(245047922359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-160057 / 8000000) (-5001781 / 250000000) (Real.log (245047922359 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19919349 / 1000000000) ≤ -Real.log (61267358119 / 62500000000) ∧
    -Real.log (61267358119 / 62500000000) ≤ (398387 / 20000000) := by
  have h := checkLog_sound (w := (1232641881 / 123767358119)) (n := 12)
    (lo := (19919349 / 1000000000)) (hi := (398387 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61267358119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61267358119) = 1/(61267358119 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-398387 / 20000000) (-19919349 / 1000000000) (Real.log (61267358119 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell046

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell047Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell047
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

theorem reflection_log_1_neg : (3067427 / 12500000) ≤ -Real.log (320 / 409) ∧
    -Real.log (320 / 409) ≤ (245394161 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 729)) (n := 12)
    (lo := (3067427 / 12500000)) (hi := (245394161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409 / 320) = 1/(320 / 409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (3067427 / 12500000) (245394161 / 1000000000) (Real.log (409 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (409 / 320) = -Real.log (320 / 409) := by
    rw [show ((409 / 320) : ℝ) = ((320 / 409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (65180657 / 200000000) ≤ -Real.log (231 / 320) ∧
    -Real.log (231 / 320) ≤ (162951643 / 500000000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 231) = 1/(231 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-162951643 / 500000000) (-65180657 / 200000000) (Real.log (231 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (244935619 / 1000000000) ≤ -Real.log (5120 / 6541) ∧
    -Real.log (5120 / 6541) ≤ (12246781 / 50000000) := by
  have h := checkLog_sound (w := (1421 / 11661)) (n := 12)
    (lo := (244935619 / 1000000000)) (hi := (12246781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6541 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6541 / 5120) = 1/(5120 / 6541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (244935619 / 1000000000) (12246781 / 50000000) (Real.log (6541 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6541 / 5120) = -Real.log (5120 / 6541) := by
    rw [show ((6541 / 5120) : ℝ) = ((5120 / 6541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (162545963 / 500000000) ≤ -Real.log (3699 / 5120) ∧
    -Real.log (3699 / 5120) ≤ (325091927 / 1000000000) := by
  have h := checkLog_sound (w := (1421 / 8819)) (n := 12)
    (lo := (162545963 / 500000000)) (hi := (325091927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3699) = 1/(3699 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-325091927 / 1000000000) (-162545963 / 500000000) (Real.log (3699 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1123343 / 6250000) ≤ -Real.log (10000 / 11969) ∧
    -Real.log (10000 / 11969) ≤ (179734881 / 1000000000) := by
  have h := checkLog_sound (w := (1969 / 21969)) (n := 12)
    (lo := (1123343 / 6250000)) (hi := (179734881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11969 / 10000) = 1/(10000 / 11969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1123343 / 6250000) (179734881 / 1000000000) (Real.log (11969 / 10000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11969 / 10000) = -Real.log (10000 / 11969) := by
    rw [show ((11969 / 10000) : ℝ) = ((10000 / 11969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (219276039 / 1000000000) ≤ -Real.log (8031 / 10000) ∧
    -Real.log (8031 / 10000) ≤ (5481901 / 25000000) := by
  have h := checkLog_sound (w := (1969 / 18031)) (n := 12)
    (lo := (219276039 / 1000000000)) (hi := (5481901 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8031) = 1/(8031 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5481901 / 25000000) (-219276039 / 1000000000) (Real.log (8031 / 10000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7203429 / 40000000) ≤ -Real.log (25000 / 29933) ∧
    -Real.log (25000 / 29933) ≤ (90042863 / 500000000) := by
  have h := checkLog_sound (w := (4933 / 54933)) (n := 12)
    (lo := (7203429 / 40000000)) (hi := (90042863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29933 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29933 / 25000) = 1/(25000 / 29933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7203429 / 40000000) (90042863 / 500000000) (Real.log (29933 / 25000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (29933 / 25000) = -Real.log (25000 / 29933) := by
    rw [show ((29933 / 25000) : ℝ) = ((25000 / 29933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4395983 / 20000000) ≤ -Real.log (20067 / 25000) ∧
    -Real.log (20067 / 25000) ≤ (219799151 / 1000000000) := by
  have h := checkLog_sound (w := (4933 / 45067)) (n := 12)
    (lo := (4395983 / 20000000)) (hi := (219799151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20067) = 1/(20067 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-219799151 / 1000000000) (-4395983 / 20000000) (Real.log (20067 / 25000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131678051 / 1000000000) ≤ -Real.log (1000000 / 1140741) ∧
    -Real.log (1000000 / 1140741) ≤ (32919513 / 250000000) := by
  have h := checkLog_sound (w := (140741 / 2140741)) (n := 12)
    (lo := (131678051 / 1000000000)) (hi := (32919513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1140741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1140741 / 1000000) = 1/(1000000 / 1140741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131678051 / 1000000000) (32919513 / 250000000) (Real.log (1140741 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1140741 / 1000000) = -Real.log (1000000 / 1140741) := by
    rw [show ((1140741 / 1000000) : ℝ) = ((1000000 / 1140741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (151684889 / 1000000000) ≤ -Real.log (859259 / 1000000) ∧
    -Real.log (859259 / 1000000) ≤ (15168489 / 100000000) := by
  have h := checkLog_sound (w := (140741 / 1859259)) (n := 12)
    (lo := (151684889 / 1000000000)) (hi := (15168489 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 859259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 859259) = 1/(859259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-15168489 / 100000000) (-151684889 / 1000000000) (Real.log (859259 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65973569 / 500000000) ≤ -Real.log (125000 / 142631) ∧
    -Real.log (125000 / 142631) ≤ (131947139 / 1000000000) := by
  have h := checkLog_sound (w := (17631 / 267631)) (n := 12)
    (lo := (65973569 / 500000000)) (hi := (131947139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142631 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142631 / 125000) = 1/(125000 / 142631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65973569 / 500000000) (131947139 / 1000000000) (Real.log (142631 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (142631 / 125000) = -Real.log (125000 / 142631) := by
    rw [show ((142631 / 125000) : ℝ) = ((125000 / 142631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (152042237 / 1000000000) ≤ -Real.log (107369 / 125000) ∧
    -Real.log (107369 / 125000) ≤ (76021119 / 500000000) := by
  have h := checkLog_sound (w := (17631 / 232369)) (n := 12)
    (lo := (152042237 / 1000000000)) (hi := (76021119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107369) = 1/(107369 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-76021119 / 500000000) (-152042237 / 1000000000) (Real.log (107369 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (285013773 / 500000000) ≤ -Real.log (125000000000 / 221039470127) ∧
    -Real.log (125000000000 / 221039470127) ≤ (570027547 / 1000000000) := by
  have h := checkLog_sound (w := (96039470127 / 346039470127)) (n := 12)
    (lo := (285013773 / 500000000)) (hi := (570027547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221039470127 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221039470127 / 125000000000) = 1/(125000000000 / 221039470127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (285013773 / 500000000) (570027547 / 1000000000) (Real.log (221039470127 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (221039470127 / 125000000000) = -Real.log (125000000000 / 221039470127) := by
    rw [show ((221039470127 / 125000000000) : ℝ) = ((125000000000 / 221039470127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (114259489 / 200000000) ≤ -Real.log (250000000000 / 442640692641) ∧
    -Real.log (250000000000 / 442640692641) ≤ (285648723 / 500000000) := by
  have h := checkLog_sound (w := (192640692641 / 692640692641)) (n := 12)
    (lo := (114259489 / 200000000)) (hi := (285648723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((442640692641 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(442640692641 / 250000000000) = 1/(250000000000 / 442640692641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (114259489 / 200000000) (285648723 / 500000000) (Real.log (442640692641 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (442640692641 / 250000000000) = -Real.log (250000000000 / 442640692641) := by
    rw [show ((442640692641 / 250000000000) : ℝ) = ((250000000000 / 442640692641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (9975273 / 25000000) ≤ -Real.log (12500000000 / 18629373677) ∧
    -Real.log (12500000000 / 18629373677) ≤ (399010921 / 1000000000) := by
  have h := checkLog_sound (w := (6129373677 / 31129373677)) (n := 12)
    (lo := (9975273 / 25000000)) (hi := (399010921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18629373677 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18629373677 / 12500000000) = 1/(12500000000 / 18629373677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9975273 / 25000000) (399010921 / 1000000000) (Real.log (18629373677 / 12500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (18629373677 / 12500000000) = -Real.log (12500000000 / 18629373677) := by
    rw [show ((18629373677 / 12500000000) : ℝ) = ((12500000000 / 18629373677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3199079 / 8000000) ≤ -Real.log (62500000000 / 93228310161) ∧
    -Real.log (62500000000 / 93228310161) ≤ (99971219 / 250000000) := by
  have h := checkLog_sound (w := (30728310161 / 155728310161)) (n := 12)
    (lo := (3199079 / 8000000)) (hi := (99971219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93228310161 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93228310161 / 62500000000) = 1/(62500000000 / 93228310161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (3199079 / 8000000) (99971219 / 250000000) (Real.log (93228310161 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (93228310161 / 62500000000) = -Real.log (62500000000 / 93228310161) := by
    rw [show ((93228310161 / 62500000000) : ℝ) = ((62500000000 / 93228310161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14168147 / 50000000) ≤ -Real.log (976562500 / 1296471591) ∧
    -Real.log (976562500 / 1296471591) ≤ (283362941 / 1000000000) := by
  have h := checkLog_sound (w := (319909091 / 2273034091)) (n := 12)
    (lo := (14168147 / 50000000)) (hi := (283362941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1296471591 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1296471591 / 976562500) = 1/(976562500 / 1296471591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14168147 / 50000000) (283362941 / 1000000000) (Real.log (1296471591 / 976562500)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1296471591 / 976562500) = -Real.log (976562500 / 1296471591) := by
    rw [show ((1296471591 / 976562500) : ℝ) = ((976562500 / 1296471591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (454383 / 1600000) ≤ -Real.log (20000000000 / 26568376347) ∧
    -Real.log (20000000000 / 26568376347) ≤ (2218667 / 7812500) := by
  have h := checkLog_sound (w := (6568376347 / 46568376347)) (n := 12)
    (lo := (454383 / 1600000)) (hi := (2218667 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26568376347 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26568376347 / 20000000000) = 1/(20000000000 / 26568376347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (454383 / 1600000) (2218667 / 7812500) (Real.log (26568376347 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (26568376347 / 20000000000) = -Real.log (20000000000 / 26568376347) := by
    rw [show ((26568376347 / 20000000000) : ℝ) = ((20000000000 / 26568376347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20095099 / 1000000000) ≤ -Real.log (15314147839 / 15625000000) ∧
    -Real.log (15314147839 / 15625000000) ≤ (200951 / 10000000) := by
  have h := checkLog_sound (w := (310852161 / 30939147839)) (n := 12)
    (lo := (20095099 / 1000000000)) (hi := (200951 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15314147839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15314147839) = 1/(15314147839 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-200951 / 10000000) (-20095099 / 1000000000) (Real.log (15314147839 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20006837 / 1000000000) ≤ -Real.log (980191970919 / 1000000000000) ∧
    -Real.log (980191970919 / 1000000000000) ≤ (10003419 / 500000000) := by
  have h := checkLog_sound (w := (19808029081 / 1980191970919)) (n := 12)
    (lo := (20006837 / 1000000000)) (hi := (10003419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980191970919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980191970919) = 1/(980191970919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10003419 / 500000000) (-20006837 / 1000000000) (Real.log (980191970919 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell047

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell048Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell048
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

theorem reflection_log_1_neg : (24585249 / 100000000) ≤ -Real.log (5120 / 6547) ∧
    -Real.log (5120 / 6547) ≤ (245852491 / 1000000000) := by
  have h := checkLog_sound (w := (1427 / 11667)) (n := 12)
    (lo := (24585249 / 100000000)) (hi := (245852491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6547 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6547 / 5120) = 1/(5120 / 6547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24585249 / 100000000) (245852491 / 1000000000) (Real.log (6547 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6547 / 5120) = -Real.log (5120 / 6547) := by
    rw [show ((6547 / 5120) : ℝ) = ((5120 / 6547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (326715303 / 1000000000) ≤ -Real.log (3693 / 5120) ∧
    -Real.log (3693 / 5120) ≤ (40839413 / 125000000) := by
  have h := checkLog_sound (w := (1427 / 8813)) (n := 12)
    (lo := (326715303 / 1000000000)) (hi := (40839413 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3693) = 1/(3693 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-40839413 / 125000000) (-326715303 / 1000000000) (Real.log (3693 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (3067427 / 12500000) ≤ -Real.log (320 / 409) ∧
    -Real.log (320 / 409) ≤ (245394161 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 729)) (n := 12)
    (lo := (3067427 / 12500000)) (hi := (245394161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409 / 320) = 1/(320 / 409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (3067427 / 12500000) (245394161 / 1000000000) (Real.log (409 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (409 / 320) = -Real.log (320 / 409) := by
    rw [show ((409 / 320) : ℝ) = ((320 / 409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (65180657 / 200000000) ≤ -Real.log (231 / 320) ∧
    -Real.log (231 / 320) ≤ (162951643 / 500000000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 231) = 1/(231 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-162951643 / 500000000) (-65180657 / 200000000) (Real.log (231 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18008489 / 100000000) ≤ -Real.log (1000000 / 1197319) ∧
    -Real.log (1000000 / 1197319) ≤ (180084891 / 1000000000) := by
  have h := checkLog_sound (w := (197319 / 2197319)) (n := 12)
    (lo := (18008489 / 100000000)) (hi := (180084891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197319 / 1000000) = 1/(1000000 / 1197319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18008489 / 100000000) (180084891 / 1000000000) (Real.log (1197319 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1197319 / 1000000) = -Real.log (1000000 / 1197319) := by
    rw [show ((1197319 / 1000000) : ℝ) = ((1000000 / 1197319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (13737369 / 62500000) ≤ -Real.log (802681 / 1000000) ∧
    -Real.log (802681 / 1000000) ≤ (43959581 / 200000000) := by
  have h := checkLog_sound (w := (197319 / 1802681)) (n := 12)
    (lo := (13737369 / 62500000)) (hi := (43959581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802681) = 1/(802681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-43959581 / 200000000) (-13737369 / 62500000) (Real.log (802681 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (180434777 / 1000000000) ≤ -Real.log (500000 / 598869) ∧
    -Real.log (500000 / 598869) ≤ (90217389 / 500000000) := by
  have h := checkLog_sound (w := (98869 / 1098869)) (n := 12)
    (lo := (180434777 / 1000000000)) (hi := (90217389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598869 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598869 / 500000) = 1/(500000 / 598869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (180434777 / 1000000000) (90217389 / 500000000) (Real.log (598869 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (598869 / 500000) = -Real.log (500000 / 598869) := by
    rw [show ((598869 / 500000) : ℝ) = ((500000 / 598869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (220320041 / 1000000000) ≤ -Real.log (401131 / 500000) ∧
    -Real.log (401131 / 500000) ≤ (110160021 / 500000000) := by
  have h := checkLog_sound (w := (98869 / 901131)) (n := 12)
    (lo := (220320041 / 1000000000)) (hi := (110160021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401131) = 1/(401131 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-110160021 / 500000000) (-220320041 / 1000000000) (Real.log (401131 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131946261 / 1000000000) ≤ -Real.log (1000000 / 1141047) ∧
    -Real.log (1000000 / 1141047) ≤ (65973131 / 500000000) := by
  have h := checkLog_sound (w := (141047 / 2141047)) (n := 12)
    (lo := (131946261 / 1000000000)) (hi := (65973131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1141047 / 1000000) = 1/(1000000 / 1141047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131946261 / 1000000000) (65973131 / 500000000) (Real.log (1141047 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1141047 / 1000000) = -Real.log (1000000 / 1141047) := by
    rw [show ((1141047 / 1000000) : ℝ) = ((1000000 / 1141047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (152041073 / 1000000000) ≤ -Real.log (858953 / 1000000) ∧
    -Real.log (858953 / 1000000) ≤ (76020537 / 500000000) := by
  have h := checkLog_sound (w := (141047 / 1858953)) (n := 12)
    (lo := (152041073 / 1000000000)) (hi := (76020537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 858953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 858953) = 1/(858953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76020537 / 500000000) (-152041073 / 1000000000) (Real.log (858953 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33053819 / 250000000) ≤ -Real.log (500000 / 570677) ∧
    -Real.log (500000 / 570677) ≤ (132215277 / 1000000000) := by
  have h := checkLog_sound (w := (70677 / 1070677)) (n := 12)
    (lo := (33053819 / 250000000)) (hi := (132215277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570677 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570677 / 500000) = 1/(500000 / 570677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33053819 / 250000000) (132215277 / 1000000000) (Real.log (570677 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (570677 / 500000) = -Real.log (500000 / 570677) := by
    rw [show ((570677 / 500000) : ℝ) = ((500000 / 570677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (152398549 / 1000000000) ≤ -Real.log (429323 / 500000) ∧
    -Real.log (429323 / 500000) ≤ (3047971 / 20000000) := by
  have h := checkLog_sound (w := (70677 / 929323)) (n := 12)
    (lo := (152398549 / 1000000000)) (hi := (3047971 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429323) = 1/(429323 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3047971 / 20000000) (-152398549 / 1000000000) (Real.log (429323 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (114259489 / 200000000) ≤ -Real.log (500000000000 / 885281385281) ∧
    -Real.log (500000000000 / 885281385281) ≤ (285648723 / 500000000) := by
  have h := checkLog_sound (w := (385281385281 / 1385281385281)) (n := 12)
    (lo := (114259489 / 200000000)) (hi := (285648723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885281385281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885281385281 / 500000000000) = 1/(500000000000 / 885281385281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (114259489 / 200000000) (285648723 / 500000000) (Real.log (885281385281 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (885281385281 / 500000000000) = -Real.log (500000000000 / 885281385281) := by
    rw [show ((885281385281 / 500000000000) : ℝ) = ((500000000000 / 885281385281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (572567793 / 1000000000) ≤ -Real.log (31250000000 / 55400419713) ∧
    -Real.log (31250000000 / 55400419713) ≤ (286283897 / 500000000) := by
  have h := checkLog_sound (w := (24150419713 / 86650419713)) (n := 12)
    (lo := (572567793 / 1000000000)) (hi := (286283897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55400419713 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55400419713 / 31250000000) = 1/(31250000000 / 55400419713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (572567793 / 1000000000) (286283897 / 500000000) (Real.log (55400419713 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (55400419713 / 31250000000) = -Real.log (31250000000 / 55400419713) := by
    rw [show ((55400419713 / 31250000000) : ℝ) = ((31250000000 / 55400419713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (199941397 / 500000000) ≤ -Real.log (100000000000 / 149164985841) ∧
    -Real.log (100000000000 / 149164985841) ≤ (79976559 / 200000000) := by
  have h := checkLog_sound (w := (49164985841 / 249164985841)) (n := 12)
    (lo := (199941397 / 500000000)) (hi := (79976559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149164985841 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149164985841 / 100000000000) = 1/(100000000000 / 149164985841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (199941397 / 500000000) (79976559 / 200000000) (Real.log (149164985841 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (149164985841 / 100000000000) = -Real.log (100000000000 / 149164985841) := by
    rw [show ((149164985841 / 100000000000) : ℝ) = ((100000000000 / 149164985841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (400754819 / 1000000000) ≤ -Real.log (500000000000 / 746475590269) ∧
    -Real.log (500000000000 / 746475590269) ≤ (20037741 / 50000000) := by
  have h := checkLog_sound (w := (246475590269 / 1246475590269)) (n := 12)
    (lo := (400754819 / 1000000000)) (hi := (20037741 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746475590269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746475590269 / 500000000000) = 1/(500000000000 / 746475590269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (400754819 / 1000000000) (20037741 / 50000000) (Real.log (746475590269 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (746475590269 / 500000000000) = -Real.log (500000000000 / 746475590269) := by
    rw [show ((746475590269 / 500000000000) : ℝ) = ((500000000000 / 746475590269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (56797467 / 200000000) ≤ -Real.log (125000000000 / 166052013323) ∧
    -Real.log (125000000000 / 166052013323) ≤ (35498417 / 125000000) := by
  have h := checkLog_sound (w := (41052013323 / 291052013323)) (n := 12)
    (lo := (56797467 / 200000000)) (hi := (35498417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166052013323 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166052013323 / 125000000000) = 1/(125000000000 / 166052013323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (56797467 / 200000000) (35498417 / 125000000) (Real.log (166052013323 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (166052013323 / 125000000000) = -Real.log (125000000000 / 166052013323) := by
    rw [show ((166052013323 / 125000000000) : ℝ) = ((125000000000 / 166052013323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (11384553 / 40000000) ≤ -Real.log (250000000000 / 332312151923) ∧
    -Real.log (250000000000 / 332312151923) ≤ (142306913 / 500000000) := by
  have h := checkLog_sound (w := (82312151923 / 582312151923)) (n := 12)
    (lo := (11384553 / 40000000)) (hi := (142306913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332312151923 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332312151923 / 250000000000) = 1/(250000000000 / 332312151923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (11384553 / 40000000) (142306913 / 500000000) (Real.log (332312151923 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (332312151923 / 250000000000) = -Real.log (250000000000 / 332312151923) := by
    rw [show ((332312151923 / 250000000000) : ℝ) = ((250000000000 / 332312151923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2522909 / 125000000) ≤ -Real.log (245004761671 / 250000000000) ∧
    -Real.log (245004761671 / 250000000000) ≤ (20183273 / 1000000000) := by
  have h := checkLog_sound (w := (4995238329 / 495004761671)) (n := 12)
    (lo := (2522909 / 125000000)) (hi := (20183273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245004761671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245004761671) = 1/(245004761671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20183273 / 1000000000) (-2522909 / 125000000) (Real.log (245004761671 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20094811 / 1000000000) ≤ -Real.log (980105743791 / 1000000000000) ∧
    -Real.log (980105743791 / 1000000000000) ≤ (5023703 / 250000000) := by
  have h := checkLog_sound (w := (19894256209 / 1980105743791)) (n := 12)
    (lo := (20094811 / 1000000000)) (hi := (5023703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980105743791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980105743791) = 1/(980105743791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5023703 / 250000000) (-20094811 / 1000000000) (Real.log (980105743791 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell048

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell049Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell049
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

theorem reflection_log_1_neg : (24631061 / 100000000) ≤ -Real.log (512 / 655) ∧
    -Real.log (512 / 655) ≤ (246310611 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 1167)) (n := 12)
    (lo := (24631061 / 100000000)) (hi := (246310611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655 / 512) = 1/(512 / 655) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24631061 / 100000000) (246310611 / 1000000000) (Real.log (655 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (655 / 512) = -Real.log (512 / 655) := by
    rw [show ((655 / 512) : ℝ) = ((512 / 655) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16376399 / 50000000) ≤ -Real.log (369 / 512) ∧
    -Real.log (369 / 512) ≤ (327527981 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 881)) (n := 12)
    (lo := (16376399 / 50000000)) (hi := (327527981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 369) = 1/(369 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-327527981 / 1000000000) (-16376399 / 50000000) (Real.log (369 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24585249 / 100000000) ≤ -Real.log (5120 / 6547) ∧
    -Real.log (5120 / 6547) ≤ (245852491 / 1000000000) := by
  have h := checkLog_sound (w := (1427 / 11667)) (n := 12)
    (lo := (24585249 / 100000000)) (hi := (245852491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6547 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6547 / 5120) = 1/(5120 / 6547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24585249 / 100000000) (245852491 / 1000000000) (Real.log (6547 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6547 / 5120) = -Real.log (5120 / 6547) := by
    rw [show ((6547 / 5120) : ℝ) = ((5120 / 6547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (326715303 / 1000000000) ≤ -Real.log (3693 / 5120) ∧
    -Real.log (3693 / 5120) ≤ (40839413 / 125000000) := by
  have h := checkLog_sound (w := (1427 / 8813)) (n := 12)
    (lo := (326715303 / 1000000000)) (hi := (40839413 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3693) = 1/(3693 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-40839413 / 125000000) (-326715303 / 1000000000) (Real.log (3693 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (180433943 / 1000000000) ≤ -Real.log (1000000 / 1197737) ∧
    -Real.log (1000000 / 1197737) ≤ (22554243 / 125000000) := by
  have h := checkLog_sound (w := (197737 / 2197737)) (n := 12)
    (lo := (180433943 / 1000000000)) (hi := (22554243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197737 / 1000000) = 1/(1000000 / 1197737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (180433943 / 1000000000) (22554243 / 125000000) (Real.log (1197737 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1197737 / 1000000) = -Real.log (1000000 / 1197737) := by
    rw [show ((1197737 / 1000000) : ℝ) = ((1000000 / 1197737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (110159397 / 500000000) ≤ -Real.log (802263 / 1000000) ∧
    -Real.log (802263 / 1000000) ≤ (44063759 / 200000000) := by
  have h := checkLog_sound (w := (197737 / 1802263)) (n := 12)
    (lo := (110159397 / 500000000)) (hi := (44063759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802263) = 1/(802263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-44063759 / 200000000) (-110159397 / 500000000) (Real.log (802263 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (90392271 / 500000000) ≤ -Real.log (1000000 / 1198157) ∧
    -Real.log (1000000 / 1198157) ≤ (180784543 / 1000000000) := by
  have h := checkLog_sound (w := (198157 / 2198157)) (n := 12)
    (lo := (90392271 / 500000000)) (hi := (180784543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198157 / 1000000) = 1/(1000000 / 1198157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (90392271 / 500000000) (180784543 / 1000000000) (Real.log (1198157 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1198157 / 1000000) = -Real.log (1000000 / 1198157) := by
    rw [show ((1198157 / 1000000) : ℝ) = ((1000000 / 1198157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4416849 / 20000000) ≤ -Real.log (801843 / 1000000) ∧
    -Real.log (801843 / 1000000) ≤ (220842451 / 1000000000) := by
  have h := checkLog_sound (w := (198157 / 1801843)) (n := 12)
    (lo := (4416849 / 20000000)) (hi := (220842451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801843) = 1/(801843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-220842451 / 1000000000) (-4416849 / 20000000) (Real.log (801843 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (41317 / 312500) ≤ -Real.log (1000000 / 1141353) ∧
    -Real.log (1000000 / 1141353) ≤ (132214401 / 1000000000) := by
  have h := checkLog_sound (w := (141353 / 2141353)) (n := 12)
    (lo := (41317 / 312500)) (hi := (132214401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1141353 / 1000000) = 1/(1000000 / 1141353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (41317 / 312500) (132214401 / 1000000000) (Real.log (1141353 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1141353 / 1000000) = -Real.log (1000000 / 1141353) := by
    rw [show ((1141353 / 1000000) : ℝ) = ((1000000 / 1141353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (19049673 / 125000000) ≤ -Real.log (858647 / 1000000) ∧
    -Real.log (858647 / 1000000) ≤ (30479477 / 200000000) := by
  have h := checkLog_sound (w := (141353 / 1858647)) (n := 12)
    (lo := (19049673 / 125000000)) (hi := (30479477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 858647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 858647) = 1/(858647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-30479477 / 200000000) (-19049673 / 125000000) (Real.log (858647 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (132483343 / 1000000000) ≤ -Real.log (50000 / 57083) ∧
    -Real.log (50000 / 57083) ≤ (8280209 / 62500000) := by
  have h := checkLog_sound (w := (7083 / 107083)) (n := 12)
    (lo := (132483343 / 1000000000)) (hi := (8280209 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57083 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57083 / 50000) = 1/(50000 / 57083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (132483343 / 1000000000) (8280209 / 62500000) (Real.log (57083 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (57083 / 50000) = -Real.log (50000 / 57083) := by
    rw [show ((57083 / 50000) : ℝ) = ((50000 / 57083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (152754987 / 1000000000) ≤ -Real.log (42917 / 50000) ∧
    -Real.log (42917 / 50000) ≤ (38188747 / 250000000) := by
  have h := checkLog_sound (w := (7083 / 92917)) (n := 12)
    (lo := (152754987 / 1000000000)) (hi := (38188747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42917) = 1/(42917 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38188747 / 250000000) (-152754987 / 1000000000) (Real.log (42917 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (572567793 / 1000000000) ≤ -Real.log (500000000000 / 886406715407) ∧
    -Real.log (500000000000 / 886406715407) ≤ (286283897 / 500000000) := by
  have h := checkLog_sound (w := (386406715407 / 1386406715407)) (n := 12)
    (lo := (572567793 / 1000000000)) (hi := (286283897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((886406715407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(886406715407 / 500000000000) = 1/(500000000000 / 886406715407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (572567793 / 1000000000) (286283897 / 500000000) (Real.log (886406715407 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (886406715407 / 500000000000) = -Real.log (500000000000 / 886406715407) := by
    rw [show ((886406715407 / 500000000000) : ℝ) = ((500000000000 / 886406715407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (573838591 / 1000000000) ≤ -Real.log (500000000000 / 887533875339) ∧
    -Real.log (500000000000 / 887533875339) ≤ (2241557 / 3906250) := by
  have h := checkLog_sound (w := (387533875339 / 1387533875339)) (n := 12)
    (lo := (573838591 / 1000000000)) (hi := (2241557 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887533875339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887533875339 / 500000000000) = 1/(500000000000 / 887533875339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (573838591 / 1000000000) (2241557 / 3906250) (Real.log (887533875339 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (887533875339 / 500000000000) = -Real.log (500000000000 / 887533875339) := by
    rw [show ((887533875339 / 500000000000) : ℝ) = ((500000000000 / 887533875339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (400752737 / 1000000000) ≤ -Real.log (500000000000 / 746474036569) ∧
    -Real.log (500000000000 / 746474036569) ≤ (200376369 / 500000000) := by
  have h := checkLog_sound (w := (246474036569 / 1246474036569)) (n := 12)
    (lo := (400752737 / 1000000000)) (hi := (200376369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746474036569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746474036569 / 500000000000) = 1/(500000000000 / 746474036569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (400752737 / 1000000000) (200376369 / 500000000) (Real.log (746474036569 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (746474036569 / 500000000000) = -Real.log (500000000000 / 746474036569) := by
    rw [show ((746474036569 / 500000000000) : ℝ) = ((500000000000 / 746474036569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (401626993 / 1000000000) ≤ -Real.log (125000000000 / 186781732833) ∧
    -Real.log (125000000000 / 186781732833) ≤ (200813497 / 500000000) := by
  have h := checkLog_sound (w := (61781732833 / 311781732833)) (n := 12)
    (lo := (401626993 / 1000000000)) (hi := (200813497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186781732833 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186781732833 / 125000000000) = 1/(125000000000 / 186781732833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (401626993 / 1000000000) (200813497 / 500000000) (Real.log (186781732833 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (186781732833 / 125000000000) = -Real.log (125000000000 / 186781732833) := by
    rw [show ((186781732833 / 125000000000) : ℝ) = ((125000000000 / 186781732833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (56922357 / 200000000) ≤ -Real.log (500000000000 / 664622947497) ∧
    -Real.log (500000000000 / 664622947497) ≤ (142305893 / 500000000) := by
  have h := checkLog_sound (w := (164622947497 / 1164622947497)) (n := 12)
    (lo := (56922357 / 200000000)) (hi := (142305893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664622947497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664622947497 / 500000000000) = 1/(500000000000 / 664622947497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (56922357 / 200000000) (142305893 / 500000000) (Real.log (664622947497 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (664622947497 / 500000000000) = -Real.log (500000000000 / 664622947497) := by
    rw [show ((664622947497 / 500000000000) : ℝ) = ((500000000000 / 664622947497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (285238331 / 1000000000) ≤ -Real.log (500000000000 / 665039494839) ∧
    -Real.log (500000000000 / 665039494839) ≤ (71309583 / 250000000) := by
  have h := checkLog_sound (w := (165039494839 / 1165039494839)) (n := 12)
    (lo := (285238331 / 1000000000)) (hi := (71309583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665039494839 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665039494839 / 500000000000) = 1/(500000000000 / 665039494839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (285238331 / 1000000000) (71309583 / 250000000) (Real.log (665039494839 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (665039494839 / 500000000000) = -Real.log (500000000000 / 665039494839) := by
    rw [show ((665039494839 / 500000000000) : ℝ) = ((500000000000 / 665039494839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20271643 / 1000000000) ≤ -Real.log (2449831111 / 2500000000) ∧
    -Real.log (2449831111 / 2500000000) ≤ (5067911 / 250000000) := by
  have h := checkLog_sound (w := (50168889 / 4949831111)) (n := 12)
    (lo := (20271643 / 1000000000)) (hi := (5067911 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2449831111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2449831111) = 1/(2449831111 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5067911 / 250000000) (-20271643 / 1000000000) (Real.log (2449831111 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20182983 / 1000000000) ≤ -Real.log (980019329391 / 1000000000000) ∧
    -Real.log (980019329391 / 1000000000000) ≤ (2522873 / 125000000) := by
  have h := checkLog_sound (w := (19980670609 / 1980019329391)) (n := 12)
    (lo := (20182983 / 1000000000)) (hi := (2522873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980019329391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980019329391) = 1/(980019329391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2522873 / 125000000) (-20182983 / 1000000000) (Real.log (980019329391 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell049

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell050Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell050
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

theorem reflection_log_1_neg : (246768521 / 1000000000) ≤ -Real.log (5120 / 6553) ∧
    -Real.log (5120 / 6553) ≤ (123384261 / 500000000) := by
  have h := checkLog_sound (w := (1433 / 11673)) (n := 12)
    (lo := (246768521 / 1000000000)) (hi := (123384261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6553 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6553 / 5120) = 1/(5120 / 6553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (246768521 / 1000000000) (123384261 / 500000000) (Real.log (6553 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6553 / 5120) = -Real.log (5120 / 6553) := by
    rw [show ((6553 / 5120) : ℝ) = ((5120 / 6553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (328341319 / 1000000000) ≤ -Real.log (3687 / 5120) ∧
    -Real.log (3687 / 5120) ≤ (8208533 / 25000000) := by
  have h := checkLog_sound (w := (1433 / 8807)) (n := 12)
    (lo := (328341319 / 1000000000)) (hi := (8208533 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3687) = 1/(3687 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-8208533 / 25000000) (-328341319 / 1000000000) (Real.log (3687 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24631061 / 100000000) ≤ -Real.log (512 / 655) ∧
    -Real.log (512 / 655) ≤ (246310611 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 1167)) (n := 12)
    (lo := (24631061 / 100000000)) (hi := (246310611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655 / 512) = 1/(512 / 655) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24631061 / 100000000) (246310611 / 1000000000) (Real.log (655 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (655 / 512) = -Real.log (512 / 655) := by
    rw [show ((655 / 512) : ℝ) = ((512 / 655) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16376399 / 50000000) ≤ -Real.log (369 / 512) ∧
    -Real.log (369 / 512) ≤ (327527981 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 881)) (n := 12)
    (lo := (16376399 / 50000000)) (hi := (327527981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 369) = 1/(369 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-327527981 / 1000000000) (-16376399 / 50000000) (Real.log (369 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45195927 / 250000000) ≤ -Real.log (250000 / 299539) ∧
    -Real.log (250000 / 299539) ≤ (180783709 / 1000000000) := by
  have h := checkLog_sound (w := (49539 / 549539)) (n := 12)
    (lo := (45195927 / 250000000)) (hi := (180783709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299539 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299539 / 250000) = 1/(250000 / 299539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45195927 / 250000000) (180783709 / 1000000000) (Real.log (299539 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (299539 / 250000) = -Real.log (250000 / 299539) := by
    rw [show ((299539 / 250000) : ℝ) = ((250000 / 299539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (220841203 / 1000000000) ≤ -Real.log (200461 / 250000) ∧
    -Real.log (200461 / 250000) ≤ (55210301 / 250000000) := by
  have h := checkLog_sound (w := (49539 / 450461)) (n := 12)
    (lo := (220841203 / 1000000000)) (hi := (55210301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200461) = 1/(200461 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-55210301 / 250000000) (-220841203 / 1000000000) (Real.log (200461 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (181133351 / 1000000000) ≤ -Real.log (40000 / 47943) ∧
    -Real.log (40000 / 47943) ≤ (22641669 / 125000000) := by
  have h := checkLog_sound (w := (7943 / 87943)) (n := 12)
    (lo := (181133351 / 1000000000)) (hi := (22641669 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47943 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47943 / 40000) = 1/(40000 / 47943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (181133351 / 1000000000) (22641669 / 125000000) (Real.log (47943 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (47943 / 40000) = -Real.log (40000 / 47943) := by
    rw [show ((47943 / 40000) : ℝ) = ((40000 / 47943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (44272777 / 200000000) ≤ -Real.log (32057 / 40000) ∧
    -Real.log (32057 / 40000) ≤ (110681943 / 500000000) := by
  have h := checkLog_sound (w := (7943 / 72057)) (n := 12)
    (lo := (44272777 / 200000000)) (hi := (110681943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32057) = 1/(32057 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-110681943 / 500000000) (-44272777 / 200000000) (Real.log (32057 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (132482467 / 1000000000) ≤ -Real.log (1000000 / 1141659) ∧
    -Real.log (1000000 / 1141659) ≤ (33120617 / 250000000) := by
  have h := checkLog_sound (w := (141659 / 2141659)) (n := 12)
    (lo := (132482467 / 1000000000)) (hi := (33120617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1141659 / 1000000) = 1/(1000000 / 1141659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (132482467 / 1000000000) (33120617 / 250000000) (Real.log (1141659 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1141659 / 1000000) = -Real.log (1000000 / 1141659) := by
    rw [show ((1141659 / 1000000) : ℝ) = ((1000000 / 1141659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (76376911 / 500000000) ≤ -Real.log (858341 / 1000000) ∧
    -Real.log (858341 / 1000000) ≤ (152753823 / 1000000000) := by
  have h := checkLog_sound (w := (141659 / 1858341)) (n := 12)
    (lo := (76376911 / 500000000)) (hi := (152753823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 858341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 858341) = 1/(858341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-152753823 / 1000000000) (-76376911 / 500000000) (Real.log (858341 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66375669 / 500000000) ≤ -Real.log (500000 / 570983) ∧
    -Real.log (500000 / 570983) ≤ (132751339 / 1000000000) := by
  have h := checkLog_sound (w := (70983 / 1070983)) (n := 12)
    (lo := (66375669 / 500000000)) (hi := (132751339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570983 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570983 / 500000) = 1/(500000 / 570983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66375669 / 500000000) (132751339 / 1000000000) (Real.log (570983 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (570983 / 500000) = -Real.log (500000 / 570983) := by
    rw [show ((570983 / 500000) : ℝ) = ((500000 / 570983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (153111553 / 1000000000) ≤ -Real.log (429017 / 500000) ∧
    -Real.log (429017 / 500000) ≤ (76555777 / 500000000) := by
  have h := checkLog_sound (w := (70983 / 929017)) (n := 12)
    (lo := (153111553 / 1000000000)) (hi := (76555777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429017) = 1/(429017 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-76555777 / 500000000) (-153111553 / 1000000000) (Real.log (429017 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (573838591 / 1000000000) ≤ -Real.log (250000000000 / 443766937669) ∧
    -Real.log (250000000000 / 443766937669) ≤ (2241557 / 3906250) := by
  have h := checkLog_sound (w := (193766937669 / 693766937669)) (n := 12)
    (lo := (573838591 / 1000000000)) (hi := (2241557 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443766937669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443766937669 / 250000000000) = 1/(250000000000 / 443766937669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (573838591 / 1000000000) (2241557 / 3906250) (Real.log (443766937669 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (443766937669 / 250000000000) = -Real.log (250000000000 / 443766937669) := by
    rw [show ((443766937669 / 250000000000) : ℝ) = ((250000000000 / 443766937669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (7188873 / 12500000) ≤ -Real.log (250000000000 / 444331434771) ∧
    -Real.log (250000000000 / 444331434771) ≤ (575109841 / 1000000000) := by
  have h := checkLog_sound (w := (194331434771 / 694331434771)) (n := 12)
    (lo := (7188873 / 12500000)) (hi := (575109841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444331434771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444331434771 / 250000000000) = 1/(250000000000 / 444331434771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (7188873 / 12500000) (575109841 / 1000000000) (Real.log (444331434771 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (444331434771 / 250000000000) = -Real.log (250000000000 / 444331434771) := by
    rw [show ((444331434771 / 250000000000) : ℝ) = ((250000000000 / 444331434771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (401624911 / 1000000000) ≤ -Real.log (62500000000 / 93390672001) ∧
    -Real.log (62500000000 / 93390672001) ≤ (25101557 / 62500000) := by
  have h := checkLog_sound (w := (30890672001 / 155890672001)) (n := 12)
    (lo := (401624911 / 1000000000)) (hi := (25101557 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93390672001 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93390672001 / 62500000000) = 1/(62500000000 / 93390672001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (401624911 / 1000000000) (25101557 / 62500000) (Real.log (93390672001 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (93390672001 / 62500000000) = -Real.log (62500000000 / 93390672001) := by
    rw [show ((93390672001 / 62500000000) : ℝ) = ((62500000000 / 93390672001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (402497237 / 1000000000) ≤ -Real.log (500000000000 / 747777396513) ∧
    -Real.log (500000000000 / 747777396513) ≤ (201248619 / 500000000) := by
  have h := checkLog_sound (w := (247777396513 / 1247777396513)) (n := 12)
    (lo := (402497237 / 1000000000)) (hi := (201248619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747777396513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747777396513 / 500000000000) = 1/(500000000000 / 747777396513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (402497237 / 1000000000) (201248619 / 500000000) (Real.log (747777396513 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (747777396513 / 500000000000) = -Real.log (500000000000 / 747777396513) := by
    rw [show ((747777396513 / 500000000000) : ℝ) = ((500000000000 / 747777396513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (28523629 / 100000000) ≤ -Real.log (500000000000 / 665038137523) ∧
    -Real.log (500000000000 / 665038137523) ≤ (285236291 / 1000000000) := by
  have h := checkLog_sound (w := (165038137523 / 1165038137523)) (n := 12)
    (lo := (28523629 / 100000000)) (hi := (285236291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665038137523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665038137523 / 500000000000) = 1/(500000000000 / 665038137523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (28523629 / 100000000) (285236291 / 1000000000) (Real.log (665038137523 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (665038137523 / 500000000000) = -Real.log (500000000000 / 665038137523) := by
    rw [show ((665038137523 / 500000000000) : ℝ) = ((500000000000 / 665038137523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (285862891 / 1000000000) ≤ -Real.log (500000000000 / 665454981971) ∧
    -Real.log (500000000000 / 665454981971) ≤ (71465723 / 250000000) := by
  have h := checkLog_sound (w := (165454981971 / 1165454981971)) (n := 12)
    (lo := (285862891 / 1000000000)) (hi := (71465723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665454981971 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665454981971 / 500000000000) = 1/(500000000000 / 665454981971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (285862891 / 1000000000) (71465723 / 250000000) (Real.log (665454981971 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (665454981971 / 500000000000) = -Real.log (500000000000 / 665454981971) := by
    rw [show ((665454981971 / 500000000000) : ℝ) = ((500000000000 / 665454981971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10180107 / 500000000) ≤ -Real.log (244961413711 / 250000000000) ∧
    -Real.log (244961413711 / 250000000000) ≤ (4072043 / 200000000) := by
  have h := checkLog_sound (w := (5038586289 / 494961413711)) (n := 12)
    (lo := (10180107 / 500000000)) (hi := (4072043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244961413711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244961413711) = 1/(244961413711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4072043 / 200000000) (-10180107 / 500000000) (Real.log (244961413711 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10135677 / 500000000) ≤ -Real.log (979932727719 / 1000000000000) ∧
    -Real.log (979932727719 / 1000000000000) ≤ (4054271 / 200000000) := by
  have h := checkLog_sound (w := (20067272281 / 1979932727719)) (n := 12)
    (lo := (10135677 / 500000000)) (hi := (4054271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979932727719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979932727719) = 1/(979932727719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4054271 / 200000000) (-10135677 / 500000000) (Real.log (979932727719 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell050

end


