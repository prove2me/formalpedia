-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell023Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell023Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:21:03.275876+00:00
-- url     : https://prove2.me/theorems/5cb74767-9eb1-4119-b844-ed5db16294f8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell023Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell024…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell023Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell024Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell025Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell026Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell027Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell028Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell029Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell023Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell024Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell025Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell026Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell027Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell028Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell029Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell023Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell024Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell025Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell026Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell027Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell028Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell029Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell023Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell024Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell025Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell026Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell027Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell028Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell029Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell023Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell023
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

theorem reflection_log_1_neg : (11716537 / 50000000) ≤ -Real.log (640 / 809) ∧
    -Real.log (640 / 809) ≤ (234330741 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 1449)) (n := 12)
    (lo := (11716537 / 50000000)) (hi := (234330741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809 / 640) = 1/(640 / 809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11716537 / 50000000) (234330741 / 1000000000) (Real.log (809 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (809 / 640) = -Real.log (640 / 809) := by
    rw [show ((809 / 640) : ℝ) = ((640 / 809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (153305041 / 500000000) ≤ -Real.log (471 / 640) ∧
    -Real.log (471 / 640) ≤ (306610083 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 1111)) (n := 12)
    (lo := (153305041 / 500000000)) (hi := (306610083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 471) = 1/(471 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-306610083 / 1000000000) (-153305041 / 500000000) (Real.log (471 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (116933549 / 500000000) ≤ -Real.log (5120 / 6469) ∧
    -Real.log (5120 / 6469) ≤ (233867099 / 1000000000) := by
  have h := checkLog_sound (w := (1349 / 11589)) (n := 12)
    (lo := (116933549 / 500000000)) (hi := (233867099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6469 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6469 / 5120) = 1/(5120 / 6469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (116933549 / 500000000) (233867099 / 1000000000) (Real.log (6469 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6469 / 5120) = -Real.log (5120 / 6469) := by
    rw [show ((6469 / 5120) : ℝ) = ((5120 / 6469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (15290711 / 50000000) ≤ -Real.log (3771 / 5120) ∧
    -Real.log (3771 / 5120) ≤ (305814221 / 1000000000) := by
  have h := checkLog_sound (w := (1349 / 8891)) (n := 12)
    (lo := (15290711 / 50000000)) (hi := (305814221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3771) = 1/(3771 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-305814221 / 1000000000) (-15290711 / 50000000) (Real.log (3771 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42827791 / 250000000) ≤ -Real.log (50000 / 59343) ∧
    -Real.log (50000 / 59343) ≤ (34262233 / 200000000) := by
  have h := checkLog_sound (w := (9343 / 109343)) (n := 12)
    (lo := (42827791 / 250000000)) (hi := (34262233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59343 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59343 / 50000) = 1/(50000 / 59343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42827791 / 250000000) (34262233 / 200000000) (Real.log (59343 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (59343 / 50000) = -Real.log (50000 / 59343) := by
    rw [show ((59343 / 50000) : ℝ) = ((50000 / 59343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (103425991 / 500000000) ≤ -Real.log (40657 / 50000) ∧
    -Real.log (40657 / 50000) ≤ (206851983 / 1000000000) := by
  have h := checkLog_sound (w := (9343 / 90657)) (n := 12)
    (lo := (103425991 / 500000000)) (hi := (206851983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40657) = 1/(40657 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-206851983 / 1000000000) (-103425991 / 500000000) (Real.log (40657 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10729061 / 62500000) ≤ -Real.log (12500 / 14841) ∧
    -Real.log (12500 / 14841) ≤ (171664977 / 1000000000) := by
  have h := checkLog_sound (w := (2341 / 27341)) (n := 12)
    (lo := (10729061 / 62500000)) (hi := (171664977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14841 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14841 / 12500) = 1/(12500 / 14841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10729061 / 62500000) (171664977 / 1000000000) (Real.log (14841 / 12500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14841 / 12500) = -Real.log (12500 / 14841) := by
    rw [show ((14841 / 12500) : ℝ) = ((12500 / 14841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (25921079 / 125000000) ≤ -Real.log (10159 / 12500) ∧
    -Real.log (10159 / 12500) ≤ (207368633 / 1000000000) := by
  have h := checkLog_sound (w := (2341 / 22659)) (n := 12)
    (lo := (25921079 / 125000000)) (hi := (207368633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 10159) = 1/(10159 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-207368633 / 1000000000) (-25921079 / 125000000) (Real.log (10159 / 12500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (31310123 / 250000000) ≤ -Real.log (1000000 / 1133421) ∧
    -Real.log (1000000 / 1133421) ≤ (125240493 / 1000000000) := by
  have h := checkLog_sound (w := (133421 / 2133421)) (n := 12)
    (lo := (31310123 / 250000000)) (hi := (125240493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133421 / 1000000) = 1/(1000000 / 1133421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (31310123 / 250000000) (125240493 / 1000000000) (Real.log (1133421 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1133421 / 1000000) = -Real.log (1000000 / 1133421) := by
    rw [show ((1133421 / 1000000) : ℝ) = ((1000000 / 1133421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (71601001 / 500000000) ≤ -Real.log (866579 / 1000000) ∧
    -Real.log (866579 / 1000000) ≤ (143202003 / 1000000000) := by
  have h := checkLog_sound (w := (133421 / 1866579)) (n := 12)
    (lo := (71601001 / 500000000)) (hi := (143202003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 866579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 866579) = 1/(866579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-143202003 / 1000000000) (-71601001 / 500000000) (Real.log (866579 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (25102087 / 200000000) ≤ -Real.log (1000000 / 1133727) ∧
    -Real.log (1000000 / 1133727) ≤ (31377609 / 250000000) := by
  have h := checkLog_sound (w := (133727 / 2133727)) (n := 12)
    (lo := (25102087 / 200000000)) (hi := (31377609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133727 / 1000000) = 1/(1000000 / 1133727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (25102087 / 200000000) (31377609 / 250000000) (Real.log (1133727 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1133727 / 1000000) = -Real.log (1000000 / 1133727) := by
    rw [show ((1133727 / 1000000) : ℝ) = ((1000000 / 1133727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (143555177 / 1000000000) ≤ -Real.log (866273 / 1000000) ∧
    -Real.log (866273 / 1000000) ≤ (71777589 / 500000000) := by
  have h := checkLog_sound (w := (133727 / 1866273)) (n := 12)
    (lo := (143555177 / 1000000000)) (hi := (71777589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 866273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 866273) = 1/(866273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-71777589 / 500000000) (-143555177 / 1000000000) (Real.log (866273 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (269840659 / 500000000) ≤ -Real.log (12500000000 / 21443251127) ∧
    -Real.log (12500000000 / 21443251127) ≤ (539681319 / 1000000000) := by
  have h := checkLog_sound (w := (8943251127 / 33943251127)) (n := 12)
    (lo := (269840659 / 500000000)) (hi := (539681319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21443251127 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21443251127 / 12500000000) = 1/(12500000000 / 21443251127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (269840659 / 500000000) (539681319 / 1000000000) (Real.log (21443251127 / 12500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (21443251127 / 12500000000) = -Real.log (12500000000 / 21443251127) := by
    rw [show ((21443251127 / 12500000000) : ℝ) = ((12500000000 / 21443251127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (540940823 / 1000000000) ≤ -Real.log (25000000000 / 42940552017) ∧
    -Real.log (25000000000 / 42940552017) ≤ (67617603 / 125000000) := by
  have h := checkLog_sound (w := (17940552017 / 67940552017)) (n := 12)
    (lo := (540940823 / 1000000000)) (hi := (67617603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42940552017 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42940552017 / 25000000000) = 1/(25000000000 / 42940552017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (540940823 / 1000000000) (67617603 / 125000000) (Real.log (42940552017 / 25000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (42940552017 / 25000000000) = -Real.log (25000000000 / 42940552017) := by
    rw [show ((42940552017 / 25000000000) : ℝ) = ((25000000000 / 42940552017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (189081573 / 500000000) ≤ -Real.log (250000000000 / 364900263177) ∧
    -Real.log (250000000000 / 364900263177) ≤ (378163147 / 1000000000) := by
  have h := checkLog_sound (w := (114900263177 / 614900263177)) (n := 12)
    (lo := (189081573 / 500000000)) (hi := (378163147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364900263177 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364900263177 / 250000000000) = 1/(250000000000 / 364900263177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (189081573 / 500000000) (378163147 / 1000000000) (Real.log (364900263177 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (364900263177 / 250000000000) = -Real.log (250000000000 / 364900263177) := by
    rw [show ((364900263177 / 250000000000) : ℝ) = ((250000000000 / 364900263177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (47379201 / 125000000) ≤ -Real.log (250000000000 / 365218033271) ∧
    -Real.log (250000000000 / 365218033271) ≤ (379033609 / 1000000000) := by
  have h := checkLog_sound (w := (115218033271 / 615218033271)) (n := 12)
    (lo := (47379201 / 125000000)) (hi := (379033609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365218033271 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365218033271 / 250000000000) = 1/(250000000000 / 365218033271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (47379201 / 125000000) (379033609 / 1000000000) (Real.log (365218033271 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (365218033271 / 250000000000) = -Real.log (250000000000 / 365218033271) := by
    rw [show ((365218033271 / 250000000000) : ℝ) = ((250000000000 / 365218033271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (53688499 / 200000000) ≤ -Real.log (500000000000 / 653962881629) ∧
    -Real.log (500000000000 / 653962881629) ≤ (2097207 / 7812500) := by
  have h := checkLog_sound (w := (153962881629 / 1153962881629)) (n := 12)
    (lo := (53688499 / 200000000)) (hi := (2097207 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653962881629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653962881629 / 500000000000) = 1/(500000000000 / 653962881629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (53688499 / 200000000) (2097207 / 7812500) (Real.log (653962881629 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (653962881629 / 500000000000) = -Real.log (500000000000 / 653962881629) := by
    rw [show ((653962881629 / 500000000000) : ℝ) = ((500000000000 / 653962881629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (269065613 / 1000000000) ≤ -Real.log (500000000000 / 654370504449) ∧
    -Real.log (500000000000 / 654370504449) ≤ (134532807 / 500000000) := by
  have h := checkLog_sound (w := (154370504449 / 1154370504449)) (n := 12)
    (lo := (269065613 / 1000000000)) (hi := (134532807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654370504449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654370504449 / 500000000000) = 1/(500000000000 / 654370504449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (269065613 / 1000000000) (134532807 / 500000000) (Real.log (654370504449 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (654370504449 / 500000000000) = -Real.log (500000000000 / 654370504449) := by
    rw [show ((654370504449 / 500000000000) : ℝ) = ((500000000000 / 654370504449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9022371 / 500000000) ≤ -Real.log (982117089471 / 1000000000000) ∧
    -Real.log (982117089471 / 1000000000000) ≤ (18044743 / 1000000000) := by
  have h := checkLog_sound (w := (17882910529 / 1982117089471)) (n := 12)
    (lo := (9022371 / 500000000)) (hi := (18044743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982117089471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982117089471) = 1/(982117089471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18044743 / 1000000000) (-9022371 / 500000000) (Real.log (982117089471 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17961509 / 1000000000) ≤ -Real.log (982198836759 / 1000000000000) ∧
    -Real.log (982198836759 / 1000000000000) ≤ (1796151 / 100000000) := by
  have h := checkLog_sound (w := (17801163241 / 1982198836759)) (n := 12)
    (lo := (17961509 / 1000000000)) (hi := (1796151 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982198836759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982198836759) = 1/(982198836759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1796151 / 100000000) (-17961509 / 1000000000) (Real.log (982198836759 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell023

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell024Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell024
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

theorem reflection_log_1_neg : (29349271 / 125000000) ≤ -Real.log (1024 / 1295) ∧
    -Real.log (1024 / 1295) ≤ (234794169 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2319)) (n := 12)
    (lo := (29349271 / 125000000)) (hi := (234794169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295 / 1024) = 1/(1024 / 1295) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (29349271 / 125000000) (234794169 / 1000000000) (Real.log (1295 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1295 / 1024) = -Real.log (1024 / 1295) := by
    rw [show ((1295 / 1024) : ℝ) = ((1024 / 1295) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (307406577 / 1000000000) ≤ -Real.log (753 / 1024) ∧
    -Real.log (753 / 1024) ≤ (153703289 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1777)) (n := 12)
    (lo := (307406577 / 1000000000)) (hi := (153703289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 753) = 1/(753 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-153703289 / 500000000) (-307406577 / 1000000000) (Real.log (753 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11716537 / 50000000) ≤ -Real.log (640 / 809) ∧
    -Real.log (640 / 809) ≤ (234330741 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 1449)) (n := 12)
    (lo := (11716537 / 50000000)) (hi := (234330741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809 / 640) = 1/(640 / 809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11716537 / 50000000) (234330741 / 1000000000) (Real.log (809 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (809 / 640) = -Real.log (640 / 809) := by
    rw [show ((809 / 640) : ℝ) = ((640 / 809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (153305041 / 500000000) ≤ -Real.log (471 / 640) ∧
    -Real.log (471 / 640) ≤ (306610083 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 1111)) (n := 12)
    (lo := (153305041 / 500000000)) (hi := (306610083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 471) = 1/(471 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-306610083 / 1000000000) (-153305041 / 500000000) (Real.log (471 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42915823 / 250000000) ≤ -Real.log (500000 / 593639) ∧
    -Real.log (500000 / 593639) ≤ (171663293 / 1000000000) := by
  have h := checkLog_sound (w := (93639 / 1093639)) (n := 12)
    (lo := (42915823 / 250000000)) (hi := (171663293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593639 / 500000) = 1/(500000 / 593639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42915823 / 250000000) (171663293 / 1000000000) (Real.log (593639 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (593639 / 500000) = -Real.log (500000 / 593639) := by
    rw [show ((593639 / 500000) : ℝ) = ((500000 / 593639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (207366171 / 1000000000) ≤ -Real.log (406361 / 500000) ∧
    -Real.log (406361 / 500000) ≤ (51841543 / 250000000) := by
  have h := checkLog_sound (w := (93639 / 906361)) (n := 12)
    (lo := (207366171 / 1000000000)) (hi := (51841543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406361) = 1/(406361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-51841543 / 250000000) (-207366171 / 1000000000) (Real.log (406361 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (172016979 / 1000000000) ≤ -Real.log (500000 / 593849) ∧
    -Real.log (500000 / 593849) ≤ (8600849 / 50000000) := by
  have h := checkLog_sound (w := (93849 / 1093849)) (n := 12)
    (lo := (172016979 / 1000000000)) (hi := (8600849 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593849 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593849 / 500000) = 1/(500000 / 593849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (172016979 / 1000000000) (8600849 / 50000000) (Real.log (593849 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (593849 / 500000) = -Real.log (500000 / 593849) := by
    rw [show ((593849 / 500000) : ℝ) = ((500000 / 593849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (103941543 / 500000000) ≤ -Real.log (406151 / 500000) ∧
    -Real.log (406151 / 500000) ≤ (207883087 / 1000000000) := by
  have h := checkLog_sound (w := (93849 / 906151)) (n := 12)
    (lo := (103941543 / 500000000)) (hi := (207883087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406151) = 1/(406151 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-207883087 / 1000000000) (-103941543 / 500000000) (Real.log (406151 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125509553 / 1000000000) ≤ -Real.log (500000 / 566863) ∧
    -Real.log (500000 / 566863) ≤ (62754777 / 500000000) := by
  have h := checkLog_sound (w := (66863 / 1066863)) (n := 12)
    (lo := (125509553 / 1000000000)) (hi := (62754777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566863 / 500000) = 1/(500000 / 566863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125509553 / 1000000000) (62754777 / 500000000) (Real.log (566863 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (566863 / 500000) = -Real.log (500000 / 566863) := by
    rw [show ((566863 / 500000) : ℝ) = ((500000 / 566863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (143554023 / 1000000000) ≤ -Real.log (433137 / 500000) ∧
    -Real.log (433137 / 500000) ≤ (17944253 / 125000000) := by
  have h := checkLog_sound (w := (66863 / 933137)) (n := 12)
    (lo := (143554023 / 1000000000)) (hi := (17944253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433137) = 1/(433137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17944253 / 125000000) (-143554023 / 1000000000) (Real.log (433137 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (125778541 / 1000000000) ≤ -Real.log (1000000 / 1134031) ∧
    -Real.log (1000000 / 1134031) ≤ (62889271 / 500000000) := by
  have h := checkLog_sound (w := (134031 / 2134031)) (n := 12)
    (lo := (125778541 / 1000000000)) (hi := (62889271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1134031 / 1000000) = 1/(1000000 / 1134031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (125778541 / 1000000000) (62889271 / 500000000) (Real.log (1134031 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1134031 / 1000000) = -Real.log (1000000 / 1134031) := by
    rw [show ((1134031 / 1000000) : ℝ) = ((1000000 / 1134031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (143906167 / 1000000000) ≤ -Real.log (865969 / 1000000) ∧
    -Real.log (865969 / 1000000) ≤ (17988271 / 125000000) := by
  have h := checkLog_sound (w := (134031 / 1865969)) (n := 12)
    (lo := (143906167 / 1000000000)) (hi := (17988271 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 865969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 865969) = 1/(865969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-17988271 / 125000000) (-143906167 / 1000000000) (Real.log (865969 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (540940823 / 1000000000) ≤ -Real.log (500000000000 / 858811040339) ∧
    -Real.log (500000000000 / 858811040339) ≤ (67617603 / 125000000) := by
  have h := checkLog_sound (w := (358811040339 / 1358811040339)) (n := 12)
    (lo := (540940823 / 1000000000)) (hi := (67617603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858811040339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858811040339 / 500000000000) = 1/(500000000000 / 858811040339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (540940823 / 1000000000) (67617603 / 125000000) (Real.log (858811040339 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (858811040339 / 500000000000) = -Real.log (500000000000 / 858811040339) := by
    rw [show ((858811040339 / 500000000000) : ℝ) = ((500000000000 / 858811040339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (271100373 / 500000000) ≤ -Real.log (500000000000 / 859893758301) ∧
    -Real.log (500000000000 / 859893758301) ≤ (542200747 / 1000000000) := by
  have h := checkLog_sound (w := (359893758301 / 1359893758301)) (n := 12)
    (lo := (271100373 / 500000000)) (hi := (542200747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859893758301 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859893758301 / 500000000000) = 1/(500000000000 / 859893758301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (271100373 / 500000000) (542200747 / 1000000000) (Real.log (859893758301 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (859893758301 / 500000000000) = -Real.log (500000000000 / 859893758301) := by
    rw [show ((859893758301 / 500000000000) : ℝ) = ((500000000000 / 859893758301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (379029463 / 1000000000) ≤ -Real.log (500000000000 / 730433038603) ∧
    -Real.log (500000000000 / 730433038603) ≤ (47378683 / 125000000) := by
  have h := checkLog_sound (w := (230433038603 / 1230433038603)) (n := 12)
    (lo := (379029463 / 1000000000)) (hi := (47378683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730433038603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730433038603 / 500000000000) = 1/(500000000000 / 730433038603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (379029463 / 1000000000) (47378683 / 125000000) (Real.log (730433038603 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (730433038603 / 500000000000) = -Real.log (500000000000 / 730433038603) := by
    rw [show ((730433038603 / 500000000000) : ℝ) = ((500000000000 / 730433038603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (189950033 / 500000000) ≤ -Real.log (62500000000 / 91383654109) ∧
    -Real.log (62500000000 / 91383654109) ≤ (379900067 / 1000000000) := by
  have h := checkLog_sound (w := (28883654109 / 153883654109)) (n := 12)
    (lo := (189950033 / 500000000)) (hi := (379900067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91383654109 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91383654109 / 62500000000) = 1/(62500000000 / 91383654109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (189950033 / 500000000) (379900067 / 1000000000) (Real.log (91383654109 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (91383654109 / 62500000000) = -Real.log (62500000000 / 91383654109) := by
    rw [show ((91383654109 / 62500000000) : ℝ) = ((62500000000 / 91383654109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (33632947 / 125000000) ≤ -Real.log (250000000000 / 327184585939) ∧
    -Real.log (250000000000 / 327184585939) ≤ (269063577 / 1000000000) := by
  have h := checkLog_sound (w := (77184585939 / 577184585939)) (n := 12)
    (lo := (33632947 / 125000000)) (hi := (269063577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327184585939 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327184585939 / 250000000000) = 1/(250000000000 / 327184585939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (33632947 / 125000000) (269063577 / 1000000000) (Real.log (327184585939 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (327184585939 / 250000000000) = -Real.log (250000000000 / 327184585939) := by
    rw [show ((327184585939 / 250000000000) : ℝ) = ((250000000000 / 327184585939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (269684709 / 1000000000) ≤ -Real.log (125000000000 / 163693937081) ∧
    -Real.log (125000000000 / 163693937081) ≤ (26968471 / 100000000) := by
  have h := checkLog_sound (w := (38693937081 / 288693937081)) (n := 12)
    (lo := (269684709 / 1000000000)) (hi := (26968471 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163693937081 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163693937081 / 125000000000) = 1/(125000000000 / 163693937081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (269684709 / 1000000000) (26968471 / 100000000) (Real.log (163693937081 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (163693937081 / 125000000000) = -Real.log (125000000000 / 163693937081) := by
    rw [show ((163693937081 / 125000000000) : ℝ) = ((125000000000 / 163693937081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9063813 / 500000000) ≤ -Real.log (982035691039 / 1000000000000) ∧
    -Real.log (982035691039 / 1000000000000) ≤ (18127627 / 1000000000) := by
  have h := checkLog_sound (w := (17964308961 / 1982035691039)) (n := 12)
    (lo := (9063813 / 500000000)) (hi := (18127627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982035691039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982035691039) = 1/(982035691039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18127627 / 1000000000) (-9063813 / 500000000) (Real.log (982035691039 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18044469 / 1000000000) ≤ -Real.log (245529339231 / 250000000000) ∧
    -Real.log (245529339231 / 250000000000) ≤ (1804447 / 100000000) := by
  have h := checkLog_sound (w := (4470660769 / 495529339231)) (n := 12)
    (lo := (18044469 / 1000000000)) (hi := (1804447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245529339231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245529339231) = 1/(245529339231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1804447 / 100000000) (-18044469 / 1000000000) (Real.log (245529339231 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell024

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell025Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell025
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

theorem reflection_log_1_neg : (235257381 / 1000000000) ≤ -Real.log (2560 / 3239) ∧
    -Real.log (2560 / 3239) ≤ (117628691 / 500000000) := by
  have h := checkLog_sound (w := (679 / 5799)) (n := 12)
    (lo := (235257381 / 1000000000)) (hi := (117628691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3239 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3239 / 2560) = 1/(2560 / 3239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (235257381 / 1000000000) (117628691 / 500000000) (Real.log (3239 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3239 / 2560) = -Real.log (2560 / 3239) := by
    rw [show ((3239 / 2560) : ℝ) = ((2560 / 3239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (77050927 / 250000000) ≤ -Real.log (1881 / 2560) ∧
    -Real.log (1881 / 2560) ≤ (308203709 / 1000000000) := by
  have h := checkLog_sound (w := (679 / 4441)) (n := 12)
    (lo := (77050927 / 250000000)) (hi := (308203709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1881) = 1/(1881 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-308203709 / 1000000000) (-77050927 / 250000000) (Real.log (1881 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (29349271 / 125000000) ≤ -Real.log (1024 / 1295) ∧
    -Real.log (1024 / 1295) ≤ (234794169 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2319)) (n := 12)
    (lo := (29349271 / 125000000)) (hi := (234794169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295 / 1024) = 1/(1024 / 1295) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (29349271 / 125000000) (234794169 / 1000000000) (Real.log (1295 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1295 / 1024) = -Real.log (1024 / 1295) := by
    rw [show ((1295 / 1024) : ℝ) = ((1024 / 1295) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (307406577 / 1000000000) ≤ -Real.log (753 / 1024) ∧
    -Real.log (753 / 1024) ≤ (153703289 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1777)) (n := 12)
    (lo := (307406577 / 1000000000)) (hi := (153703289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 753) = 1/(753 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-153703289 / 500000000) (-307406577 / 1000000000) (Real.log (753 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172016137 / 1000000000) ≤ -Real.log (1000000 / 1187697) ∧
    -Real.log (1000000 / 1187697) ≤ (86008069 / 500000000) := by
  have h := checkLog_sound (w := (187697 / 2187697)) (n := 12)
    (lo := (172016137 / 1000000000)) (hi := (86008069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187697 / 1000000) = 1/(1000000 / 1187697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172016137 / 1000000000) (86008069 / 500000000) (Real.log (1187697 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1187697 / 1000000) = -Real.log (1000000 / 1187697) := by
    rw [show ((1187697 / 1000000) : ℝ) = ((1000000 / 1187697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (41576371 / 200000000) ≤ -Real.log (812303 / 1000000) ∧
    -Real.log (812303 / 1000000) ≤ (1624077 / 7812500) := by
  have h := checkLog_sound (w := (187697 / 1812303)) (n := 12)
    (lo := (41576371 / 200000000)) (hi := (1624077 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812303) = 1/(812303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1624077 / 7812500) (-41576371 / 200000000) (Real.log (812303 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (172368859 / 1000000000) ≤ -Real.log (250000 / 297029) ∧
    -Real.log (250000 / 297029) ≤ (8618443 / 50000000) := by
  have h := checkLog_sound (w := (47029 / 547029)) (n := 12)
    (lo := (172368859 / 1000000000)) (hi := (8618443 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297029 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297029 / 250000) = 1/(250000 / 297029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (172368859 / 1000000000) (8618443 / 50000000) (Real.log (297029 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (297029 / 250000) = -Real.log (250000 / 297029) := by
    rw [show ((297029 / 250000) : ℝ) = ((250000 / 297029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (104198903 / 500000000) ≤ -Real.log (202971 / 250000) ∧
    -Real.log (202971 / 250000) ≤ (208397807 / 1000000000) := by
  have h := checkLog_sound (w := (47029 / 452971)) (n := 12)
    (lo := (104198903 / 500000000)) (hi := (208397807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202971) = 1/(202971 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-208397807 / 1000000000) (-104198903 / 500000000) (Real.log (202971 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125777659 / 1000000000) ≤ -Real.log (100000 / 113403) ∧
    -Real.log (100000 / 113403) ≤ (6288883 / 50000000) := by
  have h := checkLog_sound (w := (13403 / 213403)) (n := 12)
    (lo := (125777659 / 1000000000)) (hi := (6288883 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113403 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113403 / 100000) = 1/(100000 / 113403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125777659 / 1000000000) (6288883 / 50000000) (Real.log (113403 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (113403 / 100000) = -Real.log (100000 / 113403) := by
    rw [show ((113403 / 100000) : ℝ) = ((100000 / 113403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (143905013 / 1000000000) ≤ -Real.log (86597 / 100000) ∧
    -Real.log (86597 / 100000) ≤ (71952507 / 500000000) := by
  have h := checkLog_sound (w := (13403 / 186597)) (n := 12)
    (lo := (143905013 / 1000000000)) (hi := (71952507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86597) = 1/(86597 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-71952507 / 500000000) (-143905013 / 1000000000) (Real.log (86597 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126047457 / 1000000000) ≤ -Real.log (15625 / 17724) ∧
    -Real.log (15625 / 17724) ≤ (63023729 / 500000000) := by
  have h := checkLog_sound (w := (2099 / 33349)) (n := 12)
    (lo := (126047457 / 1000000000)) (hi := (63023729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17724 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17724 / 15625) = 1/(15625 / 17724) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126047457 / 1000000000) (63023729 / 500000000) (Real.log (17724 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (17724 / 15625) = -Real.log (15625 / 17724) := by
    rw [show ((17724 / 15625) : ℝ) = ((15625 / 17724) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36064609 / 250000000) ≤ -Real.log (13526 / 15625) ∧
    -Real.log (13526 / 15625) ≤ (144258437 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 29151)) (n := 12)
    (lo := (36064609 / 250000000)) (hi := (144258437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13526) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13526) = 1/(13526 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-144258437 / 1000000000) (-36064609 / 250000000) (Real.log (13526 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (271100373 / 500000000) ≤ -Real.log (5000000000 / 8598937583) ∧
    -Real.log (5000000000 / 8598937583) ≤ (542200747 / 1000000000) := by
  have h := checkLog_sound (w := (3598937583 / 13598937583)) (n := 12)
    (lo := (271100373 / 500000000)) (hi := (542200747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8598937583 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8598937583 / 5000000000) = 1/(5000000000 / 8598937583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (271100373 / 500000000) (542200747 / 1000000000) (Real.log (8598937583 / 5000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (8598937583 / 5000000000) = -Real.log (5000000000 / 8598937583) := by
    rw [show ((8598937583 / 5000000000) : ℝ) = ((5000000000 / 8598937583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (543461089 / 1000000000) ≤ -Real.log (125000000000 / 215244550771) ∧
    -Real.log (125000000000 / 215244550771) ≤ (54346109 / 100000000) := by
  have h := checkLog_sound (w := (90244550771 / 340244550771)) (n := 12)
    (lo := (543461089 / 1000000000)) (hi := (54346109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215244550771 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215244550771 / 125000000000) = 1/(125000000000 / 215244550771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (543461089 / 1000000000) (54346109 / 100000000) (Real.log (215244550771 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (215244550771 / 125000000000) = -Real.log (125000000000 / 215244550771) := by
    rw [show ((215244550771 / 125000000000) : ℝ) = ((125000000000 / 215244550771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (379897993 / 1000000000) ≤ -Real.log (500000000000 / 731067717341) ∧
    -Real.log (500000000000 / 731067717341) ≤ (189948997 / 500000000) := by
  have h := checkLog_sound (w := (231067717341 / 1231067717341)) (n := 12)
    (lo := (379897993 / 1000000000)) (hi := (189948997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731067717341 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731067717341 / 500000000000) = 1/(500000000000 / 731067717341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (379897993 / 1000000000) (189948997 / 500000000) (Real.log (731067717341 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (731067717341 / 500000000000) = -Real.log (500000000000 / 731067717341) := by
    rw [show ((731067717341 / 500000000000) : ℝ) = ((500000000000 / 731067717341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76153333 / 200000000) ≤ -Real.log (20000000000 / 29268122047) ∧
    -Real.log (20000000000 / 29268122047) ≤ (190383333 / 500000000) := by
  have h := checkLog_sound (w := (9268122047 / 49268122047)) (n := 12)
    (lo := (76153333 / 200000000)) (hi := (190383333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29268122047 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29268122047 / 20000000000) = 1/(20000000000 / 29268122047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (76153333 / 200000000) (190383333 / 500000000) (Real.log (29268122047 / 20000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (29268122047 / 20000000000) = -Real.log (20000000000 / 29268122047) := by
    rw [show ((29268122047 / 20000000000) : ℝ) = ((20000000000 / 29268122047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (269682673 / 1000000000) ≤ -Real.log (250000000000 / 327387207409) ∧
    -Real.log (250000000000 / 327387207409) ≤ (134841337 / 500000000) := by
  have h := checkLog_sound (w := (77387207409 / 577387207409)) (n := 12)
    (lo := (269682673 / 1000000000)) (hi := (134841337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327387207409 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327387207409 / 250000000000) = 1/(250000000000 / 327387207409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (269682673 / 1000000000) (134841337 / 500000000) (Real.log (327387207409 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (327387207409 / 250000000000) = -Real.log (250000000000 / 327387207409) := by
    rw [show ((327387207409 / 250000000000) : ℝ) = ((250000000000 / 327387207409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (135152947 / 500000000) ≤ -Real.log (125000000000 / 163795652817) ∧
    -Real.log (125000000000 / 163795652817) ≤ (54061179 / 200000000) := by
  have h := checkLog_sound (w := (38795652817 / 288795652817)) (n := 12)
    (lo := (135152947 / 500000000)) (hi := (54061179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163795652817 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163795652817 / 125000000000) = 1/(125000000000 / 163795652817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (135152947 / 500000000) (54061179 / 200000000) (Real.log (163795652817 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (163795652817 / 125000000000) = -Real.log (125000000000 / 163795652817) := by
    rw [show ((163795652817 / 125000000000) : ℝ) = ((125000000000 / 163795652817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9105489 / 500000000) ≤ -Real.log (239734824 / 244140625) ∧
    -Real.log (239734824 / 244140625) ≤ (18210979 / 1000000000) := by
  have h := checkLog_sound (w := (4405801 / 483875449)) (n := 12)
    (lo := (9105489 / 500000000)) (hi := (18210979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 239734824) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 239734824) = 1/(239734824 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18210979 / 1000000000) (-9105489 / 500000000) (Real.log (239734824 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18127353 / 1000000000) ≤ -Real.log (9820359591 / 10000000000) ∧
    -Real.log (9820359591 / 10000000000) ≤ (9063677 / 500000000) := by
  have h := checkLog_sound (w := (179640409 / 19820359591)) (n := 12)
    (lo := (18127353 / 1000000000)) (hi := (9063677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9820359591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9820359591) = 1/(9820359591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9063677 / 500000000) (-18127353 / 1000000000) (Real.log (9820359591 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell025

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell026Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell026
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

theorem reflection_log_1_neg : (11786019 / 50000000) ≤ -Real.log (5120 / 6481) ∧
    -Real.log (5120 / 6481) ≤ (235720381 / 1000000000) := by
  have h := checkLog_sound (w := (1361 / 11601)) (n := 12)
    (lo := (11786019 / 50000000)) (hi := (235720381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6481 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6481 / 5120) = 1/(5120 / 6481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11786019 / 50000000) (235720381 / 1000000000) (Real.log (6481 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6481 / 5120) = -Real.log (5120 / 6481) := by
    rw [show ((6481 / 5120) : ℝ) = ((5120 / 6481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (154500737 / 500000000) ≤ -Real.log (3759 / 5120) ∧
    -Real.log (3759 / 5120) ≤ (12360059 / 40000000) := by
  have h := checkLog_sound (w := (1361 / 8879)) (n := 12)
    (lo := (154500737 / 500000000)) (hi := (12360059 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3759) = 1/(3759 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12360059 / 40000000) (-154500737 / 500000000) (Real.log (3759 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (235257381 / 1000000000) ≤ -Real.log (2560 / 3239) ∧
    -Real.log (2560 / 3239) ≤ (117628691 / 500000000) := by
  have h := checkLog_sound (w := (679 / 5799)) (n := 12)
    (lo := (235257381 / 1000000000)) (hi := (117628691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3239 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3239 / 2560) = 1/(2560 / 3239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (235257381 / 1000000000) (117628691 / 500000000) (Real.log (3239 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3239 / 2560) = -Real.log (2560 / 3239) := by
    rw [show ((3239 / 2560) : ℝ) = ((2560 / 3239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (77050927 / 250000000) ≤ -Real.log (1881 / 2560) ∧
    -Real.log (1881 / 2560) ≤ (308203709 / 1000000000) := by
  have h := checkLog_sound (w := (679 / 4441)) (n := 12)
    (lo := (77050927 / 250000000)) (hi := (308203709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1881) = 1/(1881 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-308203709 / 1000000000) (-77050927 / 250000000) (Real.log (1881 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172368017 / 1000000000) ≤ -Real.log (200000 / 237623) ∧
    -Real.log (200000 / 237623) ≤ (86184009 / 500000000) := by
  have h := checkLog_sound (w := (37623 / 437623)) (n := 12)
    (lo := (172368017 / 1000000000)) (hi := (86184009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237623 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237623 / 200000) = 1/(200000 / 237623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172368017 / 1000000000) (86184009 / 500000000) (Real.log (237623 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (237623 / 200000) = -Real.log (200000 / 237623) := by
    rw [show ((237623 / 200000) : ℝ) = ((200000 / 237623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104198287 / 500000000) ≤ -Real.log (162377 / 200000) ∧
    -Real.log (162377 / 200000) ≤ (8335863 / 40000000) := by
  have h := checkLog_sound (w := (37623 / 362377)) (n := 12)
    (lo := (104198287 / 500000000)) (hi := (8335863 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162377) = 1/(162377 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-8335863 / 40000000) (-104198287 / 500000000) (Real.log (162377 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (86360307 / 500000000) ≤ -Real.log (500000 / 594267) ∧
    -Real.log (500000 / 594267) ≤ (34544123 / 200000000) := by
  have h := checkLog_sound (w := (94267 / 1094267)) (n := 12)
    (lo := (86360307 / 500000000)) (hi := (34544123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594267 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594267 / 500000) = 1/(500000 / 594267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (86360307 / 500000000) (34544123 / 200000000) (Real.log (594267 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (594267 / 500000) = -Real.log (500000 / 594267) := by
    rw [show ((594267 / 500000) : ℝ) = ((500000 / 594267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (20891279 / 100000000) ≤ -Real.log (405733 / 500000) ∧
    -Real.log (405733 / 500000) ≤ (208912791 / 1000000000) := by
  have h := checkLog_sound (w := (94267 / 905733)) (n := 12)
    (lo := (20891279 / 100000000)) (hi := (208912791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405733) = 1/(405733 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-208912791 / 1000000000) (-20891279 / 100000000) (Real.log (405733 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (7877911 / 62500000) ≤ -Real.log (200000 / 226867) ∧
    -Real.log (200000 / 226867) ≤ (126046577 / 1000000000) := by
  have h := checkLog_sound (w := (26867 / 426867)) (n := 12)
    (lo := (7877911 / 62500000)) (hi := (126046577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226867 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226867 / 200000) = 1/(200000 / 226867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (7877911 / 62500000) (126046577 / 1000000000) (Real.log (226867 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (226867 / 200000) = -Real.log (200000 / 226867) := by
    rw [show ((226867 / 200000) : ℝ) = ((200000 / 226867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (144257281 / 1000000000) ≤ -Real.log (173133 / 200000) ∧
    -Real.log (173133 / 200000) ≤ (72128641 / 500000000) := by
  have h := checkLog_sound (w := (26867 / 373133)) (n := 12)
    (lo := (144257281 / 1000000000)) (hi := (72128641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173133) = 1/(173133 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-72128641 / 500000000) (-144257281 / 1000000000) (Real.log (173133 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (6315771 / 50000000) ≤ -Real.log (12500 / 14183) ∧
    -Real.log (12500 / 14183) ≤ (126315421 / 1000000000) := by
  have h := checkLog_sound (w := (1683 / 26683)) (n := 12)
    (lo := (6315771 / 50000000)) (hi := (126315421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14183 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14183 / 12500) = 1/(12500 / 14183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (6315771 / 50000000) (126315421 / 1000000000) (Real.log (14183 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (14183 / 12500) = -Real.log (12500 / 14183) := by
    rw [show ((14183 / 12500) : ℝ) = ((12500 / 14183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (144609673 / 1000000000) ≤ -Real.log (10817 / 12500) ∧
    -Real.log (10817 / 12500) ≤ (72304837 / 500000000) := by
  have h := checkLog_sound (w := (1683 / 23317)) (n := 12)
    (lo := (144609673 / 1000000000)) (hi := (72304837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 10817) = 1/(10817 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-72304837 / 500000000) (-144609673 / 1000000000) (Real.log (10817 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (543461089 / 1000000000) ≤ -Real.log (500000000000 / 860978203083) ∧
    -Real.log (500000000000 / 860978203083) ≤ (54346109 / 100000000) := by
  have h := checkLog_sound (w := (360978203083 / 1360978203083)) (n := 12)
    (lo := (543461089 / 1000000000)) (hi := (54346109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((860978203083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(860978203083 / 500000000000) = 1/(500000000000 / 860978203083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (543461089 / 1000000000) (54346109 / 100000000) (Real.log (860978203083 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (860978203083 / 500000000000) = -Real.log (500000000000 / 860978203083) := by
    rw [show ((860978203083 / 500000000000) : ℝ) = ((500000000000 / 860978203083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (272360927 / 500000000) ≤ -Real.log (20000000000 / 34482575153) ∧
    -Real.log (20000000000 / 34482575153) ≤ (108944371 / 200000000) := by
  have h := checkLog_sound (w := (14482575153 / 54482575153)) (n := 12)
    (lo := (272360927 / 500000000)) (hi := (108944371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34482575153 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34482575153 / 20000000000) = 1/(20000000000 / 34482575153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (272360927 / 500000000) (108944371 / 200000000) (Real.log (34482575153 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (34482575153 / 20000000000) = -Real.log (20000000000 / 34482575153) := by
    rw [show ((34482575153 / 20000000000) : ℝ) = ((20000000000 / 34482575153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (23797787 / 62500000) ≤ -Real.log (125000000000 / 182925383521) ∧
    -Real.log (125000000000 / 182925383521) ≤ (380764593 / 1000000000) := by
  have h := checkLog_sound (w := (57925383521 / 307925383521)) (n := 12)
    (lo := (23797787 / 62500000)) (hi := (380764593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182925383521 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182925383521 / 125000000000) = 1/(125000000000 / 182925383521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (23797787 / 62500000) (380764593 / 1000000000) (Real.log (182925383521 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (182925383521 / 125000000000) = -Real.log (125000000000 / 182925383521) := by
    rw [show ((182925383521 / 125000000000) : ℝ) = ((125000000000 / 182925383521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76326681 / 200000000) ≤ -Real.log (25000000000 / 36616876123) ∧
    -Real.log (25000000000 / 36616876123) ≤ (190816703 / 500000000) := by
  have h := checkLog_sound (w := (11616876123 / 61616876123)) (n := 12)
    (lo := (76326681 / 200000000)) (hi := (190816703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36616876123 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36616876123 / 25000000000) = 1/(25000000000 / 36616876123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (76326681 / 200000000) (190816703 / 500000000) (Real.log (36616876123 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (36616876123 / 25000000000) = -Real.log (25000000000 / 36616876123) := by
    rw [show ((36616876123 / 25000000000) : ℝ) = ((25000000000 / 36616876123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (270303857 / 1000000000) ≤ -Real.log (500000000000 / 655181276821) ∧
    -Real.log (500000000000 / 655181276821) ≤ (135151929 / 500000000) := by
  have h := checkLog_sound (w := (155181276821 / 1155181276821)) (n := 12)
    (lo := (270303857 / 1000000000)) (hi := (135151929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655181276821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655181276821 / 500000000000) = 1/(500000000000 / 655181276821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (270303857 / 1000000000) (135151929 / 500000000) (Real.log (655181276821 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (655181276821 / 500000000000) = -Real.log (500000000000 / 655181276821) := by
    rw [show ((655181276821 / 500000000000) : ℝ) = ((500000000000 / 655181276821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (270925093 / 1000000000) ≤ -Real.log (500000000000 / 655588425627) ∧
    -Real.log (500000000000 / 655588425627) ≤ (135462547 / 500000000) := by
  have h := checkLog_sound (w := (155588425627 / 1155588425627)) (n := 12)
    (lo := (270925093 / 1000000000)) (hi := (135462547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655588425627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655588425627 / 500000000000) = 1/(500000000000 / 655588425627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (270925093 / 1000000000) (135462547 / 500000000) (Real.log (655588425627 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (655588425627 / 500000000000) = -Real.log (500000000000 / 655588425627) := by
    rw [show ((655588425627 / 500000000000) : ℝ) = ((500000000000 / 655588425627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18294253 / 1000000000) ≤ -Real.log (153417511 / 156250000) ∧
    -Real.log (153417511 / 156250000) ≤ (9147127 / 500000000) := by
  have h := checkLog_sound (w := (2832489 / 309667511)) (n := 12)
    (lo := (18294253 / 1000000000)) (hi := (9147127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 153417511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 153417511) = 1/(153417511 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9147127 / 500000000) (-18294253 / 1000000000) (Real.log (153417511 / 156250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3642141 / 200000000) ≤ -Real.log (39278164311 / 40000000000) ∧
    -Real.log (39278164311 / 40000000000) ≤ (9105353 / 500000000) := by
  have h := checkLog_sound (w := (721835689 / 79278164311)) (n := 12)
    (lo := (3642141 / 200000000)) (hi := (9105353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39278164311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39278164311) = 1/(39278164311 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9105353 / 500000000) (-3642141 / 200000000) (Real.log (39278164311 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell026

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell027Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell027
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

theorem reflection_log_1_neg : (59045791 / 250000000) ≤ -Real.log (1280 / 1621) ∧
    -Real.log (1280 / 1621) ≤ (47236633 / 200000000) := by
  have h := checkLog_sound (w := (341 / 2901)) (n := 12)
    (lo := (59045791 / 250000000)) (hi := (47236633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1621 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1621 / 1280) = 1/(1280 / 1621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (59045791 / 250000000) (47236633 / 200000000) (Real.log (1621 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1621 / 1280) = -Real.log (1280 / 1621) := by
    rw [show ((1621 / 1280) : ℝ) = ((1280 / 1621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (309799877 / 1000000000) ≤ -Real.log (939 / 1280) ∧
    -Real.log (939 / 1280) ≤ (154899939 / 500000000) := by
  have h := checkLog_sound (w := (341 / 2219)) (n := 12)
    (lo := (309799877 / 1000000000)) (hi := (154899939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 939) = 1/(939 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-154899939 / 500000000) (-309799877 / 1000000000) (Real.log (939 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11786019 / 50000000) ≤ -Real.log (5120 / 6481) ∧
    -Real.log (5120 / 6481) ≤ (235720381 / 1000000000) := by
  have h := checkLog_sound (w := (1361 / 11601)) (n := 12)
    (lo := (11786019 / 50000000)) (hi := (235720381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6481 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6481 / 5120) = 1/(5120 / 6481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11786019 / 50000000) (235720381 / 1000000000) (Real.log (6481 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6481 / 5120) = -Real.log (5120 / 6481) := by
    rw [show ((6481 / 5120) : ℝ) = ((5120 / 6481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (154500737 / 500000000) ≤ -Real.log (3759 / 5120) ∧
    -Real.log (3759 / 5120) ≤ (12360059 / 40000000) := by
  have h := checkLog_sound (w := (1361 / 8879)) (n := 12)
    (lo := (154500737 / 500000000)) (hi := (12360059 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3759) = 1/(3759 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12360059 / 40000000) (-154500737 / 500000000) (Real.log (3759 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172719773 / 1000000000) ≤ -Real.log (1000000 / 1188533) ∧
    -Real.log (1000000 / 1188533) ≤ (86359887 / 500000000) := by
  have h := checkLog_sound (w := (188533 / 2188533)) (n := 12)
    (lo := (172719773 / 1000000000)) (hi := (86359887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188533 / 1000000) = 1/(1000000 / 1188533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172719773 / 1000000000) (86359887 / 500000000) (Real.log (1188533 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1188533 / 1000000) = -Real.log (1000000 / 1188533) := by
    rw [show ((1188533 / 1000000) : ℝ) = ((1000000 / 1188533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104455779 / 500000000) ≤ -Real.log (811467 / 1000000) ∧
    -Real.log (811467 / 1000000) ≤ (208911559 / 1000000000) := by
  have h := checkLog_sound (w := (188533 / 1811467)) (n := 12)
    (lo := (104455779 / 500000000)) (hi := (208911559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811467) = 1/(811467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-208911559 / 1000000000) (-104455779 / 500000000) (Real.log (811467 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (86536123 / 500000000) ≤ -Real.log (125000 / 148619) ∧
    -Real.log (125000 / 148619) ≤ (173072247 / 1000000000) := by
  have h := checkLog_sound (w := (23619 / 273619)) (n := 12)
    (lo := (86536123 / 500000000)) (hi := (173072247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148619 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148619 / 125000) = 1/(125000 / 148619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (86536123 / 500000000) (173072247 / 1000000000) (Real.log (148619 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (148619 / 125000) = -Real.log (125000 / 148619) := by
    rw [show ((148619 / 125000) : ℝ) = ((125000 / 148619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5235701 / 25000000) ≤ -Real.log (101381 / 125000) ∧
    -Real.log (101381 / 125000) ≤ (209428041 / 1000000000) := by
  have h := checkLog_sound (w := (23619 / 226381)) (n := 12)
    (lo := (5235701 / 25000000)) (hi := (209428041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101381) = 1/(101381 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-209428041 / 1000000000) (-5235701 / 25000000) (Real.log (101381 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (63157269 / 500000000) ≤ -Real.log (1000000 / 1134639) ∧
    -Real.log (1000000 / 1134639) ≤ (126314539 / 1000000000) := by
  have h := checkLog_sound (w := (134639 / 2134639)) (n := 12)
    (lo := (63157269 / 500000000)) (hi := (126314539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1134639 / 1000000) = 1/(1000000 / 1134639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (63157269 / 500000000) (126314539 / 1000000000) (Real.log (1134639 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1134639 / 1000000) = -Real.log (1000000 / 1134639) := by
    rw [show ((1134639 / 1000000) : ℝ) = ((1000000 / 1134639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72304259 / 500000000) ≤ -Real.log (865361 / 1000000) ∧
    -Real.log (865361 / 1000000) ≤ (144608519 / 1000000000) := by
  have h := checkLog_sound (w := (134639 / 1865361)) (n := 12)
    (lo := (72304259 / 500000000)) (hi := (144608519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 865361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 865361) = 1/(865361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-144608519 / 1000000000) (-72304259 / 500000000) (Real.log (865361 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126584191 / 1000000000) ≤ -Real.log (200000 / 226989) ∧
    -Real.log (200000 / 226989) ≤ (988939 / 7812500) := by
  have h := checkLog_sound (w := (26989 / 426989)) (n := 12)
    (lo := (126584191 / 1000000000)) (hi := (988939 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226989 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226989 / 200000) = 1/(200000 / 226989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126584191 / 1000000000) (988939 / 7812500) (Real.log (226989 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (226989 / 200000) = -Real.log (200000 / 226989) := by
    rw [show ((226989 / 200000) : ℝ) = ((200000 / 226989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (14496219 / 100000000) ≤ -Real.log (173011 / 200000) ∧
    -Real.log (173011 / 200000) ≤ (144962191 / 1000000000) := by
  have h := checkLog_sound (w := (26989 / 373011)) (n := 12)
    (lo := (14496219 / 100000000)) (hi := (144962191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173011) = 1/(173011 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-144962191 / 1000000000) (-14496219 / 100000000) (Real.log (173011 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (272360927 / 500000000) ≤ -Real.log (62500000000 / 107758047353) ∧
    -Real.log (62500000000 / 107758047353) ≤ (108944371 / 200000000) := by
  have h := checkLog_sound (w := (45258047353 / 170258047353)) (n := 12)
    (lo := (272360927 / 500000000)) (hi := (108944371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107758047353 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107758047353 / 62500000000) = 1/(62500000000 / 107758047353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (272360927 / 500000000) (108944371 / 200000000) (Real.log (107758047353 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (107758047353 / 62500000000) = -Real.log (62500000000 / 107758047353) := by
    rw [show ((107758047353 / 62500000000) : ℝ) = ((62500000000 / 107758047353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (272991521 / 500000000) ≤ -Real.log (50000000000 / 86315228967) ∧
    -Real.log (50000000000 / 86315228967) ≤ (545983043 / 1000000000) := by
  have h := checkLog_sound (w := (36315228967 / 136315228967)) (n := 12)
    (lo := (272991521 / 500000000)) (hi := (545983043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86315228967 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86315228967 / 50000000000) = 1/(50000000000 / 86315228967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (272991521 / 500000000) (545983043 / 1000000000) (Real.log (86315228967 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (86315228967 / 50000000000) = -Real.log (50000000000 / 86315228967) := by
    rw [show ((86315228967 / 50000000000) : ℝ) = ((50000000000 / 86315228967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (381631331 / 1000000000) ≤ -Real.log (100000000000 / 146467200761) ∧
    -Real.log (100000000000 / 146467200761) ≤ (95407833 / 250000000) := by
  have h := checkLog_sound (w := (46467200761 / 246467200761)) (n := 12)
    (lo := (381631331 / 1000000000)) (hi := (95407833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146467200761 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146467200761 / 100000000000) = 1/(100000000000 / 146467200761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (381631331 / 1000000000) (95407833 / 250000000) (Real.log (146467200761 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (146467200761 / 100000000000) = -Real.log (100000000000 / 146467200761) := by
    rw [show ((146467200761 / 100000000000) : ℝ) = ((100000000000 / 146467200761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (382500287 / 1000000000) ≤ -Real.log (100000000000 / 146594529547) ∧
    -Real.log (100000000000 / 146594529547) ≤ (5976567 / 15625000) := by
  have h := checkLog_sound (w := (46594529547 / 246594529547)) (n := 12)
    (lo := (382500287 / 1000000000)) (hi := (5976567 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146594529547 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146594529547 / 100000000000) = 1/(100000000000 / 146594529547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (382500287 / 1000000000) (5976567 / 15625000) (Real.log (146594529547 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (146594529547 / 100000000000) = -Real.log (100000000000 / 146594529547) := by
    rw [show ((146594529547 / 100000000000) : ℝ) = ((100000000000 / 146594529547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (16932691 / 62500000) ≤ -Real.log (500000000000 / 655587090243) ∧
    -Real.log (500000000000 / 655587090243) ≤ (270923057 / 1000000000) := by
  have h := checkLog_sound (w := (155587090243 / 1155587090243)) (n := 12)
    (lo := (16932691 / 62500000)) (hi := (270923057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655587090243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655587090243 / 500000000000) = 1/(500000000000 / 655587090243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (16932691 / 62500000) (270923057 / 1000000000) (Real.log (655587090243 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (655587090243 / 500000000000) = -Real.log (500000000000 / 655587090243) := by
    rw [show ((655587090243 / 500000000000) : ℝ) = ((500000000000 / 655587090243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (271546381 / 1000000000) ≤ -Real.log (100000000000 / 131199172307) ∧
    -Real.log (100000000000 / 131199172307) ≤ (135773191 / 500000000) := by
  have h := checkLog_sound (w := (31199172307 / 231199172307)) (n := 12)
    (lo := (271546381 / 1000000000)) (hi := (135773191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131199172307 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131199172307 / 100000000000) = 1/(100000000000 / 131199172307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (271546381 / 1000000000) (135773191 / 500000000) (Real.log (131199172307 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (131199172307 / 100000000000) = -Real.log (100000000000 / 131199172307) := by
    rw [show ((131199172307 / 100000000000) : ℝ) = ((100000000000 / 131199172307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9188999 / 500000000) ≤ -Real.log (39271593879 / 40000000000) ∧
    -Real.log (39271593879 / 40000000000) ≤ (18377999 / 1000000000) := by
  have h := checkLog_sound (w := (728406121 / 79271593879)) (n := 12)
    (lo := (9188999 / 500000000)) (hi := (18377999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39271593879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39271593879) = 1/(39271593879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18377999 / 1000000000) (-9188999 / 500000000) (Real.log (39271593879 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18293979 / 1000000000) ≤ -Real.log (981872339679 / 1000000000000) ∧
    -Real.log (981872339679 / 1000000000000) ≤ (914699 / 50000000) := by
  have h := checkLog_sound (w := (18127660321 / 1981872339679)) (n := 12)
    (lo := (18293979 / 1000000000)) (hi := (914699 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981872339679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981872339679) = 1/(981872339679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-914699 / 50000000) (-18293979 / 1000000000) (Real.log (981872339679 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell027

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell028Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell028
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

theorem reflection_log_1_neg : (47329147 / 200000000) ≤ -Real.log (5120 / 6487) ∧
    -Real.log (5120 / 6487) ≤ (29580717 / 125000000) := by
  have h := checkLog_sound (w := (1367 / 11607)) (n := 12)
    (lo := (47329147 / 200000000)) (hi := (29580717 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6487 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6487 / 5120) = 1/(5120 / 6487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (47329147 / 200000000) (29580717 / 125000000) (Real.log (6487 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6487 / 5120) = -Real.log (5120 / 6487) := by
    rw [show ((6487 / 5120) : ℝ) = ((5120 / 6487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (155299459 / 500000000) ≤ -Real.log (3753 / 5120) ∧
    -Real.log (3753 / 5120) ≤ (310598919 / 1000000000) := by
  have h := checkLog_sound (w := (1367 / 8873)) (n := 12)
    (lo := (155299459 / 500000000)) (hi := (310598919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3753) = 1/(3753 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-310598919 / 1000000000) (-155299459 / 500000000) (Real.log (3753 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (59045791 / 250000000) ≤ -Real.log (1280 / 1621) ∧
    -Real.log (1280 / 1621) ≤ (47236633 / 200000000) := by
  have h := checkLog_sound (w := (341 / 2901)) (n := 12)
    (lo := (59045791 / 250000000)) (hi := (47236633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1621 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1621 / 1280) = 1/(1280 / 1621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (59045791 / 250000000) (47236633 / 200000000) (Real.log (1621 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1621 / 1280) = -Real.log (1280 / 1621) := by
    rw [show ((1621 / 1280) : ℝ) = ((1280 / 1621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (309799877 / 1000000000) ≤ -Real.log (939 / 1280) ∧
    -Real.log (939 / 1280) ≤ (154899939 / 500000000) := by
  have h := checkLog_sound (w := (341 / 2219)) (n := 12)
    (lo := (309799877 / 1000000000)) (hi := (154899939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 939) = 1/(939 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-154899939 / 500000000) (-309799877 / 1000000000) (Real.log (939 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (34614281 / 200000000) ≤ -Real.log (1000000 / 1188951) ∧
    -Real.log (1000000 / 1188951) ≤ (86535703 / 500000000) := by
  have h := checkLog_sound (w := (188951 / 2188951)) (n := 12)
    (lo := (34614281 / 200000000)) (hi := (86535703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188951 / 1000000) = 1/(1000000 / 1188951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (34614281 / 200000000) (86535703 / 500000000) (Real.log (1188951 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1188951 / 1000000) = -Real.log (1000000 / 1188951) := by
    rw [show ((1188951 / 1000000) : ℝ) = ((1000000 / 1188951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (209426807 / 1000000000) ≤ -Real.log (811049 / 1000000) ∧
    -Real.log (811049 / 1000000) ≤ (26178351 / 125000000) := by
  have h := checkLog_sound (w := (188951 / 1811049)) (n := 12)
    (lo := (209426807 / 1000000000)) (hi := (26178351 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811049) = 1/(811049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26178351 / 125000000) (-209426807 / 1000000000) (Real.log (811049 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (34684919 / 200000000) ≤ -Real.log (1000000 / 1189371) ∧
    -Real.log (1000000 / 1189371) ≤ (43356149 / 250000000) := by
  have h := checkLog_sound (w := (189371 / 2189371)) (n := 12)
    (lo := (34684919 / 200000000)) (hi := (43356149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189371 / 1000000) = 1/(1000000 / 1189371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (34684919 / 200000000) (43356149 / 250000000) (Real.log (1189371 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1189371 / 1000000) = -Real.log (1000000 / 1189371) := by
    rw [show ((1189371 / 1000000) : ℝ) = ((1000000 / 1189371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (209944789 / 1000000000) ≤ -Real.log (810629 / 1000000) ∧
    -Real.log (810629 / 1000000) ≤ (20994479 / 100000000) := by
  have h := checkLog_sound (w := (189371 / 1810629)) (n := 12)
    (lo := (209944789 / 1000000000)) (hi := (20994479 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810629) = 1/(810629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20994479 / 100000000) (-209944789 / 1000000000) (Real.log (810629 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12658331 / 100000000) ≤ -Real.log (31250 / 35467) ∧
    -Real.log (31250 / 35467) ≤ (126583311 / 1000000000) := by
  have h := checkLog_sound (w := (4217 / 66717)) (n := 12)
    (lo := (12658331 / 100000000)) (hi := (126583311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35467 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35467 / 31250) = 1/(31250 / 35467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12658331 / 100000000) (126583311 / 1000000000) (Real.log (35467 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (35467 / 31250) = -Real.log (31250 / 35467) := by
    rw [show ((35467 / 31250) : ℝ) = ((31250 / 35467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72480517 / 500000000) ≤ -Real.log (27033 / 31250) ∧
    -Real.log (27033 / 31250) ≤ (28992207 / 200000000) := by
  have h := checkLog_sound (w := (4217 / 58283)) (n := 12)
    (lo := (72480517 / 500000000)) (hi := (28992207 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27033) = 1/(27033 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28992207 / 200000000) (-72480517 / 500000000) (Real.log (27033 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (12685289 / 100000000) ≤ -Real.log (4000 / 4541) ∧
    -Real.log (4000 / 4541) ≤ (126852891 / 1000000000) := by
  have h := checkLog_sound (w := (541 / 8541)) (n := 12)
    (lo := (12685289 / 100000000)) (hi := (126852891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4541 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4541 / 4000) = 1/(4000 / 4541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (12685289 / 100000000) (126852891 / 1000000000) (Real.log (4541 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (4541 / 4000) = -Real.log (4000 / 4541) := by
    rw [show ((4541 / 4000) : ℝ) = ((4000 / 4541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (145314831 / 1000000000) ≤ -Real.log (3459 / 4000) ∧
    -Real.log (3459 / 4000) ≤ (9082177 / 62500000) := by
  have h := checkLog_sound (w := (541 / 7459)) (n := 12)
    (lo := (145314831 / 1000000000)) (hi := (9082177 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3459) = 1/(3459 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-9082177 / 62500000) (-145314831 / 1000000000) (Real.log (3459 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (272991521 / 500000000) ≤ -Real.log (500000000000 / 863152289669) ∧
    -Real.log (500000000000 / 863152289669) ≤ (545983043 / 1000000000) := by
  have h := checkLog_sound (w := (363152289669 / 1363152289669)) (n := 12)
    (lo := (272991521 / 500000000)) (hi := (545983043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863152289669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863152289669 / 500000000000) = 1/(500000000000 / 863152289669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (272991521 / 500000000) (545983043 / 1000000000) (Real.log (863152289669 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (863152289669 / 500000000000) = -Real.log (500000000000 / 863152289669) := by
    rw [show ((863152289669 / 500000000000) : ℝ) = ((500000000000 / 863152289669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (273622327 / 500000000) ≤ -Real.log (250000000000 / 432120969891) ∧
    -Real.log (250000000000 / 432120969891) ≤ (109448931 / 200000000) := by
  have h := checkLog_sound (w := (182120969891 / 682120969891)) (n := 12)
    (lo := (273622327 / 500000000)) (hi := (109448931 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432120969891 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432120969891 / 250000000000) = 1/(250000000000 / 432120969891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (273622327 / 500000000) (109448931 / 200000000) (Real.log (432120969891 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (432120969891 / 250000000000) = -Real.log (250000000000 / 432120969891) := by
    rw [show ((432120969891 / 250000000000) : ℝ) = ((250000000000 / 432120969891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (382498213 / 1000000000) ≤ -Real.log (100000000000 / 146594225503) ∧
    -Real.log (100000000000 / 146594225503) ≤ (191249107 / 500000000) := by
  have h := checkLog_sound (w := (46594225503 / 246594225503)) (n := 12)
    (lo := (382498213 / 1000000000)) (hi := (191249107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146594225503 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146594225503 / 100000000000) = 1/(100000000000 / 146594225503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (382498213 / 1000000000) (191249107 / 500000000) (Real.log (146594225503 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (146594225503 / 100000000000) = -Real.log (100000000000 / 146594225503) := by
    rw [show ((146594225503 / 100000000000) : ℝ) = ((100000000000 / 146594225503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76673877 / 200000000) ≤ -Real.log (100000000000 / 146721989961) ∧
    -Real.log (100000000000 / 146721989961) ≤ (191684693 / 500000000) := by
  have h := checkLog_sound (w := (46721989961 / 246721989961)) (n := 12)
    (lo := (76673877 / 200000000)) (hi := (191684693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146721989961 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146721989961 / 100000000000) = 1/(100000000000 / 146721989961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (76673877 / 200000000) (191684693 / 500000000) (Real.log (146721989961 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (146721989961 / 100000000000) = -Real.log (100000000000 / 146721989961) := by
    rw [show ((146721989961 / 100000000000) : ℝ) = ((100000000000 / 146721989961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (33943043 / 125000000) ≤ -Real.log (500000000000 / 655994525209) ∧
    -Real.log (500000000000 / 655994525209) ≤ (54308869 / 200000000) := by
  have h := checkLog_sound (w := (155994525209 / 1155994525209)) (n := 12)
    (lo := (33943043 / 125000000)) (hi := (54308869 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655994525209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655994525209 / 500000000000) = 1/(500000000000 / 655994525209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (33943043 / 125000000) (54308869 / 200000000) (Real.log (655994525209 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (655994525209 / 500000000000) = -Real.log (500000000000 / 655994525209) := by
    rw [show ((655994525209 / 500000000000) : ℝ) = ((500000000000 / 655994525209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (136083861 / 500000000) ≤ -Real.log (125000000000 / 164100896213) ∧
    -Real.log (125000000000 / 164100896213) ≤ (272167723 / 1000000000) := by
  have h := checkLog_sound (w := (39100896213 / 289100896213)) (n := 12)
    (lo := (136083861 / 500000000)) (hi := (272167723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164100896213 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164100896213 / 125000000000) = 1/(125000000000 / 164100896213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (136083861 / 500000000) (272167723 / 1000000000) (Real.log (164100896213 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (164100896213 / 125000000000) = -Real.log (125000000000 / 164100896213) := by
    rw [show ((164100896213 / 125000000000) : ℝ) = ((125000000000 / 164100896213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (923097 / 50000000) ≤ -Real.log (15707319 / 16000000) ∧
    -Real.log (15707319 / 16000000) ≤ (18461941 / 1000000000) := by
  have h := checkLog_sound (w := (292681 / 31707319)) (n := 12)
    (lo := (923097 / 50000000)) (hi := (18461941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15707319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15707319) = 1/(15707319 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18461941 / 1000000000) (-923097 / 50000000) (Real.log (15707319 / 16000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18377723 / 1000000000) ≤ -Real.log (958779411 / 976562500) ∧
    -Real.log (958779411 / 976562500) ≤ (4594431 / 250000000) := by
  have h := checkLog_sound (w := (17783089 / 1935341911)) (n := 12)
    (lo := (18377723 / 1000000000)) (hi := (4594431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 958779411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 958779411) = 1/(958779411 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4594431 / 250000000) (-18377723 / 1000000000) (Real.log (958779411 / 976562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell028

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell029Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell029
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

theorem reflection_log_1_neg : (237108091 / 1000000000) ≤ -Real.log (512 / 649) ∧
    -Real.log (512 / 649) ≤ (59277023 / 250000000) := by
  have h := checkLog_sound (w := (137 / 1161)) (n := 12)
    (lo := (237108091 / 1000000000)) (hi := (59277023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649 / 512) = 1/(512 / 649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (237108091 / 1000000000) (59277023 / 250000000) (Real.log (649 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (649 / 512) = -Real.log (512 / 649) := by
    rw [show ((649 / 512) : ℝ) = ((512 / 649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (311398599 / 1000000000) ≤ -Real.log (375 / 512) ∧
    -Real.log (375 / 512) ≤ (1556993 / 5000000) := by
  have h := checkLog_sound (w := (137 / 887)) (n := 12)
    (lo := (311398599 / 1000000000)) (hi := (1556993 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 375) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 375) = 1/(375 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1556993 / 5000000) (-311398599 / 1000000000) (Real.log (375 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (47329147 / 200000000) ≤ -Real.log (5120 / 6487) ∧
    -Real.log (5120 / 6487) ≤ (29580717 / 125000000) := by
  have h := checkLog_sound (w := (1367 / 11607)) (n := 12)
    (lo := (47329147 / 200000000)) (hi := (29580717 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6487 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6487 / 5120) = 1/(5120 / 6487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (47329147 / 200000000) (29580717 / 125000000) (Real.log (6487 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6487 / 5120) = -Real.log (5120 / 6487) := by
    rw [show ((6487 / 5120) : ℝ) = ((5120 / 6487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (155299459 / 500000000) ≤ -Real.log (3753 / 5120) ∧
    -Real.log (3753 / 5120) ≤ (310598919 / 1000000000) := by
  have h := checkLog_sound (w := (1367 / 8873)) (n := 12)
    (lo := (155299459 / 500000000)) (hi := (310598919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3753) = 1/(3753 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-310598919 / 1000000000) (-155299459 / 500000000) (Real.log (3753 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (86711457 / 500000000) ≤ -Real.log (1000000 / 1189369) ∧
    -Real.log (1000000 / 1189369) ≤ (34684583 / 200000000) := by
  have h := checkLog_sound (w := (189369 / 2189369)) (n := 12)
    (lo := (86711457 / 500000000)) (hi := (34684583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189369 / 1000000) = 1/(1000000 / 1189369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (86711457 / 500000000) (34684583 / 200000000) (Real.log (1189369 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1189369 / 1000000) = -Real.log (1000000 / 1189369) := by
    rw [show ((1189369 / 1000000) : ℝ) = ((1000000 / 1189369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104971161 / 500000000) ≤ -Real.log (810631 / 1000000) ∧
    -Real.log (810631 / 1000000) ≤ (209942323 / 1000000000) := by
  have h := checkLog_sound (w := (189369 / 1810631)) (n := 12)
    (lo := (104971161 / 500000000)) (hi := (209942323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810631) = 1/(810631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-209942323 / 1000000000) (-104971161 / 500000000) (Real.log (810631 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8688799 / 50000000) ≤ -Real.log (1000000 / 1189789) ∧
    -Real.log (1000000 / 1189789) ≤ (173775981 / 1000000000) := by
  have h := checkLog_sound (w := (189789 / 2189789)) (n := 12)
    (lo := (8688799 / 50000000)) (hi := (173775981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189789 / 1000000) = 1/(1000000 / 1189789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8688799 / 50000000) (173775981 / 1000000000) (Real.log (1189789 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1189789 / 1000000) = -Real.log (1000000 / 1189789) := by
    rw [show ((1189789 / 1000000) : ℝ) = ((1000000 / 1189789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (210460571 / 1000000000) ≤ -Real.log (810211 / 1000000) ∧
    -Real.log (810211 / 1000000) ≤ (52615143 / 250000000) := by
  have h := checkLog_sound (w := (189789 / 1810211)) (n := 12)
    (lo := (210460571 / 1000000000)) (hi := (52615143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810211) = 1/(810211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-52615143 / 250000000) (-210460571 / 1000000000) (Real.log (810211 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12685201 / 100000000) ≤ -Real.log (1000000 / 1135249) ∧
    -Real.log (1000000 / 1135249) ≤ (126852011 / 1000000000) := by
  have h := checkLog_sound (w := (135249 / 2135249)) (n := 12)
    (lo := (12685201 / 100000000)) (hi := (126852011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135249 / 1000000) = 1/(1000000 / 1135249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12685201 / 100000000) (126852011 / 1000000000) (Real.log (1135249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1135249 / 1000000) = -Real.log (1000000 / 1135249) := by
    rw [show ((1135249 / 1000000) : ℝ) = ((1000000 / 1135249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72656837 / 500000000) ≤ -Real.log (864751 / 1000000) ∧
    -Real.log (864751 / 1000000) ≤ (5812547 / 40000000) := by
  have h := checkLog_sound (w := (135249 / 1864751)) (n := 12)
    (lo := (72656837 / 500000000)) (hi := (5812547 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864751) = 1/(864751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5812547 / 40000000) (-72656837 / 500000000) (Real.log (864751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (127120637 / 1000000000) ≤ -Real.log (500000 / 567777) ∧
    -Real.log (500000 / 567777) ≤ (63560319 / 500000000) := by
  have h := checkLog_sound (w := (67777 / 1067777)) (n := 12)
    (lo := (127120637 / 1000000000)) (hi := (63560319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567777 / 500000) = 1/(500000 / 567777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (127120637 / 1000000000) (63560319 / 500000000) (Real.log (567777 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (567777 / 500000) = -Real.log (500000 / 567777) := by
    rw [show ((567777 / 500000) : ℝ) = ((500000 / 567777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (145666439 / 1000000000) ≤ -Real.log (432223 / 500000) ∧
    -Real.log (432223 / 500000) ≤ (3641661 / 25000000) := by
  have h := checkLog_sound (w := (67777 / 932223)) (n := 12)
    (lo := (145666439 / 1000000000)) (hi := (3641661 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432223) = 1/(432223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3641661 / 25000000) (-145666439 / 1000000000) (Real.log (432223 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (273622327 / 500000000) ≤ -Real.log (500000000000 / 864241939781) ∧
    -Real.log (500000000000 / 864241939781) ≤ (109448931 / 200000000) := by
  have h := checkLog_sound (w := (364241939781 / 1364241939781)) (n := 12)
    (lo := (273622327 / 500000000)) (hi := (109448931 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((864241939781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(864241939781 / 500000000000) = 1/(500000000000 / 864241939781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (273622327 / 500000000) (109448931 / 200000000) (Real.log (864241939781 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (864241939781 / 500000000000) = -Real.log (500000000000 / 864241939781) := by
    rw [show ((864241939781 / 500000000000) : ℝ) = ((500000000000 / 864241939781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (54850669 / 100000000) ≤ -Real.log (250000000000 / 432666666667) ∧
    -Real.log (250000000000 / 432666666667) ≤ (548506691 / 1000000000) := by
  have h := checkLog_sound (w := (182666666667 / 682666666667)) (n := 12)
    (lo := (54850669 / 100000000)) (hi := (548506691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432666666667 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432666666667 / 250000000000) = 1/(250000000000 / 432666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (54850669 / 100000000) (548506691 / 1000000000) (Real.log (432666666667 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (432666666667 / 250000000000) = -Real.log (250000000000 / 432666666667) := by
    rw [show ((432666666667 / 250000000000) : ℝ) = ((250000000000 / 432666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (95841309 / 250000000) ≤ -Real.log (31250000000 / 45850431639) ∧
    -Real.log (31250000000 / 45850431639) ≤ (383365237 / 1000000000) := by
  have h := checkLog_sound (w := (14600431639 / 77100431639)) (n := 12)
    (lo := (95841309 / 250000000)) (hi := (383365237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45850431639 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45850431639 / 31250000000) = 1/(31250000000 / 45850431639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95841309 / 250000000) (383365237 / 1000000000) (Real.log (45850431639 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (45850431639 / 31250000000) = -Real.log (31250000000 / 45850431639) := by
    rw [show ((45850431639 / 31250000000) : ℝ) = ((31250000000 / 45850431639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (384236551 / 1000000000) ≤ -Real.log (50000000000 / 73424638767) ∧
    -Real.log (50000000000 / 73424638767) ≤ (48029569 / 125000000) := by
  have h := checkLog_sound (w := (23424638767 / 123424638767)) (n := 12)
    (lo := (384236551 / 1000000000)) (hi := (48029569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73424638767 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73424638767 / 50000000000) = 1/(50000000000 / 73424638767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (384236551 / 1000000000) (48029569 / 125000000) (Real.log (73424638767 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (73424638767 / 50000000000) = -Real.log (50000000000 / 73424638767) := by
    rw [show ((73424638767 / 50000000000) : ℝ) = ((50000000000 / 73424638767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (68041421 / 250000000) ≤ -Real.log (500000000000 / 656402247583) ∧
    -Real.log (500000000000 / 656402247583) ≤ (54433137 / 200000000) := by
  have h := checkLog_sound (w := (156402247583 / 1156402247583)) (n := 12)
    (lo := (68041421 / 250000000)) (hi := (54433137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656402247583 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656402247583 / 500000000000) = 1/(500000000000 / 656402247583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (68041421 / 250000000) (54433137 / 200000000) (Real.log (656402247583 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (656402247583 / 500000000000) = -Real.log (500000000000 / 656402247583) := by
    rw [show ((656402247583 / 500000000000) : ℝ) = ((500000000000 / 656402247583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (272787077 / 1000000000) ≤ -Real.log (125000000000 / 164202564417) ∧
    -Real.log (125000000000 / 164202564417) ≤ (136393539 / 500000000) := by
  have h := checkLog_sound (w := (39202564417 / 289202564417)) (n := 12)
    (lo := (272787077 / 1000000000)) (hi := (136393539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164202564417 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164202564417 / 125000000000) = 1/(125000000000 / 164202564417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (272787077 / 1000000000) (136393539 / 500000000) (Real.log (164202564417 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (164202564417 / 125000000000) = -Real.log (125000000000 / 164202564417) := by
    rw [show ((164202564417 / 125000000000) : ℝ) = ((125000000000 / 164202564417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9272901 / 500000000) ≤ -Real.log (245406278271 / 250000000000) ∧
    -Real.log (245406278271 / 250000000000) ≤ (18545803 / 1000000000) := by
  have h := checkLog_sound (w := (4593721729 / 495406278271)) (n := 12)
    (lo := (9272901 / 500000000)) (hi := (18545803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245406278271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245406278271) = 1/(245406278271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18545803 / 1000000000) (-9272901 / 500000000) (Real.log (245406278271 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (576927 / 31250000) ≤ -Real.log (981707707999 / 1000000000000) ∧
    -Real.log (981707707999 / 1000000000000) ≤ (3692333 / 200000000) := by
  have h := checkLog_sound (w := (18292292001 / 1981707707999)) (n := 12)
    (lo := (576927 / 31250000)) (hi := (3692333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981707707999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981707707999) = 1/(981707707999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3692333 / 200000000) (-576927 / 31250000) (Real.log (981707707999 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell029

end


