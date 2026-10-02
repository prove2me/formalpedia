-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell205Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell205Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:36:43.208996+00:00
-- url     : https://prove2.me/theorems/c890cd41-502c-4bed-bbce-e264c7d7d0b8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell205Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell206…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell205Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell206Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell207Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell208Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell205Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell206Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell207Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell208Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell205Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell206Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell207Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell208Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell205Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell206Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell207Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell208Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell205Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell205
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

theorem reflection_log_1_neg : (157661919 / 500000000) ≤ -Real.log (2560 / 3509) ∧
    -Real.log (2560 / 3509) ≤ (315323839 / 1000000000) := by
  have h := checkLog_sound (w := (949 / 6069)) (n := 12)
    (lo := (157661919 / 500000000)) (hi := (315323839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3509 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3509 / 2560) = 1/(2560 / 3509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (157661919 / 500000000) (315323839 / 1000000000) (Real.log (3509 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3509 / 2560) = -Real.log (2560 / 3509) := by
    rw [show ((3509 / 2560) : ℝ) = ((2560 / 3509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (231576077 / 500000000) ≤ -Real.log (1611 / 2560) ∧
    -Real.log (1611 / 2560) ≤ (92630431 / 200000000) := by
  have h := checkLog_sound (w := (949 / 4171)) (n := 12)
    (lo := (231576077 / 500000000)) (hi := (92630431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1611) = 1/(1611 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-92630431 / 200000000) (-231576077 / 500000000) (Real.log (1611 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157448137 / 500000000) ≤ -Real.log (1024 / 1403) ∧
    -Real.log (1024 / 1403) ≤ (12595851 / 40000000) := by
  have h := checkLog_sound (w := (379 / 2427)) (n := 12)
    (lo := (157448137 / 500000000)) (hi := (12595851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403 / 1024) = 1/(1024 / 1403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (157448137 / 500000000) (12595851 / 40000000) (Real.log (1403 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1403 / 1024) = -Real.log (1024 / 1403) := by
    rw [show ((1403 / 1024) : ℝ) = ((1024 / 1403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28888843 / 62500000) ≤ -Real.log (645 / 1024) ∧
    -Real.log (645 / 1024) ≤ (462221489 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1669)) (n := 12)
    (lo := (28888843 / 62500000)) (hi := (462221489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 645) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 645) = 1/(645 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-462221489 / 1000000000) (-28888843 / 62500000) (Real.log (645 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23372497 / 100000000) ≤ -Real.log (1000000 / 1263297) ∧
    -Real.log (1000000 / 1263297) ≤ (233724971 / 1000000000) := by
  have h := checkLog_sound (w := (263297 / 2263297)) (n := 12)
    (lo := (23372497 / 100000000)) (hi := (233724971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1263297 / 1000000) = 1/(1000000 / 1263297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23372497 / 100000000) (233724971 / 1000000000) (Real.log (1263297 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1263297 / 1000000) = -Real.log (1000000 / 1263297) := by
    rw [show ((1263297 / 1000000) : ℝ) = ((1000000 / 1263297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (305570453 / 1000000000) ≤ -Real.log (736703 / 1000000) ∧
    -Real.log (736703 / 1000000) ≤ (152785227 / 500000000) := by
  have h := checkLog_sound (w := (263297 / 1736703)) (n := 12)
    (lo := (305570453 / 1000000000)) (hi := (152785227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 736703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 736703) = 1/(736703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-152785227 / 500000000) (-305570453 / 1000000000) (Real.log (736703 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (29257469 / 125000000) ≤ -Real.log (25000 / 31593) ∧
    -Real.log (25000 / 31593) ≤ (234059753 / 1000000000) := by
  have h := checkLog_sound (w := (6593 / 56593)) (n := 12)
    (lo := (29257469 / 125000000)) (hi := (234059753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31593 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31593 / 25000) = 1/(25000 / 31593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (29257469 / 125000000) (234059753 / 1000000000) (Real.log (31593 / 25000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (31593 / 25000) = -Real.log (25000 / 31593) := by
    rw [show ((31593 / 25000) : ℝ) = ((25000 / 31593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (306144797 / 1000000000) ≤ -Real.log (18407 / 25000) ∧
    -Real.log (18407 / 25000) ≤ (153072399 / 500000000) := by
  have h := checkLog_sound (w := (6593 / 43407)) (n := 12)
    (lo := (306144797 / 1000000000)) (hi := (153072399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18407) = 1/(18407 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-153072399 / 500000000) (-306144797 / 1000000000) (Real.log (18407 / 25000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (173805397 / 1000000000) ≤ -Real.log (15625 / 18591) ∧
    -Real.log (15625 / 18591) ≤ (86902699 / 500000000) := by
  have h := checkLog_sound (w := (1483 / 17108)) (n := 12)
    (lo := (173805397 / 1000000000)) (hi := (86902699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18591 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18591 / 15625) = 1/(15625 / 18591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (173805397 / 1000000000) (86902699 / 500000000) (Real.log (18591 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (18591 / 15625) = -Real.log (15625 / 18591) := by
    rw [show ((18591 / 15625) : ℝ) = ((15625 / 18591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21050377 / 100000000) ≤ -Real.log (12659 / 15625) ∧
    -Real.log (12659 / 15625) ≤ (210503771 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 14142)) (n := 12)
    (lo := (21050377 / 100000000)) (hi := (210503771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12659) = 1/(12659 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-210503771 / 1000000000) (-21050377 / 100000000) (Real.log (12659 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (174071787 / 1000000000) ≤ -Real.log (1000000 / 1190141) ∧
    -Real.log (1000000 / 1190141) ≤ (43517947 / 250000000) := by
  have h := checkLog_sound (w := (190141 / 2190141)) (n := 12)
    (lo := (174071787 / 1000000000)) (hi := (43517947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1190141 / 1000000) = 1/(1000000 / 1190141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (174071787 / 1000000000) (43517947 / 250000000) (Real.log (1190141 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1190141 / 1000000) = -Real.log (1000000 / 1190141) := by
    rw [show ((1190141 / 1000000) : ℝ) = ((1000000 / 1190141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2636189 / 12500000) ≤ -Real.log (809859 / 1000000) ∧
    -Real.log (809859 / 1000000) ≤ (210895121 / 1000000000) := by
  have h := checkLog_sound (w := (190141 / 1809859)) (n := 12)
    (lo := (2636189 / 12500000)) (hi := (210895121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 809859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 809859) = 1/(809859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-210895121 / 1000000000) (-2636189 / 12500000) (Real.log (809859 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (388558881 / 500000000) ≤ -Real.log (62500000000 / 135949612403) ∧
    -Real.log (62500000000 / 135949612403) ≤ (194279441 / 250000000) := by
  have h := checkLog_sound (w := (10949612403 / 260949612403)) (n := 12)
    (lo := (41985291 / 500000000)) (hi := (83970583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135949612403 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(135949612403 / 125000000000) = 1/(62500000000 / 135949612403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (388558881 / 500000000) (194279441 / 250000000) (Real.log (135949612403 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (135949612403 / 62500000000) = -Real.log (62500000000 / 135949612403) := by
    rw [show ((135949612403 / 62500000000) : ℝ) = ((62500000000 / 135949612403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (778475991 / 1000000000) ≤ -Real.log (500000000000 / 1089075108629) ∧
    -Real.log (500000000000 / 1089075108629) ≤ (778475993 / 1000000000) := by
  have h := checkLog_sound (w := (89075108629 / 2089075108629)) (n := 12)
    (lo := (85328811 / 1000000000)) (hi := (21332203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089075108629 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1089075108629 / 1000000000000) = 1/(500000000000 / 1089075108629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (778475991 / 1000000000) (778475993 / 1000000000) (Real.log (1089075108629 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1089075108629 / 500000000000) = -Real.log (500000000000 / 1089075108629) := by
    rw [show ((1089075108629 / 500000000000) : ℝ) = ((500000000000 / 1089075108629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (539295423 / 1000000000) ≤ -Real.log (31250000000 / 53587444669) ∧
    -Real.log (31250000000 / 53587444669) ≤ (8426491 / 15625000) := by
  have h := checkLog_sound (w := (22337444669 / 84837444669)) (n := 12)
    (lo := (539295423 / 1000000000)) (hi := (8426491 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53587444669 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53587444669 / 31250000000) = 1/(31250000000 / 53587444669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (539295423 / 1000000000) (8426491 / 15625000) (Real.log (53587444669 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (53587444669 / 31250000000) = -Real.log (31250000000 / 53587444669) := by
    rw [show ((53587444669 / 31250000000) : ℝ) = ((31250000000 / 53587444669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10804091 / 20000000) ≤ -Real.log (500000000000 / 858178953659) ∧
    -Real.log (500000000000 / 858178953659) ≤ (540204551 / 1000000000) := by
  have h := checkLog_sound (w := (358178953659 / 1358178953659)) (n := 12)
    (lo := (10804091 / 20000000)) (hi := (540204551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858178953659 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858178953659 / 500000000000) = 1/(500000000000 / 858178953659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (10804091 / 20000000) (540204551 / 1000000000) (Real.log (858178953659 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (858178953659 / 500000000000) = -Real.log (500000000000 / 858178953659) := by
    rw [show ((858178953659 / 500000000000) : ℝ) = ((500000000000 / 858178953659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (384309167 / 1000000000) ≤ -Real.log (500000000000 / 734299707717) ∧
    -Real.log (500000000000 / 734299707717) ≤ (24019323 / 62500000) := by
  have h := checkLog_sound (w := (234299707717 / 1234299707717)) (n := 12)
    (lo := (384309167 / 1000000000)) (hi := (24019323 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734299707717 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734299707717 / 500000000000) = 1/(500000000000 / 734299707717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (384309167 / 1000000000) (24019323 / 62500000) (Real.log (734299707717 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (734299707717 / 500000000000) = -Real.log (500000000000 / 734299707717) := by
    rw [show ((734299707717 / 500000000000) : ℝ) = ((500000000000 / 734299707717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (96241727 / 250000000) ≤ -Real.log (100000000000 / 146956568983) ∧
    -Real.log (100000000000 / 146956568983) ≤ (384966909 / 1000000000) := by
  have h := checkLog_sound (w := (46956568983 / 246956568983)) (n := 12)
    (lo := (96241727 / 250000000)) (hi := (384966909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146956568983 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146956568983 / 100000000000) = 1/(100000000000 / 146956568983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (96241727 / 250000000) (384966909 / 1000000000) (Real.log (146956568983 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (146956568983 / 100000000000) = -Real.log (100000000000 / 146956568983) := by
    rw [show ((146956568983 / 100000000000) : ℝ) = ((100000000000 / 146956568983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36823333 / 1000000000) ≤ -Real.log (963846400119 / 1000000000000) ∧
    -Real.log (963846400119 / 1000000000000) ≤ (18411667 / 500000000) := by
  have h := checkLog_sound (w := (36153599881 / 1963846400119)) (n := 12)
    (lo := (36823333 / 1000000000)) (hi := (18411667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963846400119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963846400119) = 1/(963846400119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18411667 / 500000000) (-36823333 / 1000000000) (Real.log (963846400119 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (36698373 / 1000000000) ≤ -Real.log (235343469 / 244140625) ∧
    -Real.log (235343469 / 244140625) ≤ (18349187 / 500000000) := by
  have h := checkLog_sound (w := (4398578 / 239742047)) (n := 12)
    (lo := (36698373 / 1000000000)) (hi := (18349187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 235343469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 235343469) = 1/(235343469 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18349187 / 500000000) (-36698373 / 1000000000) (Real.log (235343469 / 244140625)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell205

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell206Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell206
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

theorem reflection_log_1_neg : (157875609 / 500000000) ≤ -Real.log (5120 / 7021) ∧
    -Real.log (5120 / 7021) ≤ (315751219 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 12141)) (n := 12)
    (lo := (157875609 / 500000000)) (hi := (315751219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7021 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7021 / 5120) = 1/(5120 / 7021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (157875609 / 500000000) (315751219 / 1000000000) (Real.log (7021 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7021 / 5120) = -Real.log (5120 / 7021) := by
    rw [show ((7021 / 5120) : ℝ) = ((5120 / 7021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (232041843 / 500000000) ≤ -Real.log (3219 / 5120) ∧
    -Real.log (3219 / 5120) ≤ (464083687 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 8339)) (n := 12)
    (lo := (232041843 / 500000000)) (hi := (464083687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3219) = 1/(3219 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-464083687 / 1000000000) (-232041843 / 500000000) (Real.log (3219 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157661919 / 500000000) ≤ -Real.log (2560 / 3509) ∧
    -Real.log (2560 / 3509) ≤ (315323839 / 1000000000) := by
  have h := checkLog_sound (w := (949 / 6069)) (n := 12)
    (lo := (157661919 / 500000000)) (hi := (315323839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3509 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3509 / 2560) = 1/(2560 / 3509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (157661919 / 500000000) (315323839 / 1000000000) (Real.log (3509 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3509 / 2560) = -Real.log (2560 / 3509) := by
    rw [show ((3509 / 2560) : ℝ) = ((2560 / 3509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (231576077 / 500000000) ≤ -Real.log (1611 / 2560) ∧
    -Real.log (1611 / 2560) ≤ (92630431 / 200000000) := by
  have h := checkLog_sound (w := (949 / 4171)) (n := 12)
    (lo := (231576077 / 500000000)) (hi := (92630431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1611) = 1/(1611 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-92630431 / 200000000) (-231576077 / 500000000) (Real.log (1611 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2925737 / 12500000) ≤ -Real.log (1000000 / 1263719) ∧
    -Real.log (1000000 / 1263719) ≤ (234058961 / 1000000000) := by
  have h := checkLog_sound (w := (263719 / 2263719)) (n := 12)
    (lo := (2925737 / 12500000)) (hi := (234058961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1263719 / 1000000) = 1/(1000000 / 1263719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2925737 / 12500000) (234058961 / 1000000000) (Real.log (1263719 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1263719 / 1000000) = -Real.log (1000000 / 1263719) := by
    rw [show ((1263719 / 1000000) : ℝ) = ((1000000 / 1263719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (306143439 / 1000000000) ≤ -Real.log (736281 / 1000000) ∧
    -Real.log (736281 / 1000000) ≤ (3826793 / 12500000) := by
  have h := checkLog_sound (w := (263719 / 1736281)) (n := 12)
    (lo := (306143439 / 1000000000)) (hi := (3826793 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 736281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 736281) = 1/(736281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3826793 / 12500000) (-306143439 / 1000000000) (Real.log (736281 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (117197211 / 500000000) ≤ -Real.log (1000000 / 1264143) ∧
    -Real.log (1000000 / 1264143) ≤ (234394423 / 1000000000) := by
  have h := checkLog_sound (w := (264143 / 2264143)) (n := 12)
    (lo := (117197211 / 500000000)) (hi := (234394423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264143 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264143 / 1000000) = 1/(1000000 / 1264143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (117197211 / 500000000) (234394423 / 1000000000) (Real.log (1264143 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1264143 / 1000000) = -Real.log (1000000 / 1264143) := by
    rw [show ((1264143 / 1000000) : ℝ) = ((1000000 / 1264143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (19169967 / 62500000) ≤ -Real.log (735857 / 1000000) ∧
    -Real.log (735857 / 1000000) ≤ (306719473 / 1000000000) := by
  have h := checkLog_sound (w := (264143 / 1735857)) (n := 12)
    (lo := (19169967 / 62500000)) (hi := (306719473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735857) = 1/(735857 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-306719473 / 1000000000) (-19169967 / 62500000) (Real.log (735857 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (174070947 / 1000000000) ≤ -Real.log (50000 / 59507) ∧
    -Real.log (50000 / 59507) ≤ (43517737 / 250000000) := by
  have h := checkLog_sound (w := (9507 / 109507)) (n := 12)
    (lo := (174070947 / 1000000000)) (hi := (43517737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59507 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59507 / 50000) = 1/(50000 / 59507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (174070947 / 1000000000) (43517737 / 250000000) (Real.log (59507 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (59507 / 50000) = -Real.log (50000 / 59507) := by
    rw [show ((59507 / 50000) : ℝ) = ((50000 / 59507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (42178777 / 200000000) ≤ -Real.log (40493 / 50000) ∧
    -Real.log (40493 / 50000) ≤ (105446943 / 500000000) := by
  have h := checkLog_sound (w := (9507 / 90493)) (n := 12)
    (lo := (42178777 / 200000000)) (hi := (105446943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40493) = 1/(40493 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-105446943 / 500000000) (-42178777 / 200000000) (Real.log (40493 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (174338107 / 1000000000) ≤ -Real.log (500000 / 595229) ∧
    -Real.log (500000 / 595229) ≤ (43584527 / 250000000) := by
  have h := checkLog_sound (w := (95229 / 1095229)) (n := 12)
    (lo := (174338107 / 1000000000)) (hi := (43584527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595229 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595229 / 500000) = 1/(500000 / 595229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (174338107 / 1000000000) (43584527 / 250000000) (Real.log (595229 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (595229 / 500000) = -Real.log (500000 / 595229) := by
    rw [show ((595229 / 500000) : ℝ) = ((500000 / 595229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (211286623 / 1000000000) ≤ -Real.log (404771 / 500000) ∧
    -Real.log (404771 / 500000) ≤ (6602707 / 31250000) := by
  have h := checkLog_sound (w := (95229 / 904771)) (n := 12)
    (lo := (211286623 / 1000000000)) (hi := (6602707 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404771) = 1/(404771 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6602707 / 31250000) (-211286623 / 1000000000) (Real.log (404771 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (778475991 / 1000000000) ≤ -Real.log (125000000000 / 272268777157) ∧
    -Real.log (125000000000 / 272268777157) ≤ (778475993 / 1000000000) := by
  have h := checkLog_sound (w := (22268777157 / 522268777157)) (n := 12)
    (lo := (85328811 / 1000000000)) (hi := (21332203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272268777157 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272268777157 / 250000000000) = 1/(125000000000 / 272268777157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (778475991 / 1000000000) (778475993 / 1000000000) (Real.log (272268777157 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (272268777157 / 125000000000) = -Real.log (125000000000 / 272268777157) := by
    rw [show ((272268777157 / 125000000000) : ℝ) = ((125000000000 / 272268777157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (155966981 / 200000000) ≤ -Real.log (100000000000 / 218111214663) ∧
    -Real.log (100000000000 / 218111214663) ≤ (779834907 / 1000000000) := by
  have h := checkLog_sound (w := (18111214663 / 418111214663)) (n := 12)
    (lo := (3467509 / 40000000)) (hi := (43343863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218111214663 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(218111214663 / 200000000000) = 1/(100000000000 / 218111214663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (155966981 / 200000000) (779834907 / 1000000000) (Real.log (218111214663 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (218111214663 / 100000000000) = -Real.log (100000000000 / 218111214663) := by
    rw [show ((218111214663 / 100000000000) : ℝ) = ((100000000000 / 218111214663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (675253 / 1250000) ≤ -Real.log (500000000000 / 858177109011) ∧
    -Real.log (500000000000 / 858177109011) ≤ (540202401 / 1000000000) := by
  have h := checkLog_sound (w := (358177109011 / 1358177109011)) (n := 12)
    (lo := (675253 / 1250000)) (hi := (540202401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858177109011 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858177109011 / 500000000000) = 1/(500000000000 / 858177109011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675253 / 1250000) (540202401 / 1000000000) (Real.log (858177109011 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (858177109011 / 500000000000) = -Real.log (500000000000 / 858177109011) := by
    rw [show ((858177109011 / 500000000000) : ℝ) = ((500000000000 / 858177109011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (270556947 / 500000000) ≤ -Real.log (500000000000 / 858959689179) ∧
    -Real.log (500000000000 / 858959689179) ≤ (108222779 / 200000000) := by
  have h := checkLog_sound (w := (358959689179 / 1358959689179)) (n := 12)
    (lo := (270556947 / 500000000)) (hi := (108222779 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858959689179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858959689179 / 500000000000) = 1/(500000000000 / 858959689179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (270556947 / 500000000) (108222779 / 200000000) (Real.log (858959689179 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (858959689179 / 500000000000) = -Real.log (500000000000 / 858959689179) := by
    rw [show ((858959689179 / 500000000000) : ℝ) = ((500000000000 / 858959689179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (384964833 / 1000000000) ≤ -Real.log (125000000000 / 183695330057) ∧
    -Real.log (125000000000 / 183695330057) ≤ (192482417 / 500000000) := by
  have h := checkLog_sound (w := (58695330057 / 308695330057)) (n := 12)
    (lo := (384964833 / 1000000000)) (hi := (192482417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183695330057 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183695330057 / 125000000000) = 1/(125000000000 / 183695330057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (384964833 / 1000000000) (192482417 / 500000000) (Real.log (183695330057 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (183695330057 / 125000000000) = -Real.log (125000000000 / 183695330057) := by
    rw [show ((183695330057 / 125000000000) : ℝ) = ((125000000000 / 183695330057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (38562473 / 100000000) ≤ -Real.log (250000000000 / 367633180243) ∧
    -Real.log (250000000000 / 367633180243) ≤ (385624731 / 1000000000) := by
  have h := checkLog_sound (w := (117633180243 / 617633180243)) (n := 12)
    (lo := (38562473 / 100000000)) (hi := (385624731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367633180243 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367633180243 / 250000000000) = 1/(250000000000 / 367633180243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (38562473 / 100000000) (385624731 / 1000000000) (Real.log (367633180243 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (367633180243 / 250000000000) = -Real.log (250000000000 / 367633180243) := by
    rw [show ((367633180243 / 250000000000) : ℝ) = ((250000000000 / 367633180243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9237129 / 250000000) ≤ -Real.log (240931437559 / 250000000000) ∧
    -Real.log (240931437559 / 250000000000) ≤ (36948517 / 1000000000) := by
  have h := checkLog_sound (w := (9068562441 / 490931437559)) (n := 12)
    (lo := (9237129 / 250000000)) (hi := (36948517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240931437559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240931437559) = 1/(240931437559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-36948517 / 1000000000) (-9237129 / 250000000) (Real.log (240931437559 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18411469 / 500000000) ≤ -Real.log (2409616951 / 2500000000) ∧
    -Real.log (2409616951 / 2500000000) ≤ (36822939 / 1000000000) := by
  have h := checkLog_sound (w := (90383049 / 4909616951)) (n := 12)
    (lo := (18411469 / 500000000)) (hi := (36822939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2409616951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2409616951) = 1/(2409616951 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-36822939 / 1000000000) (-18411469 / 500000000) (Real.log (2409616951 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell206

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell207Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell207
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

theorem reflection_log_1_neg : (316178417 / 1000000000) ≤ -Real.log (320 / 439) ∧
    -Real.log (320 / 439) ≤ (158089209 / 500000000) := by
  have h := checkLog_sound (w := (119 / 759)) (n := 12)
    (lo := (316178417 / 1000000000)) (hi := (158089209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(439 / 320) = 1/(320 / 439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (316178417 / 1000000000) (158089209 / 500000000) (Real.log (439 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (439 / 320) = -Real.log (320 / 439) := by
    rw [show ((439 / 320) : ℝ) = ((320 / 439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (465016087 / 1000000000) ≤ -Real.log (201 / 320) ∧
    -Real.log (201 / 320) ≤ (58127011 / 125000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 201) = 1/(201 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58127011 / 125000000) (-465016087 / 1000000000) (Real.log (201 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157875609 / 500000000) ≤ -Real.log (5120 / 7021) ∧
    -Real.log (5120 / 7021) ≤ (315751219 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 12141)) (n := 12)
    (lo := (157875609 / 500000000)) (hi := (315751219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7021 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7021 / 5120) = 1/(5120 / 7021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (157875609 / 500000000) (315751219 / 1000000000) (Real.log (7021 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7021 / 5120) = -Real.log (5120 / 7021) := by
    rw [show ((7021 / 5120) : ℝ) = ((5120 / 7021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (232041843 / 500000000) ≤ -Real.log (3219 / 5120) ∧
    -Real.log (3219 / 5120) ≤ (464083687 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 8339)) (n := 12)
    (lo := (232041843 / 500000000)) (hi := (464083687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3219) = 1/(3219 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-464083687 / 1000000000) (-232041843 / 500000000) (Real.log (3219 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (5859821 / 25000000) ≤ -Real.log (1000000 / 1264141) ∧
    -Real.log (1000000 / 1264141) ≤ (234392841 / 1000000000) := by
  have h := checkLog_sound (w := (264141 / 2264141)) (n := 12)
    (lo := (5859821 / 25000000)) (hi := (234392841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264141 / 1000000) = 1/(1000000 / 1264141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (5859821 / 25000000) (234392841 / 1000000000) (Real.log (1264141 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1264141 / 1000000) = -Real.log (1000000 / 1264141) := by
    rw [show ((1264141 / 1000000) : ℝ) = ((1000000 / 1264141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (153358377 / 500000000) ≤ -Real.log (735859 / 1000000) ∧
    -Real.log (735859 / 1000000) ≤ (61343351 / 200000000) := by
  have h := checkLog_sound (w := (264141 / 1735859)) (n := 12)
    (lo := (153358377 / 500000000)) (hi := (61343351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735859) = 1/(735859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-61343351 / 200000000) (-153358377 / 500000000) (Real.log (735859 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (234728189 / 1000000000) ≤ -Real.log (200000 / 252913) ∧
    -Real.log (200000 / 252913) ≤ (23472819 / 100000000) := by
  have h := checkLog_sound (w := (52913 / 452913)) (n := 12)
    (lo := (234728189 / 1000000000)) (hi := (23472819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252913 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252913 / 200000) = 1/(200000 / 252913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (234728189 / 1000000000) (23472819 / 100000000) (Real.log (252913 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (252913 / 200000) = -Real.log (200000 / 252913) := by
    rw [show ((252913 / 200000) : ℝ) = ((200000 / 252913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (153646559 / 500000000) ≤ -Real.log (147087 / 200000) ∧
    -Real.log (147087 / 200000) ≤ (307293119 / 1000000000) := by
  have h := checkLog_sound (w := (52913 / 347087)) (n := 12)
    (lo := (153646559 / 500000000)) (hi := (307293119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147087) = 1/(147087 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-307293119 / 1000000000) (-153646559 / 500000000) (Real.log (147087 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (174337267 / 1000000000) ≤ -Real.log (1000000 / 1190457) ∧
    -Real.log (1000000 / 1190457) ≤ (43584317 / 250000000) := by
  have h := checkLog_sound (w := (190457 / 2190457)) (n := 12)
    (lo := (174337267 / 1000000000)) (hi := (43584317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1190457 / 1000000) = 1/(1000000 / 1190457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (174337267 / 1000000000) (43584317 / 250000000) (Real.log (1190457 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1190457 / 1000000) = -Real.log (1000000 / 1190457) := by
    rw [show ((1190457 / 1000000) : ℝ) = ((1000000 / 1190457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52821347 / 250000000) ≤ -Real.log (809543 / 1000000) ∧
    -Real.log (809543 / 1000000) ≤ (211285389 / 1000000000) := by
  have h := checkLog_sound (w := (190457 / 1809543)) (n := 12)
    (lo := (52821347 / 250000000)) (hi := (211285389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 809543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 809543) = 1/(809543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-211285389 / 1000000000) (-52821347 / 250000000) (Real.log (809543 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34920703 / 200000000) ≤ -Real.log (500000 / 595387) ∧
    -Real.log (500000 / 595387) ≤ (43650879 / 250000000) := by
  have h := checkLog_sound (w := (95387 / 1095387)) (n := 12)
    (lo := (34920703 / 200000000)) (hi := (43650879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595387 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595387 / 500000) = 1/(500000 / 595387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34920703 / 200000000) (43650879 / 250000000) (Real.log (595387 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (595387 / 500000) = -Real.log (500000 / 595387) := by
    rw [show ((595387 / 500000) : ℝ) = ((500000 / 595387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (211677043 / 1000000000) ≤ -Real.log (404613 / 500000) ∧
    -Real.log (404613 / 500000) ≤ (52919261 / 250000000) := by
  have h := checkLog_sound (w := (95387 / 904613)) (n := 12)
    (lo := (211677043 / 1000000000)) (hi := (52919261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404613) = 1/(404613 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-52919261 / 250000000) (-211677043 / 1000000000) (Real.log (404613 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (155966981 / 200000000) ≤ -Real.log (250000000000 / 545278036657) ∧
    -Real.log (250000000000 / 545278036657) ≤ (779834907 / 1000000000) := by
  have h := checkLog_sound (w := (45278036657 / 1045278036657)) (n := 12)
    (lo := (3467509 / 40000000)) (hi := (43343863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545278036657 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(545278036657 / 500000000000) = 1/(250000000000 / 545278036657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (155966981 / 200000000) (779834907 / 1000000000) (Real.log (545278036657 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (545278036657 / 250000000000) = -Real.log (250000000000 / 545278036657) := by
    rw [show ((545278036657 / 250000000000) : ℝ) = ((250000000000 / 545278036657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (97649313 / 125000000) ≤ -Real.log (125000000000 / 273009950249) ∧
    -Real.log (125000000000 / 273009950249) ≤ (390597253 / 500000000) := by
  have h := checkLog_sound (w := (23009950249 / 523009950249)) (n := 12)
    (lo := (22011831 / 250000000)) (hi := (3521893 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273009950249 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(273009950249 / 250000000000) = 1/(125000000000 / 273009950249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (97649313 / 125000000) (390597253 / 500000000) (Real.log (273009950249 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (273009950249 / 125000000000) = -Real.log (125000000000 / 273009950249) := by
    rw [show ((273009950249 / 125000000000) : ℝ) = ((125000000000 / 273009950249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (270554797 / 500000000) ≤ -Real.log (100000000000 / 171791199129) ∧
    -Real.log (100000000000 / 171791199129) ≤ (108221919 / 200000000) := by
  have h := checkLog_sound (w := (71791199129 / 271791199129)) (n := 12)
    (lo := (270554797 / 500000000)) (hi := (108221919 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171791199129 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171791199129 / 100000000000) = 1/(100000000000 / 171791199129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (270554797 / 500000000) (108221919 / 200000000) (Real.log (171791199129 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (171791199129 / 100000000000) = -Real.log (100000000000 / 171791199129) := by
    rw [show ((171791199129 / 100000000000) : ℝ) = ((100000000000 / 171791199129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (542021307 / 1000000000) ≤ -Real.log (500000000000 / 859739473917) ∧
    -Real.log (500000000000 / 859739473917) ≤ (135505327 / 250000000) := by
  have h := checkLog_sound (w := (359739473917 / 1359739473917)) (n := 12)
    (lo := (542021307 / 1000000000)) (hi := (135505327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859739473917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859739473917 / 500000000000) = 1/(500000000000 / 859739473917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (542021307 / 1000000000) (135505327 / 250000000) (Real.log (859739473917 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (859739473917 / 500000000000) = -Real.log (500000000000 / 859739473917) := by
    rw [show ((859739473917 / 500000000000) : ℝ) = ((500000000000 / 859739473917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (77124531 / 200000000) ≤ -Real.log (125000000000 / 183816208651) ∧
    -Real.log (125000000000 / 183816208651) ≤ (3012677 / 7812500) := by
  have h := checkLog_sound (w := (58816208651 / 308816208651)) (n := 12)
    (lo := (77124531 / 200000000)) (hi := (3012677 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183816208651 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183816208651 / 125000000000) = 1/(125000000000 / 183816208651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (77124531 / 200000000) (3012677 / 7812500) (Real.log (183816208651 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (183816208651 / 125000000000) = -Real.log (125000000000 / 183816208651) := by
    rw [show ((183816208651 / 125000000000) : ℝ) = ((125000000000 / 183816208651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (386280559 / 1000000000) ≤ -Real.log (500000000000 / 735748727797) ∧
    -Real.log (500000000000 / 735748727797) ≤ (4828507 / 12500000) := by
  have h := checkLog_sound (w := (235748727797 / 1235748727797)) (n := 12)
    (lo := (386280559 / 1000000000)) (hi := (4828507 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735748727797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735748727797 / 500000000000) = 1/(500000000000 / 735748727797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (386280559 / 1000000000) (4828507 / 12500000) (Real.log (735748727797 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (735748727797 / 500000000000) = -Real.log (500000000000 / 735748727797) := by
    rw [show ((735748727797 / 500000000000) : ℝ) = ((500000000000 / 735748727797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (37073527 / 1000000000) ≤ -Real.log (240901320231 / 250000000000) ∧
    -Real.log (240901320231 / 250000000000) ≤ (4634191 / 125000000) := by
  have h := checkLog_sound (w := (9098679769 / 490901320231)) (n := 12)
    (lo := (37073527 / 1000000000)) (hi := (4634191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240901320231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240901320231) = 1/(240901320231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4634191 / 125000000) (-37073527 / 1000000000) (Real.log (240901320231 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (36948121 / 1000000000) ≤ -Real.log (963726131151 / 1000000000000) ∧
    -Real.log (963726131151 / 1000000000000) ≤ (18474061 / 500000000) := by
  have h := checkLog_sound (w := (36273868849 / 1963726131151)) (n := 12)
    (lo := (36948121 / 1000000000)) (hi := (18474061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963726131151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963726131151) = 1/(963726131151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18474061 / 500000000) (-36948121 / 1000000000) (Real.log (963726131151 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell207

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell208Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell208
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

theorem reflection_log_1_neg : (316605433 / 1000000000) ≤ -Real.log (5120 / 7027) ∧
    -Real.log (5120 / 7027) ≤ (158302717 / 500000000) := by
  have h := checkLog_sound (w := (1907 / 12147)) (n := 12)
    (lo := (316605433 / 1000000000)) (hi := (158302717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7027 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7027 / 5120) = 1/(5120 / 7027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (316605433 / 1000000000) (158302717 / 500000000) (Real.log (7027 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7027 / 5120) = -Real.log (5120 / 7027) := by
    rw [show ((7027 / 5120) : ℝ) = ((5120 / 7027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (232974679 / 500000000) ≤ -Real.log (3213 / 5120) ∧
    -Real.log (3213 / 5120) ≤ (465949359 / 1000000000) := by
  have h := checkLog_sound (w := (1907 / 8333)) (n := 12)
    (lo := (232974679 / 500000000)) (hi := (465949359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3213) = 1/(3213 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-465949359 / 1000000000) (-232974679 / 500000000) (Real.log (3213 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (316178417 / 1000000000) ≤ -Real.log (320 / 439) ∧
    -Real.log (320 / 439) ≤ (158089209 / 500000000) := by
  have h := checkLog_sound (w := (119 / 759)) (n := 12)
    (lo := (316178417 / 1000000000)) (hi := (158089209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(439 / 320) = 1/(320 / 439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (316178417 / 1000000000) (158089209 / 500000000) (Real.log (439 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (439 / 320) = -Real.log (320 / 439) := by
    rw [show ((439 / 320) : ℝ) = ((320 / 439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (465016087 / 1000000000) ≤ -Real.log (201 / 320) ∧
    -Real.log (201 / 320) ≤ (58127011 / 125000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 201) = 1/(201 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58127011 / 125000000) (-465016087 / 1000000000) (Real.log (201 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (117363699 / 500000000) ≤ -Real.log (250000 / 316141) ∧
    -Real.log (250000 / 316141) ≤ (234727399 / 1000000000) := by
  have h := checkLog_sound (w := (66141 / 566141)) (n := 12)
    (lo := (117363699 / 500000000)) (hi := (234727399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316141 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316141 / 250000) = 1/(250000 / 316141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (117363699 / 500000000) (234727399 / 1000000000) (Real.log (316141 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (316141 / 250000) = -Real.log (250000 / 316141) := by
    rw [show ((316141 / 250000) : ℝ) = ((250000 / 316141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (153645879 / 500000000) ≤ -Real.log (183859 / 250000) ∧
    -Real.log (183859 / 250000) ≤ (307291759 / 1000000000) := by
  have h := checkLog_sound (w := (66141 / 433859)) (n := 12)
    (lo := (153645879 / 500000000)) (hi := (307291759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183859) = 1/(183859 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-307291759 / 1000000000) (-153645879 / 500000000) (Real.log (183859 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47012369 / 200000000) ≤ -Real.log (1000000 / 1264987) ∧
    -Real.log (1000000 / 1264987) ≤ (117530923 / 500000000) := by
  have h := checkLog_sound (w := (264987 / 2264987)) (n := 12)
    (lo := (47012369 / 200000000)) (hi := (117530923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264987 / 1000000) = 1/(1000000 / 1264987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47012369 / 200000000) (117530923 / 500000000) (Real.log (1264987 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1264987 / 1000000) = -Real.log (1000000 / 1264987) := by
    rw [show ((1264987 / 1000000) : ℝ) = ((1000000 / 1264987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (76966773 / 250000000) ≤ -Real.log (735013 / 1000000) ∧
    -Real.log (735013 / 1000000) ≤ (307867093 / 1000000000) := by
  have h := checkLog_sound (w := (264987 / 1735013)) (n := 12)
    (lo := (76966773 / 250000000)) (hi := (307867093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735013) = 1/(735013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-307867093 / 1000000000) (-76966773 / 250000000) (Real.log (735013 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (43650669 / 250000000) ≤ -Real.log (1000000 / 1190773) ∧
    -Real.log (1000000 / 1190773) ≤ (174602677 / 1000000000) := by
  have h := checkLog_sound (w := (190773 / 2190773)) (n := 12)
    (lo := (43650669 / 250000000)) (hi := (174602677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1190773 / 1000000) = 1/(1000000 / 1190773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (43650669 / 250000000) (174602677 / 1000000000) (Real.log (1190773 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1190773 / 1000000) = -Real.log (1000000 / 1190773) := by
    rw [show ((1190773 / 1000000) : ℝ) = ((1000000 / 1190773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (211675807 / 1000000000) ≤ -Real.log (809227 / 1000000) ∧
    -Real.log (809227 / 1000000) ≤ (6614869 / 31250000) := by
  have h := checkLog_sound (w := (190773 / 1809227)) (n := 12)
    (lo := (211675807 / 1000000000)) (hi := (6614869 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 809227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 809227) = 1/(809227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-6614869 / 31250000) (-211675807 / 1000000000) (Real.log (809227 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (174869693 / 1000000000) ≤ -Real.log (1000000 / 1191091) ∧
    -Real.log (1000000 / 1191091) ≤ (87434847 / 500000000) := by
  have h := checkLog_sound (w := (191091 / 2191091)) (n := 12)
    (lo := (174869693 / 1000000000)) (hi := (87434847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191091 / 1000000) = 1/(1000000 / 1191091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (174869693 / 1000000000) (87434847 / 500000000) (Real.log (1191091 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1191091 / 1000000) = -Real.log (1000000 / 1191091) := by
    rw [show ((1191091 / 1000000) : ℝ) = ((1000000 / 1191091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53017213 / 250000000) ≤ -Real.log (808909 / 1000000) ∧
    -Real.log (808909 / 1000000) ≤ (212068853 / 1000000000) := by
  have h := checkLog_sound (w := (191091 / 1808909)) (n := 12)
    (lo := (53017213 / 250000000)) (hi := (212068853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808909) = 1/(808909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-212068853 / 1000000000) (-53017213 / 250000000) (Real.log (808909 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (97649313 / 125000000) ≤ -Real.log (100000000000 / 218407960199) ∧
    -Real.log (100000000000 / 218407960199) ≤ (390597253 / 500000000) := by
  have h := checkLog_sound (w := (18407960199 / 418407960199)) (n := 12)
    (lo := (22011831 / 250000000)) (hi := (3521893 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218407960199 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(218407960199 / 200000000000) = 1/(100000000000 / 218407960199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (97649313 / 125000000) (390597253 / 500000000) (Real.log (218407960199 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (218407960199 / 100000000000) = -Real.log (100000000000 / 218407960199) := by
    rw [show ((218407960199 / 100000000000) : ℝ) = ((100000000000 / 218407960199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (782554791 / 1000000000) ≤ -Real.log (500000000000 / 1093526299409) ∧
    -Real.log (500000000000 / 1093526299409) ≤ (782554793 / 1000000000) := by
  have h := checkLog_sound (w := (93526299409 / 2093526299409)) (n := 12)
    (lo := (89407611 / 1000000000)) (hi := (22351903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093526299409 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1093526299409 / 1000000000000) = 1/(500000000000 / 1093526299409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (782554791 / 1000000000) (782554793 / 1000000000) (Real.log (1093526299409 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1093526299409 / 500000000000) = -Real.log (500000000000 / 1093526299409) := by
    rw [show ((1093526299409 / 500000000000) : ℝ) = ((500000000000 / 1093526299409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (542019157 / 1000000000) ≤ -Real.log (500000000000 / 859737625027) ∧
    -Real.log (500000000000 / 859737625027) ≤ (271009579 / 500000000) := by
  have h := checkLog_sound (w := (359737625027 / 1359737625027)) (n := 12)
    (lo := (542019157 / 1000000000)) (hi := (271009579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859737625027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859737625027 / 500000000000) = 1/(500000000000 / 859737625027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (542019157 / 1000000000) (271009579 / 500000000) (Real.log (859737625027 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (859737625027 / 500000000000) = -Real.log (500000000000 / 859737625027) := by
    rw [show ((859737625027 / 500000000000) : ℝ) = ((500000000000 / 859737625027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (271464469 / 500000000) ≤ -Real.log (250000000000 / 430260077033) ∧
    -Real.log (250000000000 / 430260077033) ≤ (542928939 / 1000000000) := by
  have h := checkLog_sound (w := (180260077033 / 680260077033)) (n := 12)
    (lo := (271464469 / 500000000)) (hi := (542928939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((430260077033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(430260077033 / 250000000000) = 1/(250000000000 / 430260077033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (271464469 / 500000000) (542928939 / 1000000000) (Real.log (430260077033 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (430260077033 / 250000000000) = -Real.log (250000000000 / 430260077033) := by
    rw [show ((430260077033 / 250000000000) : ℝ) = ((250000000000 / 430260077033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (96569621 / 250000000) ≤ -Real.log (500000000000 / 735747200723) ∧
    -Real.log (500000000000 / 735747200723) ≤ (77255697 / 200000000) := by
  have h := checkLog_sound (w := (235747200723 / 1235747200723)) (n := 12)
    (lo := (96569621 / 250000000)) (hi := (77255697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735747200723 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735747200723 / 500000000000) = 1/(500000000000 / 735747200723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (96569621 / 250000000) (77255697 / 200000000) (Real.log (735747200723 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (735747200723 / 500000000000) = -Real.log (500000000000 / 735747200723) := by
    rw [show ((735747200723 / 500000000000) : ℝ) = ((500000000000 / 735747200723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (193469273 / 500000000) ≤ -Real.log (500000000000 / 736233000251) ∧
    -Real.log (500000000000 / 736233000251) ≤ (386938547 / 1000000000) := by
  have h := checkLog_sound (w := (236233000251 / 1236233000251)) (n := 12)
    (lo := (193469273 / 500000000)) (hi := (386938547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736233000251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736233000251 / 500000000000) = 1/(500000000000 / 736233000251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (193469273 / 500000000) (386938547 / 1000000000) (Real.log (736233000251 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (736233000251 / 500000000000) = -Real.log (500000000000 / 736233000251) := by
    rw [show ((736233000251 / 500000000000) : ℝ) = ((500000000000 / 736233000251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18599579 / 500000000) ≤ -Real.log (963484229719 / 1000000000000) ∧
    -Real.log (963484229719 / 1000000000000) ≤ (37199159 / 1000000000) := by
  have h := checkLog_sound (w := (36515770281 / 1963484229719)) (n := 12)
    (lo := (18599579 / 500000000)) (hi := (37199159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963484229719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963484229719) = 1/(963484229719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37199159 / 1000000000) (-18599579 / 500000000) (Real.log (963484229719 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37073131 / 1000000000) ≤ -Real.log (963605662471 / 1000000000000) ∧
    -Real.log (963605662471 / 1000000000000) ≤ (9268283 / 250000000) := by
  have h := checkLog_sound (w := (36394337529 / 1963605662471)) (n := 12)
    (lo := (37073131 / 1000000000)) (hi := (9268283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963605662471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963605662471) = 1/(963605662471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9268283 / 250000000) (-37073131 / 1000000000) (Real.log (963605662471 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell208

end


