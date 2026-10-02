-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell175Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell175Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:57:11.974766+00:00
-- url     : https://prove2.me/theorems/742610d3-67bf-4e1b-9cca-57d7045b0f4f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell175Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell176…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell175Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell176Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell177Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell178Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell179Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell180Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell181Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell175Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell176Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell177Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell178Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell179Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell180Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell181Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell175Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell176Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell177Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell178Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell179Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell180Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell181Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell175Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell176Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell177Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell178Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell179Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell180Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell181Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell175Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell175
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

theorem reflection_log_1_neg : (75604183 / 250000000) ≤ -Real.log (320 / 433) ∧
    -Real.log (320 / 433) ≤ (302416733 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 753)) (n := 12)
    (lo := (75604183 / 250000000)) (hi := (302416733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433 / 320) = 1/(320 / 433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (75604183 / 250000000) (302416733 / 1000000000) (Real.log (433 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (433 / 320) = -Real.log (320 / 433) := by
    rw [show ((433 / 320) : ℝ) = ((320 / 433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (217801101 / 500000000) ≤ -Real.log (207 / 320) ∧
    -Real.log (207 / 320) ≤ (435602203 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 207) = 1/(207 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-435602203 / 1000000000) (-217801101 / 500000000) (Real.log (207 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (301983613 / 1000000000) ≤ -Real.log (1024 / 1385) ∧
    -Real.log (1024 / 1385) ≤ (150991807 / 500000000) := by
  have h := checkLog_sound (w := (361 / 2409)) (n := 12)
    (lo := (301983613 / 1000000000)) (hi := (150991807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385 / 1024) = 1/(1024 / 1385) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (301983613 / 1000000000) (150991807 / 500000000) (Real.log (1385 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1385 / 1024) = -Real.log (1024 / 1385) := by
    rw [show ((1385 / 1024) : ℝ) = ((1024 / 1385) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86939363 / 200000000) ≤ -Real.log (663 / 1024) ∧
    -Real.log (663 / 1024) ≤ (27168551 / 62500000) := by
  have h := checkLog_sound (w := (361 / 1687)) (n := 12)
    (lo := (86939363 / 200000000)) (hi := (27168551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 663) = 1/(663 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-27168551 / 62500000) (-86939363 / 200000000) (Real.log (663 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (111829309 / 500000000) ≤ -Real.log (250000 / 312661) ∧
    -Real.log (250000 / 312661) ≤ (223658619 / 1000000000) := by
  have h := checkLog_sound (w := (62661 / 562661)) (n := 12)
    (lo := (111829309 / 500000000)) (hi := (223658619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312661 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312661 / 250000) = 1/(250000 / 312661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (111829309 / 500000000) (223658619 / 1000000000) (Real.log (312661 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (312661 / 250000) = -Real.log (250000 / 312661) := by
    rw [show ((312661 / 250000) : ℝ) = ((250000 / 312661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (288541107 / 1000000000) ≤ -Real.log (187339 / 250000) ∧
    -Real.log (187339 / 250000) ≤ (72135277 / 250000000) := by
  have h := checkLog_sound (w := (62661 / 437339)) (n := 12)
    (lo := (288541107 / 1000000000)) (hi := (72135277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187339) = 1/(187339 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-72135277 / 250000000) (-288541107 / 1000000000) (Real.log (187339 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (223996787 / 1000000000) ≤ -Real.log (1000000 / 1251067) ∧
    -Real.log (1000000 / 1251067) ≤ (55999197 / 250000000) := by
  have h := checkLog_sound (w := (251067 / 2251067)) (n := 12)
    (lo := (223996787 / 1000000000)) (hi := (55999197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251067 / 1000000) = 1/(1000000 / 1251067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (223996787 / 1000000000) (55999197 / 250000000) (Real.log (1251067 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1251067 / 1000000) = -Real.log (1000000 / 1251067) := by
    rw [show ((1251067 / 1000000) : ℝ) = ((1000000 / 1251067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (36138219 / 125000000) ≤ -Real.log (748933 / 1000000) ∧
    -Real.log (748933 / 1000000) ≤ (289105753 / 1000000000) := by
  have h := checkLog_sound (w := (251067 / 1748933)) (n := 12)
    (lo := (36138219 / 125000000)) (hi := (289105753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748933) = 1/(748933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-289105753 / 1000000000) (-36138219 / 125000000) (Real.log (748933 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33165759 / 200000000) ≤ -Real.log (1000000 / 1180371) ∧
    -Real.log (1000000 / 1180371) ≤ (41457199 / 250000000) := by
  have h := checkLog_sound (w := (180371 / 2180371)) (n := 12)
    (lo := (33165759 / 200000000)) (hi := (41457199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180371 / 1000000) = 1/(1000000 / 1180371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33165759 / 200000000) (41457199 / 250000000) (Real.log (1180371 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1180371 / 1000000) = -Real.log (1000000 / 1180371) := by
    rw [show ((1180371 / 1000000) : ℝ) = ((1000000 / 1180371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4972587 / 25000000) ≤ -Real.log (819629 / 1000000) ∧
    -Real.log (819629 / 1000000) ≤ (198903481 / 1000000000) := by
  have h := checkLog_sound (w := (180371 / 1819629)) (n := 12)
    (lo := (4972587 / 25000000)) (hi := (198903481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819629) = 1/(819629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-198903481 / 1000000000) (-4972587 / 25000000) (Real.log (819629 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (265753 / 1600000) ≤ -Real.log (500000 / 590343) ∧
    -Real.log (500000 / 590343) ≤ (83047813 / 500000000) := by
  have h := checkLog_sound (w := (90343 / 1090343)) (n := 12)
    (lo := (265753 / 1600000)) (hi := (83047813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590343 / 500000) = 1/(500000 / 590343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (265753 / 1600000) (83047813 / 500000000) (Real.log (590343 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (590343 / 500000) = -Real.log (500000 / 590343) := by
    rw [show ((590343 / 500000) : ℝ) = ((500000 / 590343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (99643937 / 500000000) ≤ -Real.log (409657 / 500000) ∧
    -Real.log (409657 / 500000) ≤ (1594303 / 8000000) := by
  have h := checkLog_sound (w := (90343 / 909657)) (n := 12)
    (lo := (99643937 / 500000000)) (hi := (1594303 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409657) = 1/(409657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1594303 / 8000000) (-99643937 / 500000000) (Real.log (409657 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (736680427 / 1000000000) ≤ -Real.log (100000000000 / 208898944193) ∧
    -Real.log (100000000000 / 208898944193) ≤ (736680429 / 1000000000) := by
  have h := checkLog_sound (w := (8898944193 / 408898944193)) (n := 12)
    (lo := (43533247 / 1000000000)) (hi := (680207 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208898944193 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(208898944193 / 200000000000) = 1/(100000000000 / 208898944193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (736680427 / 1000000000) (736680429 / 1000000000) (Real.log (208898944193 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (208898944193 / 100000000000) = -Real.log (100000000000 / 208898944193) := by
    rw [show ((208898944193 / 100000000000) : ℝ) = ((100000000000 / 208898944193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (369009467 / 500000000) ≤ -Real.log (500000000000 / 1045893719807) ∧
    -Real.log (500000000000 / 1045893719807) ≤ (92252367 / 125000000) := by
  have h := checkLog_sound (w := (45893719807 / 2045893719807)) (n := 12)
    (lo := (22435877 / 500000000)) (hi := (8974351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1045893719807 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1045893719807 / 1000000000000) = 1/(500000000000 / 1045893719807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (369009467 / 500000000) (92252367 / 125000000) (Real.log (1045893719807 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1045893719807 / 500000000000) = -Real.log (500000000000 / 1045893719807) := by
    rw [show ((1045893719807 / 500000000000) : ℝ) = ((500000000000 / 1045893719807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (256099863 / 500000000) ≤ -Real.log (100000000000 / 166895841229) ∧
    -Real.log (100000000000 / 166895841229) ≤ (512199727 / 1000000000) := by
  have h := checkLog_sound (w := (66895841229 / 266895841229)) (n := 12)
    (lo := (256099863 / 500000000)) (hi := (512199727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166895841229 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166895841229 / 100000000000) = 1/(100000000000 / 166895841229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (256099863 / 500000000) (512199727 / 1000000000) (Real.log (166895841229 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (166895841229 / 100000000000) = -Real.log (100000000000 / 166895841229) := by
    rw [show ((166895841229 / 100000000000) : ℝ) = ((100000000000 / 166895841229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (513102539 / 1000000000) ≤ -Real.log (125000000000 / 208808231177) ∧
    -Real.log (125000000000 / 208808231177) ≤ (25655127 / 50000000) := by
  have h := checkLog_sound (w := (83808231177 / 333808231177)) (n := 12)
    (lo := (513102539 / 1000000000)) (hi := (25655127 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208808231177 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(208808231177 / 125000000000) = 1/(125000000000 / 208808231177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (513102539 / 1000000000) (25655127 / 50000000) (Real.log (208808231177 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (208808231177 / 125000000000) = -Real.log (125000000000 / 208808231177) := by
    rw [show ((208808231177 / 125000000000) : ℝ) = ((125000000000 / 208808231177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14589291 / 40000000) ≤ -Real.log (250000000000 / 360032099889) ∧
    -Real.log (250000000000 / 360032099889) ≤ (91183069 / 250000000) := by
  have h := checkLog_sound (w := (110032099889 / 610032099889)) (n := 12)
    (lo := (14589291 / 40000000)) (hi := (91183069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360032099889 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360032099889 / 250000000000) = 1/(250000000000 / 360032099889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14589291 / 40000000) (91183069 / 250000000) (Real.log (360032099889 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (360032099889 / 250000000000) = -Real.log (250000000000 / 360032099889) := by
    rw [show ((360032099889 / 250000000000) : ℝ) = ((250000000000 / 360032099889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (365383499 / 1000000000) ≤ -Real.log (500000000000 / 720533275399) ∧
    -Real.log (500000000000 / 720533275399) ≤ (730767 / 2000000) := by
  have h := checkLog_sound (w := (220533275399 / 1220533275399)) (n := 12)
    (lo := (365383499 / 1000000000)) (hi := (730767 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720533275399 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720533275399 / 500000000000) = 1/(500000000000 / 720533275399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (365383499 / 1000000000) (730767 / 2000000) (Real.log (720533275399 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (720533275399 / 500000000000) = -Real.log (500000000000 / 720533275399) := by
    rw [show ((720533275399 / 500000000000) : ℝ) = ((500000000000 / 720533275399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4149031 / 125000000) ≤ -Real.log (241838142351 / 250000000000) ∧
    -Real.log (241838142351 / 250000000000) ≤ (33192249 / 1000000000) := by
  have h := checkLog_sound (w := (8161857649 / 491838142351)) (n := 12)
    (lo := (4149031 / 125000000)) (hi := (33192249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241838142351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241838142351) = 1/(241838142351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-33192249 / 1000000000) (-4149031 / 125000000) (Real.log (241838142351 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8268671 / 250000000) ≤ -Real.log (967466302359 / 1000000000000) ∧
    -Real.log (967466302359 / 1000000000000) ≤ (6614937 / 200000000) := by
  have h := checkLog_sound (w := (32533697641 / 1967466302359)) (n := 12)
    (lo := (8268671 / 250000000)) (hi := (6614937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967466302359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967466302359) = 1/(967466302359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6614937 / 200000000) (-8268671 / 250000000) (Real.log (967466302359 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell175

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell176Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell176
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

theorem reflection_log_1_neg : (302849663 / 1000000000) ≤ -Real.log (5120 / 6931) ∧
    -Real.log (5120 / 6931) ≤ (2366013 / 7812500) := by
  have h := checkLog_sound (w := (1811 / 12051)) (n := 12)
    (lo := (302849663 / 1000000000)) (hi := (2366013 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6931 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6931 / 5120) = 1/(5120 / 6931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (302849663 / 1000000000) (2366013 / 7812500) (Real.log (6931 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6931 / 5120) = -Real.log (5120 / 6931) := by
    rw [show ((6931 / 5120) : ℝ) = ((5120 / 6931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (43650841 / 100000000) ≤ -Real.log (3309 / 5120) ∧
    -Real.log (3309 / 5120) ≤ (436508411 / 1000000000) := by
  have h := checkLog_sound (w := (1811 / 8429)) (n := 12)
    (lo := (43650841 / 100000000)) (hi := (436508411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3309) = 1/(3309 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-436508411 / 1000000000) (-43650841 / 100000000) (Real.log (3309 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (75604183 / 250000000) ≤ -Real.log (320 / 433) ∧
    -Real.log (320 / 433) ≤ (302416733 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 753)) (n := 12)
    (lo := (75604183 / 250000000)) (hi := (302416733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433 / 320) = 1/(320 / 433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (75604183 / 250000000) (302416733 / 1000000000) (Real.log (433 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (433 / 320) = -Real.log (320 / 433) := by
    rw [show ((433 / 320) : ℝ) = ((320 / 433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (217801101 / 500000000) ≤ -Real.log (207 / 320) ∧
    -Real.log (207 / 320) ≤ (435602203 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 207) = 1/(207 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-435602203 / 1000000000) (-217801101 / 500000000) (Real.log (207 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (223995987 / 1000000000) ≤ -Real.log (500000 / 625533) ∧
    -Real.log (500000 / 625533) ≤ (55998997 / 250000000) := by
  have h := checkLog_sound (w := (125533 / 1125533)) (n := 12)
    (lo := (223995987 / 1000000000)) (hi := (55998997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625533 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625533 / 500000) = 1/(500000 / 625533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (223995987 / 1000000000) (55998997 / 250000000) (Real.log (625533 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (625533 / 500000) = -Real.log (500000 / 625533) := by
    rw [show ((625533 / 500000) : ℝ) = ((500000 / 625533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9034513 / 31250000) ≤ -Real.log (374467 / 500000) ∧
    -Real.log (374467 / 500000) ≤ (289104417 / 1000000000) := by
  have h := checkLog_sound (w := (125533 / 874467)) (n := 12)
    (lo := (9034513 / 31250000)) (hi := (289104417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 374467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 374467) = 1/(374467 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-289104417 / 1000000000) (-9034513 / 31250000) (Real.log (374467 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (224333243 / 1000000000) ≤ -Real.log (31250 / 39109) ∧
    -Real.log (31250 / 39109) ≤ (56083311 / 250000000) := by
  have h := checkLog_sound (w := (7859 / 70359)) (n := 12)
    (lo := (224333243 / 1000000000)) (hi := (56083311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39109 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39109 / 31250) = 1/(31250 / 39109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (224333243 / 1000000000) (56083311 / 250000000) (Real.log (39109 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (39109 / 31250) = -Real.log (31250 / 39109) := by
    rw [show ((39109 / 31250) : ℝ) = ((31250 / 39109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (289668043 / 1000000000) ≤ -Real.log (23391 / 31250) ∧
    -Real.log (23391 / 31250) ≤ (72417011 / 250000000) := by
  have h := checkLog_sound (w := (7859 / 54641)) (n := 12)
    (lo := (289668043 / 1000000000)) (hi := (72417011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23391) = 1/(23391 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-72417011 / 250000000) (-289668043 / 1000000000) (Real.log (23391 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (83047389 / 500000000) ≤ -Real.log (200000 / 236137) ∧
    -Real.log (200000 / 236137) ≤ (166094779 / 1000000000) := by
  have h := checkLog_sound (w := (36137 / 436137)) (n := 12)
    (lo := (83047389 / 500000000)) (hi := (166094779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236137 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236137 / 200000) = 1/(200000 / 236137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (83047389 / 500000000) (166094779 / 1000000000) (Real.log (236137 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (236137 / 200000) = -Real.log (200000 / 236137) := by
    rw [show ((236137 / 200000) : ℝ) = ((200000 / 236137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199286653 / 1000000000) ≤ -Real.log (163863 / 200000) ∧
    -Real.log (163863 / 200000) ≤ (99643327 / 500000000) := by
  have h := checkLog_sound (w := (36137 / 363863)) (n := 12)
    (lo := (199286653 / 1000000000)) (hi := (99643327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163863) = 1/(163863 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-99643327 / 500000000) (-199286653 / 1000000000) (Real.log (163863 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (166361537 / 1000000000) ≤ -Real.log (1000 / 1181) ∧
    -Real.log (1000 / 1181) ≤ (83180769 / 500000000) := by
  have h := checkLog_sound (w := (181 / 2181)) (n := 12)
    (lo := (166361537 / 1000000000)) (hi := (83180769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181 / 1000) = 1/(1000 / 1181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (166361537 / 1000000000) (83180769 / 500000000) (Real.log (1181 / 1000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1181 / 1000) = -Real.log (1000 / 1181) := by
    rw [show ((1181 / 1000) : ℝ) = ((1000 / 1181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (39934239 / 200000000) ≤ -Real.log (819 / 1000) ∧
    -Real.log (819 / 1000) ≤ (49917799 / 250000000) := by
  have h := checkLog_sound (w := (181 / 1819)) (n := 12)
    (lo := (39934239 / 200000000)) (hi := (49917799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 819) = 1/(819 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-49917799 / 250000000) (-39934239 / 200000000) (Real.log (819 / 1000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (369009467 / 500000000) ≤ -Real.log (250000000000 / 522946859903) ∧
    -Real.log (250000000000 / 522946859903) ≤ (92252367 / 125000000) := by
  have h := checkLog_sound (w := (22946859903 / 1022946859903)) (n := 12)
    (lo := (22435877 / 500000000)) (hi := (8974351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((522946859903 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(522946859903 / 500000000000) = 1/(250000000000 / 522946859903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (369009467 / 500000000) (92252367 / 125000000) (Real.log (522946859903 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (522946859903 / 250000000000) = -Real.log (250000000000 / 522946859903) := by
    rw [show ((522946859903 / 250000000000) : ℝ) = ((250000000000 / 522946859903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (739358073 / 1000000000) ≤ -Real.log (100000000000 / 209459051073) ∧
    -Real.log (100000000000 / 209459051073) ≤ (29574323 / 40000000) := by
  have h := checkLog_sound (w := (9459051073 / 409459051073)) (n := 12)
    (lo := (46210893 / 1000000000)) (hi := (23105447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209459051073 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209459051073 / 200000000000) = 1/(100000000000 / 209459051073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (739358073 / 1000000000) (29574323 / 40000000) (Real.log (209459051073 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (209459051073 / 100000000000) = -Real.log (100000000000 / 209459051073) := by
    rw [show ((209459051073 / 100000000000) : ℝ) = ((100000000000 / 209459051073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (128275101 / 250000000) ≤ -Real.log (250000000000 / 417615570931) ∧
    -Real.log (250000000000 / 417615570931) ≤ (102620081 / 200000000) := by
  have h := checkLog_sound (w := (167615570931 / 667615570931)) (n := 12)
    (lo := (128275101 / 250000000)) (hi := (102620081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417615570931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417615570931 / 250000000000) = 1/(250000000000 / 417615570931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (128275101 / 250000000) (102620081 / 200000000) (Real.log (417615570931 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (417615570931 / 250000000000) = -Real.log (250000000000 / 417615570931) := by
    rw [show ((417615570931 / 250000000000) : ℝ) = ((250000000000 / 417615570931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (257000643 / 500000000) ≤ -Real.log (250000000000 / 417991962721) ∧
    -Real.log (250000000000 / 417991962721) ≤ (514001287 / 1000000000) := by
  have h := checkLog_sound (w := (167991962721 / 667991962721)) (n := 12)
    (lo := (257000643 / 500000000)) (hi := (514001287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417991962721 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417991962721 / 250000000000) = 1/(250000000000 / 417991962721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (257000643 / 500000000) (514001287 / 1000000000) (Real.log (417991962721 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (417991962721 / 250000000000) = -Real.log (250000000000 / 417991962721) := by
    rw [show ((417991962721 / 250000000000) : ℝ) = ((250000000000 / 417991962721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (45672679 / 125000000) ≤ -Real.log (500000000000 / 720531785699) ∧
    -Real.log (500000000000 / 720531785699) ≤ (365381433 / 1000000000) := by
  have h := checkLog_sound (w := (220531785699 / 1220531785699)) (n := 12)
    (lo := (45672679 / 125000000)) (hi := (365381433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720531785699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720531785699 / 500000000000) = 1/(500000000000 / 720531785699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (45672679 / 125000000) (365381433 / 1000000000) (Real.log (720531785699 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (720531785699 / 500000000000) = -Real.log (500000000000 / 720531785699) := by
    rw [show ((720531785699 / 500000000000) : ℝ) = ((500000000000 / 720531785699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (91508183 / 250000000) ≤ -Real.log (250000000000 / 360500610501) ∧
    -Real.log (250000000000 / 360500610501) ≤ (366032733 / 1000000000) := by
  have h := checkLog_sound (w := (110500610501 / 610500610501)) (n := 12)
    (lo := (91508183 / 250000000)) (hi := (366032733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360500610501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360500610501 / 250000000000) = 1/(250000000000 / 360500610501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (91508183 / 250000000) (366032733 / 1000000000) (Real.log (360500610501 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (360500610501 / 250000000000) = -Real.log (250000000000 / 360500610501) := by
    rw [show ((360500610501 / 250000000000) : ℝ) = ((250000000000 / 360500610501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33309657 / 1000000000) ≤ -Real.log (967239 / 1000000) ∧
    -Real.log (967239 / 1000000) ≤ (16654829 / 500000000) := by
  have h := checkLog_sound (w := (32761 / 1967239)) (n := 12)
    (lo := (33309657 / 1000000000)) (hi := (16654829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 967239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 967239) = 1/(967239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16654829 / 500000000) (-33309657 / 1000000000) (Real.log (967239 / 1000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (53107 / 1600000) ≤ -Real.log (38694117231 / 40000000000) ∧
    -Real.log (38694117231 / 40000000000) ≤ (8297969 / 250000000) := by
  have h := checkLog_sound (w := (1305882769 / 78694117231)) (n := 12)
    (lo := (53107 / 1600000)) (hi := (8297969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38694117231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38694117231) = 1/(38694117231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8297969 / 250000000) (-53107 / 1600000) (Real.log (38694117231 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell176

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell177Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell177
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

theorem reflection_log_1_neg : (37910301 / 125000000) ≤ -Real.log (2560 / 3467) ∧
    -Real.log (2560 / 3467) ≤ (303282409 / 1000000000) := by
  have h := checkLog_sound (w := (907 / 6027)) (n := 12)
    (lo := (37910301 / 125000000)) (hi := (303282409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3467 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3467 / 2560) = 1/(2560 / 3467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37910301 / 125000000) (303282409 / 1000000000) (Real.log (3467 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3467 / 2560) = -Real.log (2560 / 3467) := by
    rw [show ((3467 / 2560) : ℝ) = ((2560 / 3467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (437415439 / 1000000000) ≤ -Real.log (1653 / 2560) ∧
    -Real.log (1653 / 2560) ≤ (5467693 / 12500000) := by
  have h := checkLog_sound (w := (907 / 4213)) (n := 12)
    (lo := (437415439 / 1000000000)) (hi := (5467693 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1653) = 1/(1653 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-5467693 / 12500000) (-437415439 / 1000000000) (Real.log (1653 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (302849663 / 1000000000) ≤ -Real.log (5120 / 6931) ∧
    -Real.log (5120 / 6931) ≤ (2366013 / 7812500) := by
  have h := checkLog_sound (w := (1811 / 12051)) (n := 12)
    (lo := (302849663 / 1000000000)) (hi := (2366013 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6931 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6931 / 5120) = 1/(5120 / 6931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (302849663 / 1000000000) (2366013 / 7812500) (Real.log (6931 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6931 / 5120) = -Real.log (5120 / 6931) := by
    rw [show ((6931 / 5120) : ℝ) = ((5120 / 6931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (43650841 / 100000000) ≤ -Real.log (3309 / 5120) ∧
    -Real.log (3309 / 5120) ≤ (436508411 / 1000000000) := by
  have h := checkLog_sound (w := (1811 / 8429)) (n := 12)
    (lo := (43650841 / 100000000)) (hi := (436508411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3309) = 1/(3309 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-436508411 / 1000000000) (-43650841 / 100000000) (Real.log (3309 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (56083111 / 250000000) ≤ -Real.log (1000000 / 1251487) ∧
    -Real.log (1000000 / 1251487) ≤ (44866489 / 200000000) := by
  have h := checkLog_sound (w := (251487 / 2251487)) (n := 12)
    (lo := (56083111 / 250000000)) (hi := (44866489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251487 / 1000000) = 1/(1000000 / 1251487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (56083111 / 250000000) (44866489 / 200000000) (Real.log (1251487 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1251487 / 1000000) = -Real.log (1000000 / 1251487) := by
    rw [show ((1251487 / 1000000) : ℝ) = ((1000000 / 1251487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (289666707 / 1000000000) ≤ -Real.log (748513 / 1000000) ∧
    -Real.log (748513 / 1000000) ≤ (72416677 / 250000000) := by
  have h := checkLog_sound (w := (251487 / 1748513)) (n := 12)
    (lo := (289666707 / 1000000000)) (hi := (72416677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748513) = 1/(748513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-72416677 / 250000000) (-289666707 / 1000000000) (Real.log (748513 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44934077 / 200000000) ≤ -Real.log (100000 / 125191) ∧
    -Real.log (100000 / 125191) ≤ (112335193 / 500000000) := by
  have h := checkLog_sound (w := (25191 / 225191)) (n := 12)
    (lo := (44934077 / 200000000)) (hi := (112335193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125191 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125191 / 100000) = 1/(100000 / 125191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44934077 / 200000000) (112335193 / 500000000) (Real.log (125191 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (125191 / 100000) = -Real.log (100000 / 125191) := by
    rw [show ((125191 / 100000) : ℝ) = ((100000 / 125191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (290231987 / 1000000000) ≤ -Real.log (74809 / 100000) ∧
    -Real.log (74809 / 100000) ≤ (72557997 / 250000000) := by
  have h := checkLog_sound (w := (25191 / 174809)) (n := 12)
    (lo := (290231987 / 1000000000)) (hi := (72557997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74809) = 1/(74809 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-72557997 / 250000000) (-290231987 / 1000000000) (Real.log (74809 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16636069 / 100000000) ≤ -Real.log (1000000 / 1180999) ∧
    -Real.log (1000000 / 1180999) ≤ (166360691 / 1000000000) := by
  have h := checkLog_sound (w := (180999 / 2180999)) (n := 12)
    (lo := (16636069 / 100000000)) (hi := (166360691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180999 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180999 / 1000000) = 1/(1000000 / 1180999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16636069 / 100000000) (166360691 / 1000000000) (Real.log (1180999 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1180999 / 1000000) = -Real.log (1000000 / 1180999) := by
    rw [show ((1180999 / 1000000) : ℝ) = ((1000000 / 1180999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (99834987 / 500000000) ≤ -Real.log (819001 / 1000000) ∧
    -Real.log (819001 / 1000000) ≤ (7986799 / 40000000) := by
  have h := checkLog_sound (w := (180999 / 1819001)) (n := 12)
    (lo := (99834987 / 500000000)) (hi := (7986799 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819001) = 1/(819001 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7986799 / 40000000) (-99834987 / 500000000) (Real.log (819001 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83313689 / 500000000) ≤ -Real.log (500000 / 590657) ∧
    -Real.log (500000 / 590657) ≤ (166627379 / 1000000000) := by
  have h := checkLog_sound (w := (90657 / 1090657)) (n := 12)
    (lo := (83313689 / 500000000)) (hi := (166627379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590657 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590657 / 500000) = 1/(500000 / 590657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83313689 / 500000000) (166627379 / 1000000000) (Real.log (590657 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (590657 / 500000) = -Real.log (500000 / 590657) := by
    rw [show ((590657 / 500000) : ℝ) = ((500000 / 590657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (200054663 / 1000000000) ≤ -Real.log (409343 / 500000) ∧
    -Real.log (409343 / 500000) ≤ (25006833 / 125000000) := by
  have h := checkLog_sound (w := (90657 / 909343)) (n := 12)
    (lo := (200054663 / 1000000000)) (hi := (25006833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409343) = 1/(409343 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-25006833 / 125000000) (-200054663 / 1000000000) (Real.log (409343 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (739358073 / 1000000000) ≤ -Real.log (125000000000 / 261823813841) ∧
    -Real.log (125000000000 / 261823813841) ≤ (29574323 / 40000000) := by
  have h := checkLog_sound (w := (11823813841 / 511823813841)) (n := 12)
    (lo := (46210893 / 1000000000)) (hi := (23105447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261823813841 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(261823813841 / 250000000000) = 1/(125000000000 / 261823813841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (739358073 / 1000000000) (29574323 / 40000000) (Real.log (261823813841 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (261823813841 / 125000000000) = -Real.log (125000000000 / 261823813841) := by
    rw [show ((261823813841 / 125000000000) : ℝ) = ((125000000000 / 261823813841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (740697847 / 1000000000) ≤ -Real.log (31250000000 / 65543708409) ∧
    -Real.log (31250000000 / 65543708409) ≤ (740697849 / 1000000000) := by
  have h := checkLog_sound (w := (3043708409 / 128043708409)) (n := 12)
    (lo := (47550667 / 1000000000)) (hi := (11887667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65543708409 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65543708409 / 62500000000) = 1/(31250000000 / 65543708409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (740697847 / 1000000000) (740697849 / 1000000000) (Real.log (65543708409 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (65543708409 / 31250000000) = -Real.log (31250000000 / 65543708409) := by
    rw [show ((65543708409 / 31250000000) : ℝ) = ((31250000000 / 65543708409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (513999151 / 1000000000) ≤ -Real.log (50000000000 / 83598214059) ∧
    -Real.log (50000000000 / 83598214059) ≤ (32124947 / 62500000) := by
  have h := checkLog_sound (w := (33598214059 / 133598214059)) (n := 12)
    (lo := (513999151 / 1000000000)) (hi := (32124947 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83598214059 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83598214059 / 50000000000) = 1/(50000000000 / 83598214059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (513999151 / 1000000000) (32124947 / 62500000) (Real.log (83598214059 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (83598214059 / 50000000000) = -Real.log (50000000000 / 83598214059) := by
    rw [show ((83598214059 / 50000000000) : ℝ) = ((50000000000 / 83598214059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (128725593 / 250000000) ≤ -Real.log (125000000000 / 209184389579) ∧
    -Real.log (125000000000 / 209184389579) ≤ (514902373 / 1000000000) := by
  have h := checkLog_sound (w := (84184389579 / 334184389579)) (n := 12)
    (lo := (128725593 / 250000000)) (hi := (514902373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209184389579 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(209184389579 / 125000000000) = 1/(125000000000 / 209184389579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (128725593 / 250000000) (514902373 / 1000000000) (Real.log (209184389579 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (209184389579 / 125000000000) = -Real.log (125000000000 / 209184389579) := by
    rw [show ((209184389579 / 125000000000) : ℝ) = ((125000000000 / 209184389579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (45753833 / 125000000) ≤ -Real.log (500000000000 / 720999730159) ∧
    -Real.log (500000000000 / 720999730159) ≤ (73206133 / 200000000) := by
  have h := checkLog_sound (w := (220999730159 / 1220999730159)) (n := 12)
    (lo := (45753833 / 125000000)) (hi := (73206133 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720999730159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720999730159 / 500000000000) = 1/(500000000000 / 720999730159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (45753833 / 125000000) (73206133 / 200000000) (Real.log (720999730159 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (720999730159 / 500000000000) = -Real.log (500000000000 / 720999730159) := by
    rw [show ((720999730159 / 500000000000) : ℝ) = ((500000000000 / 720999730159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (366682041 / 1000000000) ≤ -Real.log (500000000000 / 721469525557) ∧
    -Real.log (500000000000 / 721469525557) ≤ (183341021 / 500000000) := by
  have h := checkLog_sound (w := (221469525557 / 1221469525557)) (n := 12)
    (lo := (366682041 / 1000000000)) (hi := (183341021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721469525557 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721469525557 / 500000000000) = 1/(500000000000 / 721469525557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (366682041 / 1000000000) (183341021 / 500000000) (Real.log (721469525557 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (721469525557 / 500000000000) = -Real.log (500000000000 / 721469525557) := by
    rw [show ((721469525557 / 500000000000) : ℝ) = ((500000000000 / 721469525557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8356821 / 250000000) ≤ -Real.log (241781308351 / 250000000000) ∧
    -Real.log (241781308351 / 250000000000) ≤ (6685457 / 200000000) := by
  have h := checkLog_sound (w := (8218691649 / 491781308351)) (n := 12)
    (lo := (8356821 / 250000000)) (hi := (6685457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241781308351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241781308351) = 1/(241781308351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6685457 / 200000000) (-8356821 / 250000000) (Real.log (241781308351 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (33309283 / 1000000000) ≤ -Real.log (967239361999 / 1000000000000) ∧
    -Real.log (967239361999 / 1000000000000) ≤ (8327321 / 250000000) := by
  have h := checkLog_sound (w := (32760638001 / 1967239361999)) (n := 12)
    (lo := (33309283 / 1000000000)) (hi := (8327321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967239361999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967239361999) = 1/(967239361999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8327321 / 250000000) (-33309283 / 1000000000) (Real.log (967239361999 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell177

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell178Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell178
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

theorem reflection_log_1_neg : (60742993 / 200000000) ≤ -Real.log (5120 / 6937) ∧
    -Real.log (5120 / 6937) ≤ (151857483 / 500000000) := by
  have h := checkLog_sound (w := (1817 / 12057)) (n := 12)
    (lo := (60742993 / 200000000)) (hi := (151857483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6937 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6937 / 5120) = 1/(5120 / 6937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (60742993 / 200000000) (151857483 / 500000000) (Real.log (6937 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6937 / 5120) = -Real.log (5120 / 6937) := by
    rw [show ((6937 / 5120) : ℝ) = ((5120 / 6937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (109580823 / 250000000) ≤ -Real.log (3303 / 5120) ∧
    -Real.log (3303 / 5120) ≤ (438323293 / 1000000000) := by
  have h := checkLog_sound (w := (1817 / 8423)) (n := 12)
    (lo := (109580823 / 250000000)) (hi := (438323293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3303) = 1/(3303 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-438323293 / 1000000000) (-109580823 / 250000000) (Real.log (3303 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37910301 / 125000000) ≤ -Real.log (2560 / 3467) ∧
    -Real.log (2560 / 3467) ≤ (303282409 / 1000000000) := by
  have h := checkLog_sound (w := (907 / 6027)) (n := 12)
    (lo := (37910301 / 125000000)) (hi := (303282409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3467 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3467 / 2560) = 1/(2560 / 3467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37910301 / 125000000) (303282409 / 1000000000) (Real.log (3467 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3467 / 2560) = -Real.log (2560 / 3467) := by
    rw [show ((3467 / 2560) : ℝ) = ((2560 / 3467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (437415439 / 1000000000) ≤ -Real.log (1653 / 2560) ∧
    -Real.log (1653 / 2560) ≤ (5467693 / 12500000) := by
  have h := checkLog_sound (w := (907 / 4213)) (n := 12)
    (lo := (437415439 / 1000000000)) (hi := (5467693 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1653) = 1/(1653 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-5467693 / 12500000) (-437415439 / 1000000000) (Real.log (1653 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (224668787 / 1000000000) ≤ -Real.log (250000 / 312977) ∧
    -Real.log (250000 / 312977) ≤ (56167197 / 250000000) := by
  have h := checkLog_sound (w := (62977 / 562977)) (n := 12)
    (lo := (224668787 / 1000000000)) (hi := (56167197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312977 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312977 / 250000) = 1/(250000 / 312977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (224668787 / 1000000000) (56167197 / 250000000) (Real.log (312977 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (312977 / 250000) = -Real.log (250000 / 312977) := by
    rw [show ((312977 / 250000) : ℝ) = ((250000 / 312977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (290229313 / 1000000000) ≤ -Real.log (187023 / 250000) ∧
    -Real.log (187023 / 250000) ≤ (145114657 / 500000000) := by
  have h := checkLog_sound (w := (62977 / 437023)) (n := 12)
    (lo := (290229313 / 1000000000)) (hi := (145114657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187023) = 1/(187023 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-145114657 / 500000000) (-290229313 / 1000000000) (Real.log (187023 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (112503307 / 500000000) ≤ -Real.log (1000000 / 1252331) ∧
    -Real.log (1000000 / 1252331) ≤ (45001323 / 200000000) := by
  have h := checkLog_sound (w := (252331 / 2252331)) (n := 12)
    (lo := (112503307 / 500000000)) (hi := (45001323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252331 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252331 / 1000000) = 1/(1000000 / 1252331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (112503307 / 500000000) (45001323 / 200000000) (Real.log (1252331 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1252331 / 1000000) = -Real.log (1000000 / 1252331) := by
    rw [show ((1252331 / 1000000) : ℝ) = ((1000000 / 1252331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9087341 / 31250000) ≤ -Real.log (747669 / 1000000) ∧
    -Real.log (747669 / 1000000) ≤ (290794913 / 1000000000) := by
  have h := checkLog_sound (w := (252331 / 1747669)) (n := 12)
    (lo := (9087341 / 31250000)) (hi := (290794913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747669) = 1/(747669 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-290794913 / 1000000000) (-9087341 / 31250000) (Real.log (747669 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166626531 / 1000000000) ≤ -Real.log (1000000 / 1181313) ∧
    -Real.log (1000000 / 1181313) ≤ (41656633 / 250000000) := by
  have h := checkLog_sound (w := (181313 / 2181313)) (n := 12)
    (lo := (166626531 / 1000000000)) (hi := (41656633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181313 / 1000000) = 1/(1000000 / 1181313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166626531 / 1000000000) (41656633 / 250000000) (Real.log (1181313 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1181313 / 1000000) = -Real.log (1000000 / 1181313) := by
    rw [show ((1181313 / 1000000) : ℝ) = ((1000000 / 1181313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (200053441 / 1000000000) ≤ -Real.log (818687 / 1000000) ∧
    -Real.log (818687 / 1000000) ≤ (100026721 / 500000000) := by
  have h := checkLog_sound (w := (181313 / 1818687)) (n := 12)
    (lo := (200053441 / 1000000000)) (hi := (100026721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818687) = 1/(818687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-100026721 / 500000000) (-200053441 / 1000000000) (Real.log (818687 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83446997 / 500000000) ≤ -Real.log (1000000 / 1181629) ∧
    -Real.log (1000000 / 1181629) ≤ (33378799 / 200000000) := by
  have h := checkLog_sound (w := (181629 / 2181629)) (n := 12)
    (lo := (83446997 / 500000000)) (hi := (33378799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181629 / 1000000) = 1/(1000000 / 1181629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83446997 / 500000000) (33378799 / 200000000) (Real.log (1181629 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1181629 / 1000000) = -Real.log (1000000 / 1181629) := by
    rw [show ((1181629 / 1000000) : ℝ) = ((1000000 / 1181629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (200439499 / 1000000000) ≤ -Real.log (818371 / 1000000) ∧
    -Real.log (818371 / 1000000) ≤ (400879 / 2000000) := by
  have h := checkLog_sound (w := (181629 / 1818371)) (n := 12)
    (lo := (200439499 / 1000000000)) (hi := (400879 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818371) = 1/(818371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-400879 / 2000000) (-200439499 / 1000000000) (Real.log (818371 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (740697847 / 1000000000) ≤ -Real.log (500000000000 / 1048699334543) ∧
    -Real.log (500000000000 / 1048699334543) ≤ (740697849 / 1000000000) := by
  have h := checkLog_sound (w := (48699334543 / 2048699334543)) (n := 12)
    (lo := (47550667 / 1000000000)) (hi := (11887667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1048699334543 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1048699334543 / 1000000000000) = 1/(500000000000 / 1048699334543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (740697847 / 1000000000) (740697849 / 1000000000) (Real.log (1048699334543 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1048699334543 / 500000000000) = -Real.log (500000000000 / 1048699334543) := by
    rw [show ((1048699334543 / 500000000000) : ℝ) = ((500000000000 / 1048699334543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (742038257 / 1000000000) ≤ -Real.log (20000000000 / 42004238571) ∧
    -Real.log (20000000000 / 42004238571) ≤ (742038259 / 1000000000) := by
  have h := checkLog_sound (w := (2004238571 / 82004238571)) (n := 12)
    (lo := (48891077 / 1000000000)) (hi := (24445539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42004238571 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(42004238571 / 40000000000) = 1/(20000000000 / 42004238571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (742038257 / 1000000000) (742038259 / 1000000000) (Real.log (42004238571 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (42004238571 / 20000000000) = -Real.log (20000000000 / 42004238571) := by
    rw [show ((42004238571 / 20000000000) : ℝ) = ((20000000000 / 42004238571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (514898101 / 1000000000) ≤ -Real.log (50000000000 / 83673398459) ∧
    -Real.log (50000000000 / 83673398459) ≤ (257449051 / 500000000) := by
  have h := checkLog_sound (w := (33673398459 / 133673398459)) (n := 12)
    (lo := (514898101 / 1000000000)) (hi := (257449051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83673398459 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83673398459 / 50000000000) = 1/(50000000000 / 83673398459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (514898101 / 1000000000) (257449051 / 500000000) (Real.log (83673398459 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (83673398459 / 50000000000) = -Real.log (50000000000 / 83673398459) := by
    rw [show ((83673398459 / 50000000000) : ℝ) = ((50000000000 / 83673398459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (515801527 / 1000000000) ≤ -Real.log (6250000000 / 10468628163) ∧
    -Real.log (6250000000 / 10468628163) ≤ (64475191 / 125000000) := by
  have h := checkLog_sound (w := (4218628163 / 16718628163)) (n := 12)
    (lo := (515801527 / 1000000000)) (hi := (64475191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10468628163 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10468628163 / 6250000000) = 1/(6250000000 / 10468628163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (515801527 / 1000000000) (64475191 / 125000000) (Real.log (10468628163 / 6250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (10468628163 / 6250000000) = -Real.log (6250000000 / 10468628163) := by
    rw [show ((10468628163 / 6250000000) : ℝ) = ((6250000000 / 10468628163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (366679973 / 1000000000) ≤ -Real.log (50000000000 / 72146803357) ∧
    -Real.log (50000000000 / 72146803357) ≤ (183339987 / 500000000) := by
  have h := checkLog_sound (w := (22146803357 / 122146803357)) (n := 12)
    (lo := (366679973 / 1000000000)) (hi := (183339987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72146803357 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72146803357 / 50000000000) = 1/(50000000000 / 72146803357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (366679973 / 1000000000) (183339987 / 500000000) (Real.log (72146803357 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (72146803357 / 50000000000) = -Real.log (50000000000 / 72146803357) := by
    rw [show ((72146803357 / 50000000000) : ℝ) = ((50000000000 / 72146803357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (183666747 / 500000000) ≤ -Real.log (250000000000 / 360969841307) ∧
    -Real.log (250000000000 / 360969841307) ≤ (73466699 / 200000000) := by
  have h := checkLog_sound (w := (110969841307 / 610969841307)) (n := 12)
    (lo := (183666747 / 500000000)) (hi := (73466699 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360969841307 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360969841307 / 250000000000) = 1/(250000000000 / 360969841307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (183666747 / 500000000) (73466699 / 200000000) (Real.log (360969841307 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (360969841307 / 250000000000) = -Real.log (250000000000 / 360969841307) := by
    rw [show ((360969841307 / 250000000000) : ℝ) = ((250000000000 / 360969841307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6709101 / 200000000) ≤ -Real.log (967010906359 / 1000000000000) ∧
    -Real.log (967010906359 / 1000000000000) ≤ (16772753 / 500000000) := by
  have h := checkLog_sound (w := (32989093641 / 1967010906359)) (n := 12)
    (lo := (6709101 / 200000000)) (hi := (16772753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967010906359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967010906359) = 1/(967010906359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16772753 / 500000000) (-6709101 / 200000000) (Real.log (967010906359 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (33426909 / 1000000000) ≤ -Real.log (967125596031 / 1000000000000) ∧
    -Real.log (967125596031 / 1000000000000) ≤ (3342691 / 100000000) := by
  have h := checkLog_sound (w := (32874403969 / 1967125596031)) (n := 12)
    (lo := (33426909 / 1000000000)) (hi := (3342691 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967125596031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967125596031) = 1/(967125596031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3342691 / 100000000) (-33426909 / 1000000000) (Real.log (967125596031 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell178

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell179Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell179
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

theorem reflection_log_1_neg : (60829467 / 200000000) ≤ -Real.log (256 / 347) ∧
    -Real.log (256 / 347) ≤ (38018417 / 125000000) := by
  have h := checkLog_sound (w := (91 / 603)) (n := 12)
    (lo := (60829467 / 200000000)) (hi := (38018417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347 / 256) = 1/(256 / 347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (60829467 / 200000000) (38018417 / 125000000) (Real.log (347 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (347 / 256) = -Real.log (256 / 347) := by
    rw [show ((347 / 256) : ℝ) = ((256 / 347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (43923197 / 100000000) ≤ -Real.log (165 / 256) ∧
    -Real.log (165 / 256) ≤ (439231971 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 421)) (n := 12)
    (lo := (43923197 / 100000000)) (hi := (439231971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 165) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 165) = 1/(165 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-439231971 / 1000000000) (-43923197 / 100000000) (Real.log (165 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (60742993 / 200000000) ≤ -Real.log (5120 / 6937) ∧
    -Real.log (5120 / 6937) ≤ (151857483 / 500000000) := by
  have h := checkLog_sound (w := (1817 / 12057)) (n := 12)
    (lo := (60742993 / 200000000)) (hi := (151857483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6937 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6937 / 5120) = 1/(5120 / 6937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (60742993 / 200000000) (151857483 / 500000000) (Real.log (6937 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6937 / 5120) = -Real.log (5120 / 6937) := by
    rw [show ((6937 / 5120) : ℝ) = ((5120 / 6937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (109580823 / 250000000) ≤ -Real.log (3303 / 5120) ∧
    -Real.log (3303 / 5120) ≤ (438323293 / 1000000000) := by
  have h := checkLog_sound (w := (1817 / 8423)) (n := 12)
    (lo := (109580823 / 250000000)) (hi := (438323293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3303) = 1/(3303 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-438323293 / 1000000000) (-109580823 / 250000000) (Real.log (3303 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (28125727 / 125000000) ≤ -Real.log (100000 / 125233) ∧
    -Real.log (100000 / 125233) ≤ (225005817 / 1000000000) := by
  have h := checkLog_sound (w := (25233 / 225233)) (n := 12)
    (lo := (28125727 / 125000000)) (hi := (225005817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125233 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125233 / 100000) = 1/(100000 / 125233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (28125727 / 125000000) (225005817 / 1000000000) (Real.log (125233 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (125233 / 100000) = -Real.log (100000 / 125233) := by
    rw [show ((125233 / 100000) : ℝ) = ((100000 / 125233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (145396787 / 500000000) ≤ -Real.log (74767 / 100000) ∧
    -Real.log (74767 / 100000) ≤ (11631743 / 40000000) := by
  have h := checkLog_sound (w := (25233 / 174767)) (n := 12)
    (lo := (145396787 / 500000000)) (hi := (11631743 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74767) = 1/(74767 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11631743 / 40000000) (-145396787 / 500000000) (Real.log (74767 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (225342731 / 1000000000) ≤ -Real.log (62500 / 78297) ∧
    -Real.log (62500 / 78297) ≤ (56335683 / 250000000) := by
  have h := checkLog_sound (w := (15797 / 140797)) (n := 12)
    (lo := (225342731 / 1000000000)) (hi := (56335683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78297 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78297 / 62500) = 1/(62500 / 78297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (225342731 / 1000000000) (56335683 / 250000000) (Real.log (78297 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (78297 / 62500) = -Real.log (62500 / 78297) := by
    rw [show ((78297 / 62500) : ℝ) = ((62500 / 78297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (145679077 / 500000000) ≤ -Real.log (46703 / 62500) ∧
    -Real.log (46703 / 62500) ≤ (58271631 / 200000000) := by
  have h := checkLog_sound (w := (15797 / 109203)) (n := 12)
    (lo := (145679077 / 500000000)) (hi := (58271631 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46703) = 1/(46703 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-58271631 / 200000000) (-145679077 / 500000000) (Real.log (46703 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (41723287 / 250000000) ≤ -Real.log (250000 / 295407) ∧
    -Real.log (250000 / 295407) ≤ (166893149 / 1000000000) := by
  have h := checkLog_sound (w := (45407 / 545407)) (n := 12)
    (lo := (41723287 / 250000000)) (hi := (166893149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295407 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295407 / 250000) = 1/(250000 / 295407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (41723287 / 250000000) (166893149 / 1000000000) (Real.log (295407 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (295407 / 250000) = -Real.log (250000 / 295407) := by
    rw [show ((295407 / 250000) : ℝ) = ((250000 / 295407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (100219139 / 500000000) ≤ -Real.log (204593 / 250000) ∧
    -Real.log (204593 / 250000) ≤ (200438279 / 1000000000) := by
  have h := checkLog_sound (w := (45407 / 454593)) (n := 12)
    (lo := (100219139 / 500000000)) (hi := (200438279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204593) = 1/(204593 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-200438279 / 1000000000) (-100219139 / 500000000) (Real.log (204593 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83579847 / 500000000) ≤ -Real.log (1000000 / 1181943) ∧
    -Real.log (1000000 / 1181943) ≤ (33431939 / 200000000) := by
  have h := checkLog_sound (w := (181943 / 2181943)) (n := 12)
    (lo := (83579847 / 500000000)) (hi := (33431939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181943 / 1000000) = 1/(1000000 / 1181943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83579847 / 500000000) (33431939 / 200000000) (Real.log (1181943 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1181943 / 1000000) = -Real.log (1000000 / 1181943) := by
    rw [show ((1181943 / 1000000) : ℝ) = ((1000000 / 1181943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (100411631 / 500000000) ≤ -Real.log (818057 / 1000000) ∧
    -Real.log (818057 / 1000000) ≤ (200823263 / 1000000000) := by
  have h := checkLog_sound (w := (181943 / 1818057)) (n := 12)
    (lo := (100411631 / 500000000)) (hi := (200823263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818057) = 1/(818057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-200823263 / 1000000000) (-100411631 / 500000000) (Real.log (818057 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (742038257 / 1000000000) ≤ -Real.log (250000000000 / 525052982137) ∧
    -Real.log (250000000000 / 525052982137) ≤ (742038259 / 1000000000) := by
  have h := checkLog_sound (w := (25052982137 / 1025052982137)) (n := 12)
    (lo := (48891077 / 1000000000)) (hi := (24445539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((525052982137 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(525052982137 / 500000000000) = 1/(250000000000 / 525052982137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (742038257 / 1000000000) (742038259 / 1000000000) (Real.log (525052982137 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (525052982137 / 250000000000) = -Real.log (250000000000 / 525052982137) := by
    rw [show ((525052982137 / 250000000000) : ℝ) = ((250000000000 / 525052982137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (148675861 / 200000000) ≤ -Real.log (125000000000 / 262878787879) ∧
    -Real.log (125000000000 / 262878787879) ≤ (743379307 / 1000000000) := by
  have h := checkLog_sound (w := (12878787879 / 512878787879)) (n := 12)
    (lo := (401857 / 8000000)) (hi := (25116063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262878787879 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(262878787879 / 250000000000) = 1/(125000000000 / 262878787879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (148675861 / 200000000) (743379307 / 1000000000) (Real.log (262878787879 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (262878787879 / 125000000000) = -Real.log (125000000000 / 262878787879) := by
    rw [show ((262878787879 / 125000000000) : ℝ) = ((125000000000 / 262878787879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (515799391 / 1000000000) ≤ -Real.log (500000000000 / 837488464161) ∧
    -Real.log (500000000000 / 837488464161) ≤ (16118731 / 31250000) := by
  have h := checkLog_sound (w := (337488464161 / 1337488464161)) (n := 12)
    (lo := (515799391 / 1000000000)) (hi := (16118731 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837488464161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837488464161 / 500000000000) = 1/(500000000000 / 837488464161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (515799391 / 1000000000) (16118731 / 31250000) (Real.log (837488464161 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (837488464161 / 500000000000) = -Real.log (500000000000 / 837488464161) := by
    rw [show ((837488464161 / 500000000000) : ℝ) = ((500000000000 / 837488464161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103340177 / 200000000) ≤ -Real.log (250000000000 / 419121897951) ∧
    -Real.log (250000000000 / 419121897951) ≤ (258350443 / 500000000) := by
  have h := checkLog_sound (w := (169121897951 / 669121897951)) (n := 12)
    (lo := (103340177 / 200000000)) (hi := (258350443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419121897951 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419121897951 / 250000000000) = 1/(250000000000 / 419121897951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (103340177 / 200000000) (258350443 / 500000000) (Real.log (419121897951 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (419121897951 / 250000000000) = -Real.log (250000000000 / 419121897951) := by
    rw [show ((419121897951 / 250000000000) : ℝ) = ((250000000000 / 419121897951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (183665713 / 500000000) ≤ -Real.log (250000000000 / 360969094739) ∧
    -Real.log (250000000000 / 360969094739) ≤ (367331427 / 1000000000) := by
  have h := checkLog_sound (w := (110969094739 / 610969094739)) (n := 12)
    (lo := (183665713 / 500000000)) (hi := (367331427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360969094739 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360969094739 / 250000000000) = 1/(250000000000 / 360969094739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (183665713 / 500000000) (367331427 / 1000000000) (Real.log (360969094739 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (360969094739 / 250000000000) = -Real.log (250000000000 / 360969094739) := by
    rw [show ((360969094739 / 250000000000) : ℝ) = ((250000000000 / 360969094739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (367982957 / 1000000000) ≤ -Real.log (250000000000 / 361204353731) ∧
    -Real.log (250000000000 / 361204353731) ≤ (183991479 / 500000000) := by
  have h := checkLog_sound (w := (111204353731 / 611204353731)) (n := 12)
    (lo := (367982957 / 1000000000)) (hi := (183991479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361204353731 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361204353731 / 250000000000) = 1/(250000000000 / 361204353731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (367982957 / 1000000000) (183991479 / 500000000) (Real.log (361204353731 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (361204353731 / 250000000000) = -Real.log (250000000000 / 361204353731) := by
    rw [show ((361204353731 / 250000000000) : ℝ) = ((250000000000 / 361204353731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2103973 / 62500000) ≤ -Real.log (966896744751 / 1000000000000) ∧
    -Real.log (966896744751 / 1000000000000) ≤ (33663569 / 1000000000) := by
  have h := checkLog_sound (w := (33103255249 / 1966896744751)) (n := 12)
    (lo := (2103973 / 62500000)) (hi := (33663569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966896744751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966896744751) = 1/(966896744751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-33663569 / 1000000000) (-2103973 / 62500000) (Real.log (966896744751 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (33545129 / 1000000000) ≤ -Real.log (60438204351 / 62500000000) ∧
    -Real.log (60438204351 / 62500000000) ≤ (3354513 / 100000000) := by
  have h := checkLog_sound (w := (2061795649 / 122938204351)) (n := 12)
    (lo := (33545129 / 1000000000)) (hi := (3354513 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60438204351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60438204351) = 1/(60438204351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3354513 / 100000000) (-33545129 / 1000000000) (Real.log (60438204351 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell179

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell180Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell180
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

theorem reflection_log_1_neg : (152289759 / 500000000) ≤ -Real.log (5120 / 6943) ∧
    -Real.log (5120 / 6943) ≤ (304579519 / 1000000000) := by
  have h := checkLog_sound (w := (1823 / 12063)) (n := 12)
    (lo := (152289759 / 500000000)) (hi := (304579519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6943 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6943 / 5120) = 1/(5120 / 6943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (152289759 / 500000000) (304579519 / 1000000000) (Real.log (6943 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6943 / 5120) = -Real.log (5120 / 6943) := by
    rw [show ((6943 / 5120) : ℝ) = ((5120 / 6943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (220070737 / 500000000) ≤ -Real.log (3297 / 5120) ∧
    -Real.log (3297 / 5120) ≤ (17605659 / 40000000) := by
  have h := checkLog_sound (w := (1823 / 8417)) (n := 12)
    (lo := (220070737 / 500000000)) (hi := (17605659 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3297) = 1/(3297 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-17605659 / 40000000) (-220070737 / 500000000) (Real.log (3297 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (60829467 / 200000000) ≤ -Real.log (256 / 347) ∧
    -Real.log (256 / 347) ≤ (38018417 / 125000000) := by
  have h := checkLog_sound (w := (91 / 603)) (n := 12)
    (lo := (60829467 / 200000000)) (hi := (38018417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347 / 256) = 1/(256 / 347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (60829467 / 200000000) (38018417 / 125000000) (Real.log (347 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (347 / 256) = -Real.log (256 / 347) := by
    rw [show ((347 / 256) : ℝ) = ((256 / 347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (43923197 / 100000000) ≤ -Real.log (165 / 256) ∧
    -Real.log (165 / 256) ≤ (439231971 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 421)) (n := 12)
    (lo := (43923197 / 100000000)) (hi := (439231971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 165) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 165) = 1/(165 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-439231971 / 1000000000) (-43923197 / 100000000) (Real.log (165 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (225341933 / 1000000000) ≤ -Real.log (1000000 / 1252751) ∧
    -Real.log (1000000 / 1252751) ≤ (112670967 / 500000000) := by
  have h := checkLog_sound (w := (252751 / 2252751)) (n := 12)
    (lo := (225341933 / 1000000000)) (hi := (112670967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252751 / 1000000) = 1/(1000000 / 1252751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (225341933 / 1000000000) (112670967 / 500000000) (Real.log (1252751 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1252751 / 1000000) = -Real.log (1000000 / 1252751) := by
    rw [show ((1252751 / 1000000) : ℝ) = ((1000000 / 1252751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (18209801 / 62500000) ≤ -Real.log (747249 / 1000000) ∧
    -Real.log (747249 / 1000000) ≤ (291356817 / 1000000000) := by
  have h := checkLog_sound (w := (252751 / 1747249)) (n := 12)
    (lo := (18209801 / 62500000)) (hi := (291356817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747249) = 1/(747249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-291356817 / 1000000000) (-18209801 / 62500000) (Real.log (747249 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (56419883 / 250000000) ≤ -Real.log (500000 / 626587) ∧
    -Real.log (500000 / 626587) ≤ (225679533 / 1000000000) := by
  have h := checkLog_sound (w := (126587 / 1126587)) (n := 12)
    (lo := (56419883 / 250000000)) (hi := (225679533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626587 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626587 / 500000) = 1/(500000 / 626587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (56419883 / 250000000) (225679533 / 1000000000) (Real.log (626587 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (626587 / 500000) = -Real.log (500000 / 626587) := by
    rw [show ((626587 / 500000) : ℝ) = ((500000 / 626587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (72980763 / 250000000) ≤ -Real.log (373413 / 500000) ∧
    -Real.log (373413 / 500000) ≤ (291923053 / 1000000000) := by
  have h := checkLog_sound (w := (126587 / 873413)) (n := 12)
    (lo := (72980763 / 250000000)) (hi := (291923053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373413) = 1/(373413 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-291923053 / 1000000000) (-72980763 / 250000000) (Real.log (373413 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2611857 / 15625000) ≤ -Real.log (500000 / 590971) ∧
    -Real.log (500000 / 590971) ≤ (167158849 / 1000000000) := by
  have h := checkLog_sound (w := (90971 / 1090971)) (n := 12)
    (lo := (2611857 / 15625000)) (hi := (167158849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590971 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590971 / 500000) = 1/(500000 / 590971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2611857 / 15625000) (167158849 / 1000000000) (Real.log (590971 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (590971 / 500000) = -Real.log (500000 / 590971) := by
    rw [show ((590971 / 500000) : ℝ) = ((500000 / 590971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (5020551 / 25000000) ≤ -Real.log (409029 / 500000) ∧
    -Real.log (409029 / 500000) ≤ (200822041 / 1000000000) := by
  have h := checkLog_sound (w := (90971 / 909029)) (n := 12)
    (lo := (5020551 / 25000000)) (hi := (200822041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409029) = 1/(409029 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-200822041 / 1000000000) (-5020551 / 25000000) (Real.log (409029 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167425323 / 1000000000) ≤ -Real.log (1000000 / 1182257) ∧
    -Real.log (1000000 / 1182257) ≤ (41856331 / 250000000) := by
  have h := checkLog_sound (w := (182257 / 2182257)) (n := 12)
    (lo := (167425323 / 1000000000)) (hi := (41856331 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182257 / 1000000) = 1/(1000000 / 1182257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167425323 / 1000000000) (41856331 / 250000000) (Real.log (1182257 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1182257 / 1000000) = -Real.log (1000000 / 1182257) := by
    rw [show ((1182257 / 1000000) : ℝ) = ((1000000 / 1182257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (50301793 / 250000000) ≤ -Real.log (817743 / 1000000) ∧
    -Real.log (817743 / 1000000) ≤ (201207173 / 1000000000) := by
  have h := checkLog_sound (w := (182257 / 1817743)) (n := 12)
    (lo := (50301793 / 250000000)) (hi := (201207173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817743) = 1/(817743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-201207173 / 1000000000) (-50301793 / 250000000) (Real.log (817743 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (148675861 / 200000000) ≤ -Real.log (100000000000 / 210303030303) ∧
    -Real.log (100000000000 / 210303030303) ≤ (743379307 / 1000000000) := by
  have h := checkLog_sound (w := (10303030303 / 410303030303)) (n := 12)
    (lo := (401857 / 8000000)) (hi := (25116063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210303030303 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210303030303 / 200000000000) = 1/(100000000000 / 210303030303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (148675861 / 200000000) (743379307 / 1000000000) (Real.log (210303030303 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (210303030303 / 100000000000) = -Real.log (100000000000 / 210303030303) := by
    rw [show ((210303030303 / 100000000000) : ℝ) = ((100000000000 / 210303030303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (744720993 / 1000000000) ≤ -Real.log (250000000000 / 526463451623) ∧
    -Real.log (250000000000 / 526463451623) ≤ (148944199 / 200000000) := by
  have h := checkLog_sound (w := (26463451623 / 1026463451623)) (n := 12)
    (lo := (51573813 / 1000000000)) (hi := (25786907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((526463451623 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(526463451623 / 500000000000) = 1/(250000000000 / 526463451623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (744720993 / 1000000000) (148944199 / 200000000) (Real.log (526463451623 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (526463451623 / 250000000000) = -Real.log (250000000000 / 526463451623) := by
    rw [show ((526463451623 / 250000000000) : ℝ) = ((250000000000 / 526463451623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (516698749 / 1000000000) ≤ -Real.log (500000000000 / 838242005007) ∧
    -Real.log (500000000000 / 838242005007) ≤ (413359 / 800000) := by
  have h := checkLog_sound (w := (338242005007 / 1338242005007)) (n := 12)
    (lo := (516698749 / 1000000000)) (hi := (413359 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838242005007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838242005007 / 500000000000) = 1/(500000000000 / 838242005007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (516698749 / 1000000000) (413359 / 800000) (Real.log (838242005007 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (838242005007 / 500000000000) = -Real.log (500000000000 / 838242005007) := by
    rw [show ((838242005007 / 500000000000) : ℝ) = ((500000000000 / 838242005007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103520517 / 200000000) ≤ -Real.log (100000000000 / 167799996251) ∧
    -Real.log (100000000000 / 167799996251) ≤ (258801293 / 500000000) := by
  have h := checkLog_sound (w := (67799996251 / 267799996251)) (n := 12)
    (lo := (103520517 / 200000000)) (hi := (258801293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167799996251 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167799996251 / 100000000000) = 1/(100000000000 / 167799996251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (103520517 / 200000000) (258801293 / 500000000) (Real.log (167799996251 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (167799996251 / 100000000000) = -Real.log (100000000000 / 167799996251) := by
    rw [show ((167799996251 / 100000000000) : ℝ) = ((100000000000 / 167799996251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (45997611 / 125000000) ≤ -Real.log (25000000000 / 36120360659) ∧
    -Real.log (25000000000 / 36120360659) ≤ (367980889 / 1000000000) := by
  have h := checkLog_sound (w := (11120360659 / 61120360659)) (n := 12)
    (lo := (45997611 / 125000000)) (hi := (367980889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36120360659 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36120360659 / 25000000000) = 1/(25000000000 / 36120360659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (45997611 / 125000000) (367980889 / 1000000000) (Real.log (36120360659 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (36120360659 / 25000000000) = -Real.log (25000000000 / 36120360659) := by
    rw [show ((36120360659 / 25000000000) : ℝ) = ((25000000000 / 36120360659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (23039531 / 62500000) ≤ -Real.log (250000000000 / 361439046253) ∧
    -Real.log (250000000000 / 361439046253) ≤ (368632497 / 1000000000) := by
  have h := checkLog_sound (w := (111439046253 / 611439046253)) (n := 12)
    (lo := (23039531 / 62500000)) (hi := (368632497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361439046253 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361439046253 / 250000000000) = 1/(250000000000 / 361439046253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (23039531 / 62500000) (368632497 / 1000000000) (Real.log (361439046253 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (361439046253 / 250000000000) = -Real.log (250000000000 / 361439046253) := by
    rw [show ((361439046253 / 250000000000) : ℝ) = ((250000000000 / 361439046253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33781849 / 1000000000) ≤ -Real.log (966782385951 / 1000000000000) ∧
    -Real.log (966782385951 / 1000000000000) ≤ (675637 / 20000000) := by
  have h := checkLog_sound (w := (33217614049 / 1966782385951)) (n := 12)
    (lo := (33781849 / 1000000000)) (hi := (675637 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966782385951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966782385951) = 1/(966782385951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-675637 / 20000000) (-33781849 / 1000000000) (Real.log (966782385951 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (33663191 / 1000000000) ≤ -Real.log (241724277159 / 250000000000) ∧
    -Real.log (241724277159 / 250000000000) ≤ (4207899 / 125000000) := by
  have h := checkLog_sound (w := (8275722841 / 491724277159)) (n := 12)
    (lo := (33663191 / 1000000000)) (hi := (4207899 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241724277159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241724277159) = 1/(241724277159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4207899 / 125000000) (-33663191 / 1000000000) (Real.log (241724277159 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell180

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell181Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell181
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

theorem reflection_log_1_neg : (61002303 / 200000000) ≤ -Real.log (2560 / 3473) ∧
    -Real.log (2560 / 3473) ≤ (76252879 / 250000000) := by
  have h := checkLog_sound (w := (913 / 6033)) (n := 12)
    (lo := (61002303 / 200000000)) (hi := (76252879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3473 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3473 / 2560) = 1/(2560 / 3473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (61002303 / 200000000) (76252879 / 250000000) (Real.log (3473 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3473 / 2560) = -Real.log (2560 / 3473) := by
    rw [show ((3473 / 2560) : ℝ) = ((2560 / 3473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (441051807 / 1000000000) ≤ -Real.log (1647 / 2560) ∧
    -Real.log (1647 / 2560) ≤ (13782869 / 31250000) := by
  have h := checkLog_sound (w := (913 / 4207)) (n := 12)
    (lo := (441051807 / 1000000000)) (hi := (13782869 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1647) = 1/(1647 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-13782869 / 31250000) (-441051807 / 1000000000) (Real.log (1647 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (152289759 / 500000000) ≤ -Real.log (5120 / 6943) ∧
    -Real.log (5120 / 6943) ≤ (304579519 / 1000000000) := by
  have h := checkLog_sound (w := (1823 / 12063)) (n := 12)
    (lo := (152289759 / 500000000)) (hi := (304579519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6943 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6943 / 5120) = 1/(5120 / 6943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (152289759 / 500000000) (304579519 / 1000000000) (Real.log (6943 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6943 / 5120) = -Real.log (5120 / 6943) := by
    rw [show ((6943 / 5120) : ℝ) = ((5120 / 6943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (220070737 / 500000000) ≤ -Real.log (3297 / 5120) ∧
    -Real.log (3297 / 5120) ≤ (17605659 / 40000000) := by
  have h := checkLog_sound (w := (1823 / 8417)) (n := 12)
    (lo := (220070737 / 500000000)) (hi := (17605659 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3297) = 1/(3297 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-17605659 / 40000000) (-220070737 / 500000000) (Real.log (3297 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45135747 / 200000000) ≤ -Real.log (1000000 / 1253173) ∧
    -Real.log (1000000 / 1253173) ≤ (14104921 / 62500000) := by
  have h := checkLog_sound (w := (253173 / 2253173)) (n := 12)
    (lo := (45135747 / 200000000)) (hi := (14104921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253173 / 1000000) = 1/(1000000 / 1253173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45135747 / 200000000) (14104921 / 62500000) (Real.log (1253173 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1253173 / 1000000) = -Real.log (1000000 / 1253173) := by
    rw [show ((1253173 / 1000000) : ℝ) = ((1000000 / 1253173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (291921713 / 1000000000) ≤ -Real.log (746827 / 1000000) ∧
    -Real.log (746827 / 1000000) ≤ (145960857 / 500000000) := by
  have h := checkLog_sound (w := (253173 / 1746827)) (n := 12)
    (lo := (291921713 / 1000000000)) (hi := (145960857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746827) = 1/(746827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-145960857 / 500000000) (-291921713 / 1000000000) (Real.log (746827 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (226016221 / 1000000000) ≤ -Real.log (250000 / 313399) ∧
    -Real.log (250000 / 313399) ≤ (113008111 / 500000000) := by
  have h := checkLog_sound (w := (63399 / 563399)) (n := 12)
    (lo := (226016221 / 1000000000)) (hi := (113008111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313399 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313399 / 250000) = 1/(250000 / 313399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (226016221 / 1000000000) (113008111 / 500000000) (Real.log (313399 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (313399 / 250000) = -Real.log (250000 / 313399) := by
    rw [show ((313399 / 250000) : ℝ) = ((250000 / 313399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (29248827 / 100000000) ≤ -Real.log (186601 / 250000) ∧
    -Real.log (186601 / 250000) ≤ (292488271 / 1000000000) := by
  have h := checkLog_sound (w := (63399 / 436601)) (n := 12)
    (lo := (29248827 / 100000000)) (hi := (292488271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 186601) = 1/(186601 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-292488271 / 1000000000) (-29248827 / 100000000) (Real.log (186601 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167424477 / 1000000000) ≤ -Real.log (62500 / 73891) ∧
    -Real.log (62500 / 73891) ≤ (83712239 / 500000000) := by
  have h := checkLog_sound (w := (11391 / 136391)) (n := 12)
    (lo := (167424477 / 1000000000)) (hi := (83712239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73891 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73891 / 62500) = 1/(62500 / 73891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167424477 / 1000000000) (83712239 / 500000000) (Real.log (73891 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (73891 / 62500) = -Real.log (62500 / 73891) := by
    rw [show ((73891 / 62500) : ℝ) = ((62500 / 73891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (201205949 / 1000000000) ≤ -Real.log (51109 / 62500) ∧
    -Real.log (51109 / 62500) ≤ (4024119 / 20000000) := by
  have h := checkLog_sound (w := (11391 / 113609)) (n := 12)
    (lo := (201205949 / 1000000000)) (hi := (4024119 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51109) = 1/(51109 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4024119 / 20000000) (-201205949 / 1000000000) (Real.log (51109 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167691727 / 1000000000) ≤ -Real.log (250000 / 295643) ∧
    -Real.log (250000 / 295643) ≤ (10480733 / 62500000) := by
  have h := checkLog_sound (w := (45643 / 545643)) (n := 12)
    (lo := (167691727 / 1000000000)) (hi := (10480733 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295643 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295643 / 250000) = 1/(250000 / 295643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167691727 / 1000000000) (10480733 / 62500000) (Real.log (295643 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (295643 / 250000) = -Real.log (250000 / 295643) := by
    rw [show ((295643 / 250000) : ℝ) = ((250000 / 295643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (201592453 / 1000000000) ≤ -Real.log (204357 / 250000) ∧
    -Real.log (204357 / 250000) ≤ (100796227 / 500000000) := by
  have h := checkLog_sound (w := (45643 / 454357)) (n := 12)
    (lo := (201592453 / 1000000000)) (hi := (100796227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204357) = 1/(204357 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-100796227 / 500000000) (-201592453 / 1000000000) (Real.log (204357 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (744720993 / 1000000000) ≤ -Real.log (100000000000 / 210585380649) ∧
    -Real.log (100000000000 / 210585380649) ≤ (148944199 / 200000000) := by
  have h := checkLog_sound (w := (10585380649 / 410585380649)) (n := 12)
    (lo := (51573813 / 1000000000)) (hi := (25786907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210585380649 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210585380649 / 200000000000) = 1/(100000000000 / 210585380649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (744720993 / 1000000000) (148944199 / 200000000) (Real.log (210585380649 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (210585380649 / 100000000000) = -Real.log (100000000000 / 210585380649) := by
    rw [show ((210585380649 / 100000000000) : ℝ) = ((100000000000 / 210585380649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (373031661 / 500000000) ≤ -Real.log (500000000000 / 1054341226473) ∧
    -Real.log (500000000000 / 1054341226473) ≤ (186515831 / 250000000) := by
  have h := checkLog_sound (w := (54341226473 / 2054341226473)) (n := 12)
    (lo := (26458071 / 500000000)) (hi := (52916143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1054341226473 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1054341226473 / 1000000000000) = 1/(500000000000 / 1054341226473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (373031661 / 500000000) (186515831 / 250000000) (Real.log (1054341226473 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1054341226473 / 500000000000) = -Real.log (500000000000 / 1054341226473) := by
    rw [show ((1054341226473 / 500000000000) : ℝ) = ((500000000000 / 1054341226473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (8087507 / 15625000) ≤ -Real.log (100000000000 / 167799637667) ∧
    -Real.log (100000000000 / 167799637667) ≤ (517600449 / 1000000000) := by
  have h := checkLog_sound (w := (67799637667 / 267799637667)) (n := 12)
    (lo := (8087507 / 15625000)) (hi := (517600449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167799637667 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167799637667 / 100000000000) = 1/(100000000000 / 167799637667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (8087507 / 15625000) (517600449 / 1000000000) (Real.log (167799637667 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (167799637667 / 100000000000) = -Real.log (100000000000 / 167799637667) := by
    rw [show ((167799637667 / 100000000000) : ℝ) = ((100000000000 / 167799637667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (518504491 / 1000000000) ≤ -Real.log (500000000000 / 839757021667) ∧
    -Real.log (500000000000 / 839757021667) ≤ (129626123 / 250000000) := by
  have h := checkLog_sound (w := (339757021667 / 1339757021667)) (n := 12)
    (lo := (518504491 / 1000000000)) (hi := (129626123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839757021667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839757021667 / 500000000000) = 1/(500000000000 / 839757021667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (518504491 / 1000000000) (129626123 / 250000000) (Real.log (839757021667 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (839757021667 / 500000000000) = -Real.log (500000000000 / 839757021667) := by
    rw [show ((839757021667 / 500000000000) : ℝ) = ((500000000000 / 839757021667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (368630427 / 1000000000) ≤ -Real.log (125000000000 / 180719149269) ∧
    -Real.log (125000000000 / 180719149269) ≤ (92157607 / 250000000) := by
  have h := checkLog_sound (w := (55719149269 / 305719149269)) (n := 12)
    (lo := (368630427 / 1000000000)) (hi := (92157607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180719149269 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180719149269 / 125000000000) = 1/(125000000000 / 180719149269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (368630427 / 1000000000) (92157607 / 250000000) (Real.log (180719149269 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (180719149269 / 125000000000) = -Real.log (125000000000 / 180719149269) := by
    rw [show ((180719149269 / 125000000000) : ℝ) = ((125000000000 / 180719149269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18464209 / 50000000) ≤ -Real.log (500000000000 / 723349334743) ∧
    -Real.log (500000000000 / 723349334743) ≤ (369284181 / 1000000000) := by
  have h := checkLog_sound (w := (223349334743 / 1223349334743)) (n := 12)
    (lo := (18464209 / 50000000)) (hi := (369284181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723349334743 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723349334743 / 500000000000) = 1/(500000000000 / 723349334743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18464209 / 50000000) (369284181 / 1000000000) (Real.log (723349334743 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (723349334743 / 500000000000) = -Real.log (500000000000 / 723349334743) := by
    rw [show ((723349334743 / 500000000000) : ℝ) = ((500000000000 / 723349334743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16950363 / 500000000) ≤ -Real.log (60416716551 / 62500000000) ∧
    -Real.log (60416716551 / 62500000000) ≤ (33900727 / 1000000000) := by
  have h := checkLog_sound (w := (2083283449 / 122916716551)) (n := 12)
    (lo := (16950363 / 500000000)) (hi := (33900727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60416716551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60416716551) = 1/(60416716551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-33900727 / 1000000000) (-16950363 / 500000000) (Real.log (60416716551 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1055671 / 31250000) ≤ -Real.log (3776495119 / 3906250000) ∧
    -Real.log (3776495119 / 3906250000) ≤ (33781473 / 1000000000) := by
  have h := checkLog_sound (w := (129754881 / 7682745119)) (n := 12)
    (lo := (1055671 / 31250000)) (hi := (33781473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3776495119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3776495119) = 1/(3776495119 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-33781473 / 1000000000) (-1055671 / 31250000) (Real.log (3776495119 / 3906250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell181

end


