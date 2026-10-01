-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0015Logs__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0015Logs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:44:03.748414+00:00
-- url     : https://prove2.me/theorems/d5bdecc6-b2c3-4a4a-8a77-32c32c2db9a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0015Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0016Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0015Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0016Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0017Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0018Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0015Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0016Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0017Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0018Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0015Logs (+3 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0016Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0017Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0018Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0015Logs (+3 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0016Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0017Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0018Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0015Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0015
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

theorem reflection_log_1_neg : (682346879 / 1000000000) ≤ -Real.log (512 / 1013) ∧
    -Real.log (512 / 1013) ≤ (1066167 / 1562500) := by
  have h := checkLog_sound (w := (501 / 1525)) (n := 12)
    (lo := (682346879 / 1000000000)) (hi := (1066167 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1013 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1013 / 512) = 1/(512 / 1013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682346879 / 1000000000) (1066167 / 1562500) (Real.log (1013 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1013 / 512) = -Real.log (512 / 1013) := by
    rw [show ((1013 / 512) : ℝ) = ((512 / 1013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3840429349 / 1000000000) ≤ -Real.log (11 / 512) ∧
    -Real.log (11 / 512) ≤ (768085871 / 200000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16 / 11) = 1/(11 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-768085871 / 200000000) (-3840429349 / 1000000000) (Real.log (11 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682253093 / 1000000000) ≤ -Real.log (102400 / 202581) ∧
    -Real.log (102400 / 202581) ≤ (341126547 / 500000000) := by
  have h := checkLog_sound (w := (100181 / 304981)) (n := 12)
    (lo := (682253093 / 1000000000)) (hi := (341126547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202581 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202581 / 102400) = 1/(102400 / 202581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682253093 / 1000000000) (341126547 / 500000000) (Real.log (202581 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202581 / 102400) = -Real.log (102400 / 202581) := by
    rw [show ((202581 / 102400) : ℝ) = ((102400 / 202581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (766366013 / 200000000) ≤ -Real.log (2219 / 102400) ∧
    -Real.log (2219 / 102400) ≤ (3831830071 / 1000000000) := by
  have h := checkLog_sound (w := (981 / 5419)) (n := 12)
    (lo := (73218833 / 200000000)) (hi := (183047083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2219) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2219) = 1/(2219 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3831830071 / 1000000000) (-766366013 / 200000000) (Real.log (2219 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41964291 / 62500000) ≤ -Real.log (256 / 501) ∧
    -Real.log (256 / 501) ≤ (671428657 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 757)) (n := 12)
    (lo := (41964291 / 62500000)) (hi := (671428657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((501 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(501 / 256) = 1/(256 / 501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41964291 / 62500000) (671428657 / 1000000000) (Real.log (501 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (501 / 256) = -Real.log (256 / 501) := by
    rw [show ((501 / 256) : ℝ) = ((256 / 501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3147282169 / 1000000000) ≤ -Real.log (11 / 256) ∧
    -Real.log (11 / 256) ≤ (1573641087 / 500000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 11) = 1/(11 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1573641087 / 500000000) (-3147282169 / 1000000000) (Real.log (11 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671239017 / 1000000000) ≤ -Real.log (51200 / 100181) ∧
    -Real.log (51200 / 100181) ≤ (335619509 / 500000000) := by
  have h := checkLog_sound (w := (48981 / 151381)) (n := 12)
    (lo := (671239017 / 1000000000)) (hi := (335619509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100181 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100181 / 51200) = 1/(51200 / 100181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (671239017 / 1000000000) (335619509 / 500000000) (Real.log (100181 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100181 / 51200) = -Real.log (51200 / 100181) := by
    rw [show ((100181 / 51200) : ℝ) = ((51200 / 100181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (627736577 / 200000000) ≤ -Real.log (2219 / 51200) ∧
    -Real.log (2219 / 51200) ≤ (313868289 / 100000000) := by
  have h := checkLog_sound (w := (981 / 5419)) (n := 12)
    (lo := (73218833 / 200000000)) (hi := (183047083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2219) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2219) = 1/(2219 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-313868289 / 100000000) (-627736577 / 200000000) (Real.log (2219 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68391671 / 100000000) ≤ -Real.log (125000 / 247703) ∧
    -Real.log (125000 / 247703) ≤ (683916711 / 1000000000) := by
  have h := checkLog_sound (w := (122703 / 372703)) (n := 12)
    (lo := (68391671 / 100000000)) (hi := (683916711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247703 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247703 / 125000) = 1/(125000 / 247703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68391671 / 100000000) (683916711 / 1000000000) (Real.log (247703 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247703 / 125000) = -Real.log (125000 / 247703) := by
    rw [show ((247703 / 125000) : ℝ) = ((125000 / 247703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (399670981 / 100000000) ≤ -Real.log (2297 / 125000) ∧
    -Real.log (2297 / 125000) ≤ (499588727 / 125000000) := by
  have h := checkLog_sound (w := (6437 / 24813)) (n := 12)
    (lo := (53097391 / 100000000)) (hi := (530973911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9188) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9188) = 1/(2297 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-499588727 / 125000000) (-399670981 / 100000000) (Real.log (2297 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170998353 / 250000000) ≤ -Real.log (62500 / 123861) ∧
    -Real.log (62500 / 123861) ≤ (683993413 / 1000000000) := by
  have h := checkLog_sound (w := (61361 / 186361)) (n := 12)
    (lo := (170998353 / 250000000)) (hi := (683993413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123861 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123861 / 62500) = 1/(62500 / 123861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170998353 / 250000000) (683993413 / 1000000000) (Real.log (123861 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (123861 / 62500) = -Real.log (62500 / 123861) := by
    rw [show ((123861 / 62500) : ℝ) = ((62500 / 123861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4005015869 / 1000000000) ≤ -Real.log (1139 / 62500) ∧
    -Real.log (1139 / 62500) ≤ (32040127 / 8000000) := by
  have h := checkLog_sound (w := (6513 / 24737)) (n := 12)
    (lo := (539279969 / 1000000000)) (hi := (53927997 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9112) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9112) = 1/(1139 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-32040127 / 8000000) (-4005015869 / 1000000000) (Real.log (1139 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (683879871 / 1000000000) ≤ -Real.log (1000000 / 1981551) ∧
    -Real.log (1000000 / 1981551) ≤ (10685623 / 15625000) := by
  have h := checkLog_sound (w := (981551 / 2981551)) (n := 12)
    (lo := (683879871 / 1000000000)) (hi := (10685623 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981551 / 1000000) = 1/(1000000 / 1981551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (683879871 / 1000000000) (10685623 / 15625000) (Real.log (1981551 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1981551 / 1000000) = -Real.log (1000000 / 1981551) := by
    rw [show ((1981551 / 1000000) : ℝ) = ((1000000 / 1981551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3992745107 / 1000000000) ≤ -Real.log (18449 / 1000000) ∧
    -Real.log (18449 / 1000000) ≤ (3992745113 / 1000000000) := by
  have h := checkLog_sound (w := (12801 / 49699)) (n := 12)
    (lo := (527009207 / 1000000000)) (hi := (65876151 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18449) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18449) = 1/(18449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3992745113 / 1000000000) (-3992745107 / 1000000000) (Real.log (18449 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (17098927 / 25000000) ≤ -Real.log (125000 / 247713) ∧
    -Real.log (125000 / 247713) ≤ (683957081 / 1000000000) := by
  have h := checkLog_sound (w := (122713 / 372713)) (n := 12)
    (lo := (17098927 / 25000000)) (hi := (683957081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247713 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247713 / 125000) = 1/(125000 / 247713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (17098927 / 25000000) (683957081 / 1000000000) (Real.log (247713 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247713 / 125000) = -Real.log (125000 / 247713) := by
    rw [show ((247713 / 125000) : ℝ) = ((125000 / 247713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4001072819 / 1000000000) ≤ -Real.log (2287 / 125000) ∧
    -Real.log (2287 / 125000) ≤ (160042913 / 40000000) := by
  have h := checkLog_sound (w := (6477 / 24773)) (n := 12)
    (lo := (535336919 / 1000000000)) (hi := (13383423 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9148) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9148) = 1/(2287 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-160042913 / 40000000) (-4001072819 / 1000000000) (Real.log (2287 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (117015663 / 25000000) ≤ -Real.log (500000000000 / 53918807139747) ∧
    -Real.log (500000000000 / 53918807139747) ≤ (4680626527 / 1000000000) := by
  have h := checkLog_sound (w := (21918807139747 / 85918807139747)) (n := 12)
    (lo := (6521793 / 12500000)) (hi := (521743441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53918807139747 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53918807139747 / 32000000000000) = 1/(500000000000 / 53918807139747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (117015663 / 25000000) (4680626527 / 1000000000) (Real.log (53918807139747 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (53918807139747 / 500000000000) = -Real.log (500000000000 / 53918807139747) := by
    rw [show ((53918807139747 / 500000000000) : ℝ) = ((500000000000 / 53918807139747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4689009281 / 1000000000) ≤ -Real.log (125000000000 / 13593173836699) ∧
    -Real.log (125000000000 / 13593173836699) ≤ (586126161 / 125000000) := by
  have h := checkLog_sound (w := (5593173836699 / 21593173836699)) (n := 12)
    (lo := (530126201 / 1000000000)) (hi := (265063101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13593173836699 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(13593173836699 / 8000000000000) = 1/(125000000000 / 13593173836699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4689009281 / 1000000000) (586126161 / 125000000) (Real.log (13593173836699 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13593173836699 / 125000000000) = -Real.log (125000000000 / 13593173836699) := by
    rw [show ((13593173836699 / 125000000000) : ℝ) = ((125000000000 / 13593173836699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2338312489 / 500000000) ≤ -Real.log (500000000000 / 53703479863407) ∧
    -Real.log (500000000000 / 53703479863407) ≤ (935324997 / 200000000) := by
  have h := checkLog_sound (w := (21703479863407 / 85703479863407)) (n := 12)
    (lo := (258870949 / 500000000)) (hi := (517741899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53703479863407 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53703479863407 / 32000000000000) = 1/(500000000000 / 53703479863407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2338312489 / 500000000) (935324997 / 200000000) (Real.log (53703479863407 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (53703479863407 / 500000000000) = -Real.log (500000000000 / 53703479863407) := by
    rw [show ((53703479863407 / 500000000000) : ℝ) = ((500000000000 / 53703479863407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4685029899 / 1000000000) ≤ -Real.log (50000000000 / 5415675557499) ∧
    -Real.log (50000000000 / 5415675557499) ≤ (2342514953 / 500000000) := by
  have h := checkLog_sound (w := (2215675557499 / 8615675557499)) (n := 12)
    (lo := (526146819 / 1000000000)) (hi := (26307341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5415675557499 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5415675557499 / 3200000000000) = 1/(50000000000 / 5415675557499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4685029899 / 1000000000) (2342514953 / 500000000) (Real.log (5415675557499 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5415675557499 / 50000000000) = -Real.log (50000000000 / 5415675557499) := by
    rw [show ((5415675557499 / 50000000000) : ℝ) = ((50000000000 / 5415675557499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0015

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0016Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0016
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

theorem reflection_log_1_neg : (682253093 / 1000000000) ≤ -Real.log (102400 / 202581) ∧
    -Real.log (102400 / 202581) ≤ (341126547 / 500000000) := by
  have h := checkLog_sound (w := (100181 / 304981)) (n := 12)
    (lo := (682253093 / 1000000000)) (hi := (341126547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202581 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202581 / 102400) = 1/(102400 / 202581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682253093 / 1000000000) (341126547 / 500000000) (Real.log (202581 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202581 / 102400) = -Real.log (102400 / 202581) := by
    rw [show ((202581 / 102400) : ℝ) = ((102400 / 202581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (766366013 / 200000000) ≤ -Real.log (2219 / 102400) ∧
    -Real.log (2219 / 102400) ≤ (3831830071 / 1000000000) := by
  have h := checkLog_sound (w := (981 / 5419)) (n := 12)
    (lo := (73218833 / 200000000)) (hi := (183047083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2219) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2219) = 1/(2219 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3831830071 / 1000000000) (-766366013 / 200000000) (Real.log (2219 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682159299 / 1000000000) ≤ -Real.log (51200 / 101281) ∧
    -Real.log (51200 / 101281) ≤ (6821593 / 10000000) := by
  have h := checkLog_sound (w := (50081 / 152481)) (n := 12)
    (lo := (682159299 / 1000000000)) (hi := (6821593 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101281 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101281 / 51200) = 1/(51200 / 101281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682159299 / 1000000000) (6821593 / 10000000) (Real.log (101281 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101281 / 51200) = -Real.log (51200 / 101281) := by
    rw [show ((101281 / 51200) : ℝ) = ((51200 / 101281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3823304099 / 1000000000) ≤ -Real.log (1119 / 51200) ∧
    -Real.log (1119 / 51200) ≤ (764660821 / 200000000) := by
  have h := checkLog_sound (w := (481 / 2719)) (n := 12)
    (lo := (357568199 / 1000000000)) (hi := (1787841 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1119) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1119) = 1/(1119 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-764660821 / 200000000) (-3823304099 / 1000000000) (Real.log (1119 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671239017 / 1000000000) ≤ -Real.log (51200 / 100181) ∧
    -Real.log (51200 / 100181) ≤ (335619509 / 500000000) := by
  have h := checkLog_sound (w := (48981 / 151381)) (n := 12)
    (lo := (671239017 / 1000000000)) (hi := (335619509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100181 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100181 / 51200) = 1/(51200 / 100181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671239017 / 1000000000) (335619509 / 500000000) (Real.log (100181 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100181 / 51200) = -Real.log (51200 / 100181) := by
    rw [show ((100181 / 51200) : ℝ) = ((51200 / 100181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (627736577 / 200000000) ≤ -Real.log (2219 / 51200) ∧
    -Real.log (2219 / 51200) ≤ (313868289 / 100000000) := by
  have h := checkLog_sound (w := (981 / 5419)) (n := 12)
    (lo := (73218833 / 200000000)) (hi := (183047083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2219) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2219) = 1/(2219 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-313868289 / 100000000) (-627736577 / 200000000) (Real.log (2219 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671049343 / 1000000000) ≤ -Real.log (25600 / 50081) ∧
    -Real.log (25600 / 50081) ≤ (5242573 / 7812500) := by
  have h := checkLog_sound (w := (24481 / 75681)) (n := 12)
    (lo := (671049343 / 1000000000)) (hi := (5242573 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50081 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50081 / 25600) = 1/(25600 / 50081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (671049343 / 1000000000) (5242573 / 7812500) (Real.log (50081 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (50081 / 25600) = -Real.log (25600 / 50081) := by
    rw [show ((50081 / 25600) : ℝ) = ((25600 / 50081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3130156919 / 1000000000) ≤ -Real.log (1119 / 25600) ∧
    -Real.log (1119 / 25600) ≤ (782539231 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2719)) (n := 12)
    (lo := (357568199 / 1000000000)) (hi := (1787841 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1119) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1119) = 1/(1119 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-782539231 / 250000000) (-3130156919 / 1000000000) (Real.log (1119 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683840507 / 1000000000) ≤ -Real.log (1000000 / 1981473) ∧
    -Real.log (1000000 / 1981473) ≤ (170960127 / 250000000) := by
  have h := checkLog_sound (w := (981473 / 2981473)) (n := 12)
    (lo := (683840507 / 1000000000)) (hi := (170960127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981473 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981473 / 1000000) = 1/(1000000 / 1981473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683840507 / 1000000000) (170960127 / 250000000) (Real.log (1981473 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1981473 / 1000000) = -Real.log (1000000 / 1981473) := by
    rw [show ((1981473 / 1000000) : ℝ) = ((1000000 / 1981473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (997131537 / 250000000) ≤ -Real.log (18527 / 1000000) ∧
    -Real.log (18527 / 1000000) ≤ (1994263077 / 500000000) := by
  have h := checkLog_sound (w := (12723 / 49777)) (n := 12)
    (lo := (65348781 / 125000000)) (hi := (522790249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18527) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18527) = 1/(18527 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1994263077 / 500000000) (-997131537 / 250000000) (Real.log (18527 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136783443 / 200000000) ≤ -Real.log (8000 / 15853) ∧
    -Real.log (8000 / 15853) ≤ (21372413 / 31250000) := by
  have h := checkLog_sound (w := (7853 / 23853)) (n := 12)
    (lo := (136783443 / 200000000)) (hi := (21372413 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15853 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15853 / 8000) = 1/(8000 / 15853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136783443 / 200000000) (21372413 / 31250000) (Real.log (15853 / 8000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (15853 / 8000) = -Real.log (8000 / 15853) := by
    rw [show ((15853 / 8000) : ℝ) = ((8000 / 15853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3996764231 / 1000000000) ≤ -Real.log (147 / 8000) ∧
    -Real.log (147 / 8000) ≤ (3996764237 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 397)) (n := 12)
    (lo := (531028331 / 1000000000)) (hi := (132757083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 147) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(250 / 147) = 1/(147 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3996764237 / 1000000000) (-3996764231 / 1000000000) (Real.log (147 / 8000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21368833 / 31250000) ≤ -Real.log (500000 / 990699) ∧
    -Real.log (500000 / 990699) ≤ (683802657 / 1000000000) := by
  have h := checkLog_sound (w := (490699 / 1490699)) (n := 12)
    (lo := (21368833 / 31250000)) (hi := (683802657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990699 / 500000) = 1/(500000 / 990699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21368833 / 31250000) (683802657 / 1000000000) (Real.log (990699 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (990699 / 500000) = -Real.log (500000 / 990699) := by
    rw [show ((990699 / 500000) : ℝ) = ((500000 / 990699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1992243087 / 500000000) ≤ -Real.log (9301 / 500000) ∧
    -Real.log (9301 / 500000) ≤ (199224309 / 50000000) := by
  have h := checkLog_sound (w := (3162 / 12463)) (n := 12)
    (lo := (259375137 / 500000000)) (hi := (20750011 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9301) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9301) = 1/(9301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-199224309 / 50000000) (-1992243087 / 500000000) (Real.log (9301 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85485047 / 125000000) ≤ -Real.log (62500 / 123847) ∧
    -Real.log (62500 / 123847) ≤ (683880377 / 1000000000) := by
  have h := checkLog_sound (w := (61347 / 186347)) (n := 12)
    (lo := (85485047 / 125000000)) (hi := (683880377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123847 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123847 / 62500) = 1/(62500 / 123847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85485047 / 125000000) (683880377 / 1000000000) (Real.log (123847 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (123847 / 62500) = -Real.log (62500 / 123847) := by
    rw [show ((123847 / 62500) : ℝ) = ((62500 / 123847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (249549957 / 62500000) ≤ -Real.log (1153 / 62500) ∧
    -Real.log (1153 / 62500) ≤ (1996399659 / 500000000) := by
  have h := checkLog_sound (w := (6401 / 24849)) (n := 12)
    (lo := (131765853 / 250000000)) (hi := (527063413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9224) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9224) = 1/(1153 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1996399659 / 500000000) (-249549957 / 62500000) (Real.log (1153 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (934473331 / 200000000) ≤ -Real.log (50000000000 / 5347527932207) ∧
    -Real.log (50000000000 / 5347527932207) ≤ (2336183331 / 500000000) := by
  have h := checkLog_sound (w := (2147527932207 / 8547527932207)) (n := 12)
    (lo := (20539343 / 40000000)) (hi := (64185447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5347527932207 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5347527932207 / 3200000000000) = 1/(50000000000 / 5347527932207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (934473331 / 200000000) (2336183331 / 500000000) (Real.log (5347527932207 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5347527932207 / 50000000000) = -Real.log (50000000000 / 5347527932207) := by
    rw [show ((5347527932207 / 50000000000) : ℝ) = ((50000000000 / 5347527932207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (936136289 / 200000000) ≤ -Real.log (500000000000 / 53921768707483) ∧
    -Real.log (500000000000 / 53921768707483) ≤ (1170170363 / 250000000) := by
  have h := checkLog_sound (w := (21921768707483 / 85921768707483)) (n := 12)
    (lo := (104359673 / 200000000)) (hi := (260899183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53921768707483 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53921768707483 / 32000000000000) = 1/(500000000000 / 53921768707483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (936136289 / 200000000) (1170170363 / 250000000) (Real.log (53921768707483 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (53921768707483 / 500000000000) = -Real.log (500000000000 / 53921768707483) := by
    rw [show ((53921768707483 / 500000000000) : ℝ) = ((500000000000 / 53921768707483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4668288829 / 1000000000) ≤ -Real.log (62500000000 / 6657207558327) ∧
    -Real.log (62500000000 / 6657207558327) ≤ (1167072209 / 250000000) := by
  have h := checkLog_sound (w := (2657207558327 / 10657207558327)) (n := 12)
    (lo := (509405749 / 1000000000)) (hi := (2037623 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6657207558327 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6657207558327 / 4000000000000) = 1/(62500000000 / 6657207558327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4668288829 / 1000000000) (1167072209 / 250000000) (Real.log (6657207558327 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6657207558327 / 62500000000) = -Real.log (62500000000 / 6657207558327) := by
    rw [show ((6657207558327 / 62500000000) : ℝ) = ((62500000000 / 6657207558327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (584584961 / 125000000) ≤ -Real.log (62500000000 / 6713302254987) ∧
    -Real.log (62500000000 / 6713302254987) ≤ (935335939 / 200000000) := by
  have h := checkLog_sound (w := (2713302254987 / 10713302254987)) (n := 12)
    (lo := (2022643 / 3906250)) (hi := (517796609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6713302254987 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6713302254987 / 4000000000000) = 1/(62500000000 / 6713302254987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (584584961 / 125000000) (935335939 / 200000000) (Real.log (6713302254987 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6713302254987 / 62500000000) = -Real.log (62500000000 / 6713302254987) := by
    rw [show ((6713302254987 / 62500000000) : ℝ) = ((62500000000 / 6713302254987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0016

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0017Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0017
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

theorem reflection_log_1_neg : (682159299 / 1000000000) ≤ -Real.log (51200 / 101281) ∧
    -Real.log (51200 / 101281) ≤ (6821593 / 10000000) := by
  have h := checkLog_sound (w := (50081 / 152481)) (n := 12)
    (lo := (682159299 / 1000000000)) (hi := (6821593 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101281 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101281 / 51200) = 1/(51200 / 101281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682159299 / 1000000000) (6821593 / 10000000) (Real.log (101281 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101281 / 51200) = -Real.log (51200 / 101281) := by
    rw [show ((101281 / 51200) : ℝ) = ((51200 / 101281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3823304099 / 1000000000) ≤ -Real.log (1119 / 51200) ∧
    -Real.log (1119 / 51200) ≤ (764660821 / 200000000) := by
  have h := checkLog_sound (w := (481 / 2719)) (n := 12)
    (lo := (357568199 / 1000000000)) (hi := (1787841 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1119) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1119) = 1/(1119 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-764660821 / 200000000) (-3823304099 / 1000000000) (Real.log (1119 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682065497 / 1000000000) ≤ -Real.log (102400 / 202543) ∧
    -Real.log (102400 / 202543) ≤ (341032749 / 500000000) := by
  have h := checkLog_sound (w := (100143 / 304943)) (n := 12)
    (lo := (682065497 / 1000000000)) (hi := (341032749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202543 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202543 / 102400) = 1/(102400 / 202543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682065497 / 1000000000) (341032749 / 500000000) (Real.log (202543 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202543 / 102400) = -Real.log (102400 / 202543) := by
    rw [show ((202543 / 102400) : ℝ) = ((102400 / 202543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3814850211 / 1000000000) ≤ -Real.log (2257 / 102400) ∧
    -Real.log (2257 / 102400) ≤ (3814850217 / 1000000000) := by
  have h := checkLog_sound (w := (943 / 5457)) (n := 12)
    (lo := (349114311 / 1000000000)) (hi := (43639289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2257) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2257) = 1/(2257 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3814850217 / 1000000000) (-3814850211 / 1000000000) (Real.log (2257 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671049343 / 1000000000) ≤ -Real.log (25600 / 50081) ∧
    -Real.log (25600 / 50081) ≤ (5242573 / 7812500) := by
  have h := checkLog_sound (w := (24481 / 75681)) (n := 12)
    (lo := (671049343 / 1000000000)) (hi := (5242573 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50081 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50081 / 25600) = 1/(25600 / 50081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671049343 / 1000000000) (5242573 / 7812500) (Real.log (50081 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50081 / 25600) = -Real.log (25600 / 50081) := by
    rw [show ((50081 / 25600) : ℝ) = ((25600 / 50081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3130156919 / 1000000000) ≤ -Real.log (1119 / 25600) ∧
    -Real.log (1119 / 25600) ≤ (782539231 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2719)) (n := 12)
    (lo := (357568199 / 1000000000)) (hi := (1787841 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1119) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1119) = 1/(1119 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-782539231 / 250000000) (-3130156919 / 1000000000) (Real.log (1119 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41928727 / 62500000) ≤ -Real.log (51200 / 100143) ∧
    -Real.log (51200 / 100143) ≤ (670859633 / 1000000000) := by
  have h := checkLog_sound (w := (48943 / 151343)) (n := 12)
    (lo := (41928727 / 62500000)) (hi := (670859633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100143 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100143 / 51200) = 1/(51200 / 100143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41928727 / 62500000) (670859633 / 1000000000) (Real.log (100143 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100143 / 51200) = -Real.log (51200 / 100143) := by
    rw [show ((100143 / 51200) : ℝ) = ((51200 / 100143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3121703031 / 1000000000) ≤ -Real.log (2257 / 51200) ∧
    -Real.log (2257 / 51200) ≤ (780425759 / 250000000) := by
  have h := checkLog_sound (w := (943 / 5457)) (n := 12)
    (lo := (349114311 / 1000000000)) (hi := (43639289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2257) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2257) = 1/(2257 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-780425759 / 250000000) (-3121703031 / 1000000000) (Real.log (2257 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341882149 / 500000000) ≤ -Real.log (500000 / 990661) ∧
    -Real.log (500000 / 990661) ≤ (683764299 / 1000000000) := by
  have h := checkLog_sound (w := (490661 / 1490661)) (n := 12)
    (lo := (341882149 / 500000000)) (hi := (683764299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990661 / 500000) = 1/(500000 / 990661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341882149 / 500000000) (683764299 / 1000000000) (Real.log (990661 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (990661 / 500000) = -Real.log (500000 / 990661) := by
    rw [show ((990661 / 500000) : ℝ) = ((500000 / 990661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (796081783 / 200000000) ≤ -Real.log (9339 / 500000) ∧
    -Real.log (9339 / 500000) ≤ (3980408921 / 1000000000) := by
  have h := checkLog_sound (w := (3143 / 12482)) (n := 12)
    (lo := (102934603 / 200000000)) (hi := (64334127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9339) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9339) = 1/(9339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3980408921 / 1000000000) (-796081783 / 200000000) (Real.log (9339 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170960253 / 250000000) ≤ -Real.log (500000 / 990737) ∧
    -Real.log (500000 / 990737) ≤ (683841013 / 1000000000) := by
  have h := checkLog_sound (w := (490737 / 1490737)) (n := 12)
    (lo := (170960253 / 250000000)) (hi := (683841013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990737 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990737 / 500000) = 1/(500000 / 990737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170960253 / 250000000) (683841013 / 1000000000) (Real.log (990737 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (990737 / 500000) = -Real.log (500000 / 990737) := by
    rw [show ((990737 / 500000) : ℝ) = ((500000 / 990737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (31908641 / 8000000) ≤ -Real.log (9263 / 500000) ∧
    -Real.log (9263 / 500000) ≤ (3988580131 / 1000000000) := by
  have h := checkLog_sound (w := (3181 / 12444)) (n := 12)
    (lo := (20913769 / 40000000)) (hi := (261422113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9263) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9263) = 1/(9263 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3988580131 / 1000000000) (-31908641 / 8000000) (Real.log (9263 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (683725939 / 1000000000) ≤ -Real.log (500000 / 990623) ∧
    -Real.log (500000 / 990623) ≤ (34186297 / 50000000) := by
  have h := checkLog_sound (w := (490623 / 1490623)) (n := 12)
    (lo := (683725939 / 1000000000)) (hi := (34186297 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990623 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990623 / 500000) = 1/(500000 / 990623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (683725939 / 1000000000) (34186297 / 50000000) (Real.log (990623 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (990623 / 500000) = -Real.log (500000 / 990623) := by
    rw [show ((990623 / 500000) : ℝ) = ((500000 / 990623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3976348213 / 1000000000) ≤ -Real.log (9377 / 500000) ∧
    -Real.log (9377 / 500000) ≤ (3976348219 / 1000000000) := by
  have h := checkLog_sound (w := (3124 / 12501)) (n := 12)
    (lo := (510612313 / 1000000000)) (hi := (255306157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9377) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9377) = 1/(9377 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3976348219 / 1000000000) (-3976348213 / 1000000000) (Real.log (9377 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (17095079 / 25000000) ≤ -Real.log (1000000 / 1981399) ∧
    -Real.log (1000000 / 1981399) ≤ (683803161 / 1000000000) := by
  have h := checkLog_sound (w := (981399 / 2981399)) (n := 12)
    (lo := (17095079 / 25000000)) (hi := (683803161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981399 / 1000000) = 1/(1000000 / 1981399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (17095079 / 25000000) (683803161 / 1000000000) (Real.log (1981399 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1981399 / 1000000) = -Real.log (1000000 / 1981399) := by
    rw [show ((1981399 / 1000000) : ℝ) = ((1000000 / 1981399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3984539933 / 1000000000) ≤ -Real.log (18601 / 1000000) ∧
    -Real.log (18601 / 1000000) ≤ (3984539939 / 1000000000) := by
  have h := checkLog_sound (w := (12649 / 49851)) (n := 12)
    (lo := (518804033 / 1000000000)) (hi := (259402017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18601) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18601) = 1/(18601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3984539939 / 1000000000) (-3984539933 / 1000000000) (Real.log (18601 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4664173213 / 1000000000) ≤ -Real.log (500000000000 / 53038922796873) ∧
    -Real.log (500000000000 / 53038922796873) ≤ (233208661 / 50000000) := by
  have h := checkLog_sound (w := (21038922796873 / 85038922796873)) (n := 12)
    (lo := (505290133 / 1000000000)) (hi := (252645067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53038922796873 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53038922796873 / 32000000000000) = 1/(500000000000 / 53038922796873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4664173213 / 1000000000) (233208661 / 50000000) (Real.log (53038922796873 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (53038922796873 / 500000000000) = -Real.log (500000000000 / 53038922796873) := by
    rw [show ((53038922796873 / 500000000000) : ℝ) = ((500000000000 / 53038922796873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (292026321 / 62500000) ≤ -Real.log (100000000000 / 10695638562021) ∧
    -Real.log (100000000000 / 10695638562021) ≤ (4672421143 / 1000000000) := by
  have h := checkLog_sound (w := (4295638562021 / 17095638562021)) (n := 12)
    (lo := (64192257 / 125000000)) (hi := (513538057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10695638562021 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10695638562021 / 6400000000000) = 1/(100000000000 / 10695638562021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (292026321 / 62500000) (4672421143 / 1000000000) (Real.log (10695638562021 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10695638562021 / 100000000000) = -Real.log (100000000000 / 10695638562021) := by
    rw [show ((10695638562021 / 100000000000) : ℝ) = ((100000000000 / 10695638562021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (582509269 / 125000000) ≤ -Real.log (500000000000 / 52821957982297) ∧
    -Real.log (500000000000 / 52821957982297) ≤ (4660074159 / 1000000000) := by
  have h := checkLog_sound (w := (20821957982297 / 84821957982297)) (n := 12)
    (lo := (15662221 / 31250000)) (hi := (501191073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52821957982297 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52821957982297 / 32000000000000) = 1/(500000000000 / 52821957982297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (582509269 / 125000000) (4660074159 / 1000000000) (Real.log (52821957982297 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (52821957982297 / 500000000000) = -Real.log (500000000000 / 52821957982297) := by
    rw [show ((52821957982297 / 500000000000) : ℝ) = ((500000000000 / 52821957982297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4668343093 / 1000000000) ≤ -Real.log (250000000000 / 26630275254019) ∧
    -Real.log (250000000000 / 26630275254019) ≤ (46683431 / 10000000) := by
  have h := checkLog_sound (w := (10630275254019 / 42630275254019)) (n := 12)
    (lo := (509460013 / 1000000000)) (hi := (254730007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26630275254019 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(26630275254019 / 16000000000000) = 1/(250000000000 / 26630275254019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4668343093 / 1000000000) (46683431 / 10000000) (Real.log (26630275254019 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (26630275254019 / 250000000000) = -Real.log (250000000000 / 26630275254019) := by
    rw [show ((26630275254019 / 250000000000) : ℝ) = ((250000000000 / 26630275254019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0017

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0018Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0018
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

theorem reflection_log_1_neg : (682065497 / 1000000000) ≤ -Real.log (102400 / 202543) ∧
    -Real.log (102400 / 202543) ≤ (341032749 / 500000000) := by
  have h := checkLog_sound (w := (100143 / 304943)) (n := 12)
    (lo := (682065497 / 1000000000)) (hi := (341032749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202543 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202543 / 102400) = 1/(102400 / 202543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682065497 / 1000000000) (341032749 / 500000000) (Real.log (202543 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202543 / 102400) = -Real.log (102400 / 202543) := by
    rw [show ((202543 / 102400) : ℝ) = ((102400 / 202543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3814850211 / 1000000000) ≤ -Real.log (2257 / 102400) ∧
    -Real.log (2257 / 102400) ≤ (3814850217 / 1000000000) := by
  have h := checkLog_sound (w := (943 / 5457)) (n := 12)
    (lo := (349114311 / 1000000000)) (hi := (43639289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2257) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2257) = 1/(2257 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3814850217 / 1000000000) (-3814850211 / 1000000000) (Real.log (2257 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136394337 / 200000000) ≤ -Real.log (25600 / 50631) ∧
    -Real.log (25600 / 50631) ≤ (340985843 / 500000000) := by
  have h := checkLog_sound (w := (25031 / 76231)) (n := 12)
    (lo := (136394337 / 200000000)) (hi := (340985843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50631 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50631 / 25600) = 1/(25600 / 50631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136394337 / 200000000) (340985843 / 500000000) (Real.log (50631 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50631 / 25600) = -Real.log (25600 / 50631) := by
    rw [show ((50631 / 25600) : ℝ) = ((25600 / 50631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3806467193 / 1000000000) ≤ -Real.log (569 / 25600) ∧
    -Real.log (569 / 25600) ≤ (3806467199 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 1369)) (n := 12)
    (lo := (340731293 / 1000000000)) (hi := (170365647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 569) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 569) = 1/(569 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3806467199 / 1000000000) (-3806467193 / 1000000000) (Real.log (569 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41928727 / 62500000) ≤ -Real.log (51200 / 100143) ∧
    -Real.log (51200 / 100143) ≤ (670859633 / 1000000000) := by
  have h := checkLog_sound (w := (48943 / 151343)) (n := 12)
    (lo := (41928727 / 62500000)) (hi := (670859633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100143 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100143 / 51200) = 1/(51200 / 100143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41928727 / 62500000) (670859633 / 1000000000) (Real.log (100143 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100143 / 51200) = -Real.log (51200 / 100143) := by
    rw [show ((100143 / 51200) : ℝ) = ((51200 / 100143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3121703031 / 1000000000) ≤ -Real.log (2257 / 51200) ∧
    -Real.log (2257 / 51200) ≤ (780425759 / 250000000) := by
  have h := checkLog_sound (w := (943 / 5457)) (n := 12)
    (lo := (349114311 / 1000000000)) (hi := (43639289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2257) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2257) = 1/(2257 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-780425759 / 250000000) (-3121703031 / 1000000000) (Real.log (2257 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (134133977 / 200000000) ≤ -Real.log (12800 / 25031) ∧
    -Real.log (12800 / 25031) ≤ (335334943 / 500000000) := by
  have h := checkLog_sound (w := (12231 / 37831)) (n := 12)
    (lo := (134133977 / 200000000)) (hi := (335334943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25031 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25031 / 12800) = 1/(12800 / 25031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (134133977 / 200000000) (335334943 / 500000000) (Real.log (25031 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (25031 / 12800) = -Real.log (12800 / 25031) := by
    rw [show ((25031 / 12800) : ℝ) = ((12800 / 25031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3113320013 / 1000000000) ≤ -Real.log (569 / 12800) ∧
    -Real.log (569 / 12800) ≤ (1556660009 / 500000000) := by
  have h := checkLog_sound (w := (231 / 1369)) (n := 12)
    (lo := (340731293 / 1000000000)) (hi := (170365647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 569) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 569) = 1/(569 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1556660009 / 500000000) (-3113320013 / 1000000000) (Real.log (569 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170922021 / 250000000) ≤ -Real.log (1000000 / 1981171) ∧
    -Real.log (1000000 / 1981171) ≤ (136737617 / 200000000) := by
  have h := checkLog_sound (w := (981171 / 2981171)) (n := 12)
    (lo := (170922021 / 250000000)) (hi := (136737617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981171 / 1000000) = 1/(1000000 / 1981171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170922021 / 250000000) (136737617 / 200000000) (Real.log (1981171 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1981171 / 1000000) = -Real.log (1000000 / 1981171) := by
    rw [show ((1981171 / 1000000) : ℝ) = ((1000000 / 1981171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3972357041 / 1000000000) ≤ -Real.log (18829 / 1000000) ∧
    -Real.log (18829 / 1000000) ≤ (3972357047 / 1000000000) := by
  have h := checkLog_sound (w := (12421 / 50079)) (n := 12)
    (lo := (506621141 / 1000000000)) (hi := (253310571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18829) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18829) = 1/(18829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3972357047 / 1000000000) (-3972357041 / 1000000000) (Real.log (18829 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (683764803 / 1000000000) ≤ -Real.log (1000000 / 1981323) ∧
    -Real.log (1000000 / 1981323) ≤ (170941201 / 250000000) := by
  have h := checkLog_sound (w := (981323 / 2981323)) (n := 12)
    (lo := (683764803 / 1000000000)) (hi := (170941201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981323 / 1000000) = 1/(1000000 / 1981323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (683764803 / 1000000000) (170941201 / 250000000) (Real.log (1981323 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1981323 / 1000000) = -Real.log (1000000 / 1981323) := by
    rw [show ((1981323 / 1000000) : ℝ) = ((1000000 / 1981323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (796092491 / 200000000) ≤ -Real.log (18677 / 1000000) ∧
    -Real.log (18677 / 1000000) ≤ (3980462461 / 1000000000) := by
  have h := checkLog_sound (w := (12573 / 49927)) (n := 12)
    (lo := (102945311 / 200000000)) (hi := (128681639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18677) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18677) = 1/(18677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3980462461 / 1000000000) (-796092491 / 200000000) (Real.log (18677 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (683649217 / 1000000000) ≤ -Real.log (500000 / 990547) ∧
    -Real.log (500000 / 990547) ≤ (341824609 / 500000000) := by
  have h := checkLog_sound (w := (490547 / 1490547)) (n := 12)
    (lo := (683649217 / 1000000000)) (hi := (341824609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990547 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990547 / 500000) = 1/(500000 / 990547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (683649217 / 1000000000) (341824609 / 500000000) (Real.log (990547 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (990547 / 500000) = -Real.log (500000 / 990547) := by
    rw [show ((990547 / 500000) : ℝ) = ((500000 / 990547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (496034493 / 125000000) ≤ -Real.log (9453 / 500000) ∧
    -Real.log (9453 / 500000) ≤ (79365519 / 20000000) := by
  have h := checkLog_sound (w := (3086 / 12539)) (n := 12)
    (lo := (125635011 / 250000000)) (hi := (100508009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9453) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9453) = 1/(9453 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-79365519 / 20000000) (-496034493 / 125000000) (Real.log (9453 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (170931611 / 250000000) ≤ -Real.log (1000000 / 1981247) ∧
    -Real.log (1000000 / 1981247) ≤ (136745289 / 200000000) := by
  have h := checkLog_sound (w := (981247 / 2981247)) (n := 12)
    (lo := (170931611 / 250000000)) (hi := (136745289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981247 / 1000000) = 1/(1000000 / 1981247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (170931611 / 250000000) (136745289 / 200000000) (Real.log (1981247 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1981247 / 1000000) = -Real.log (1000000 / 1981247) := by
    rw [show ((1981247 / 1000000) : ℝ) = ((1000000 / 1981247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31065637 / 7812500) ≤ -Real.log (18753 / 1000000) ∧
    -Real.log (18753 / 1000000) ≤ (1988200771 / 500000000) := by
  have h := checkLog_sound (w := (12497 / 50003)) (n := 12)
    (lo := (127666409 / 250000000)) (hi := (510665637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18753) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18753) = 1/(18753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1988200771 / 500000000) (-31065637 / 7812500) (Real.log (18753 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (37248361 / 8000000) ≤ -Real.log (250000000000 / 26304782516331) ∧
    -Real.log (250000000000 / 26304782516331) ≤ (1164011283 / 250000000) := by
  have h := checkLog_sound (w := (10304782516331 / 42304782516331)) (n := 12)
    (lo := (99432409 / 200000000)) (hi := (248581023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26304782516331 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(26304782516331 / 16000000000000) = 1/(250000000000 / 26304782516331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (37248361 / 8000000) (1164011283 / 250000000) (Real.log (26304782516331 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (26304782516331 / 250000000000) = -Real.log (250000000000 / 26304782516331) := by
    rw [show ((26304782516331 / 250000000000) : ℝ) = ((250000000000 / 26304782516331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2332113629 / 500000000) ≤ -Real.log (500000000000 / 53041789366601) ∧
    -Real.log (500000000000 / 53041789366601) ≤ (932845453 / 200000000) := by
  have h := checkLog_sound (w := (21041789366601 / 85041789366601)) (n := 12)
    (lo := (252672089 / 500000000)) (hi := (505344179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53041789366601 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53041789366601 / 32000000000000) = 1/(500000000000 / 53041789366601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2332113629 / 500000000) (932845453 / 200000000) (Real.log (53041789366601 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (53041789366601 / 500000000000) = -Real.log (500000000000 / 53041789366601) := by
    rw [show ((53041789366601 / 500000000000) : ℝ) = ((500000000000 / 53041789366601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (116298129 / 25000000) ≤ -Real.log (500000000000 / 52393261398497) ∧
    -Real.log (500000000000 / 52393261398497) ≤ (4651925167 / 1000000000) := by
  have h := checkLog_sound (w := (20393261398497 / 84393261398497)) (n := 12)
    (lo := (3081513 / 6250000)) (hi := (493042081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52393261398497 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52393261398497 / 32000000000000) = 1/(500000000000 / 52393261398497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (116298129 / 25000000) (4651925167 / 1000000000) (Real.log (52393261398497 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (52393261398497 / 500000000000) = -Real.log (500000000000 / 52393261398497) := by
    rw [show ((52393261398497 / 500000000000) : ℝ) = ((500000000000 / 52393261398497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (233006399 / 50000000) ≤ -Real.log (100000000000 / 10564960273023) ∧
    -Real.log (100000000000 / 10564960273023) ≤ (4660127987 / 1000000000) := by
  have h := checkLog_sound (w := (4164960273023 / 16964960273023)) (n := 12)
    (lo := (5012449 / 10000000)) (hi := (501244901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10564960273023 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10564960273023 / 6400000000000) = 1/(100000000000 / 10564960273023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (233006399 / 50000000) (4660127987 / 1000000000) (Real.log (10564960273023 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10564960273023 / 100000000000) = -Real.log (100000000000 / 10564960273023) := by
    rw [show ((10564960273023 / 100000000000) : ℝ) = ((100000000000 / 10564960273023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0018

end


