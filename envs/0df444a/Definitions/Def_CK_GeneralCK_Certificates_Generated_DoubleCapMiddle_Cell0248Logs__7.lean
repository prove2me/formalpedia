-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0248Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0248Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:00:07.651252+00:00
-- url     : https://prove2.me/theorems/0342a7b7-8cf9-4015-815a-b06dfc23a6af
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0248Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0249Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0248Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0249Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0250Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0251Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0252Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0253Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0254Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0248Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0249Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0250Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0251Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0252Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0253Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0254Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0248Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0249Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0250Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0251Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0252Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0253Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0254Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0248Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0249Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0250Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0251Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0252Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0253Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0254Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0248Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0248
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

theorem reflection_log_1_neg : (121932437 / 500000000) ≤ -Real.log (2560 / 3267) ∧
    -Real.log (2560 / 3267) ≤ (1950919 / 8000000) := by
  have h := checkLog_sound (w := (707 / 5827)) (n := 12)
    (lo := (121932437 / 500000000)) (hi := (1950919 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3267 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3267 / 2560) = 1/(2560 / 3267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (121932437 / 500000000) (1950919 / 8000000) (Real.log (3267 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3267 / 2560) = -Real.log (2560 / 3267) := by
    rw [show ((3267 / 2560) : ℝ) = ((2560 / 3267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (323201311 / 1000000000) ≤ -Real.log (1853 / 2560) ∧
    -Real.log (1853 / 2560) ≤ (10100041 / 31250000) := by
  have h := checkLog_sound (w := (707 / 4413)) (n := 12)
    (lo := (323201311 / 1000000000)) (hi := (10100041 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1853) = 1/(1853 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10100041 / 31250000) (-323201311 / 1000000000) (Real.log (1853 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (243405631 / 1000000000) ≤ -Real.log (5120 / 6531) ∧
    -Real.log (5120 / 6531) ≤ (3803213 / 15625000) := by
  have h := checkLog_sound (w := (1411 / 11651)) (n := 12)
    (lo := (243405631 / 1000000000)) (hi := (3803213 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6531 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6531 / 5120) = 1/(5120 / 6531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (243405631 / 1000000000) (3803213 / 15625000) (Real.log (6531 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6531 / 5120) = -Real.log (5120 / 6531) := by
    rw [show ((6531 / 5120) : ℝ) = ((5120 / 6531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16119607 / 50000000) ≤ -Real.log (3709 / 5120) ∧
    -Real.log (3709 / 5120) ≤ (322392141 / 1000000000) := by
  have h := checkLog_sound (w := (1411 / 8829)) (n := 12)
    (lo := (16119607 / 50000000)) (hi := (322392141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3709) = 1/(3709 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-322392141 / 1000000000) (-16119607 / 50000000) (Real.log (3709 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87953177 / 200000000) ≤ -Real.log (1280 / 1987) ∧
    -Real.log (1280 / 1987) ≤ (219882943 / 500000000) := by
  have h := checkLog_sound (w := (707 / 3267)) (n := 12)
    (lo := (87953177 / 200000000)) (hi := (219882943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1987 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1987 / 1280) = 1/(1280 / 1987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87953177 / 200000000) (219882943 / 500000000) (Real.log (1987 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1987 / 1280) = -Real.log (1280 / 1987) := by
    rw [show ((1987 / 1280) : ℝ) = ((1280 / 1987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (803729639 / 1000000000) ≤ -Real.log (573 / 1280) ∧
    -Real.log (573 / 1280) ≤ (803729641 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 573) = 1/(573 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-803729641 / 1000000000) (-803729639 / 1000000000) (Real.log (573 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (439010693 / 1000000000) ≤ -Real.log (2560 / 3971) ∧
    -Real.log (2560 / 3971) ≤ (219505347 / 500000000) := by
  have h := checkLog_sound (w := (1411 / 6531)) (n := 12)
    (lo := (439010693 / 1000000000)) (hi := (219505347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3971 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3971 / 2560) = 1/(2560 / 3971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (439010693 / 1000000000) (219505347 / 500000000) (Real.log (3971 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3971 / 2560) = -Real.log (2560 / 3971) := by
    rw [show ((3971 / 2560) : ℝ) = ((2560 / 3971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (801115259 / 1000000000) ≤ -Real.log (1149 / 2560) ∧
    -Real.log (1149 / 2560) ≤ (801115261 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 2429)) (n := 12)
    (lo := (107968079 / 1000000000)) (hi := (1349601 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1149) = 1/(1149 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-801115261 / 1000000000) (-801115259 / 1000000000) (Real.log (1149 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (333194011 / 1000000000) ≤ -Real.log (500000 / 697709) ∧
    -Real.log (500000 / 697709) ≤ (83298503 / 250000000) := by
  have h := checkLog_sound (w := (197709 / 1197709)) (n := 12)
    (lo := (333194011 / 1000000000)) (hi := (83298503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697709 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697709 / 500000) = 1/(500000 / 697709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (333194011 / 1000000000) (83298503 / 250000000) (Real.log (697709 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (697709 / 500000) = -Real.log (500000 / 697709) := by
    rw [show ((697709 / 500000) : ℝ) = ((500000 / 697709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31451123 / 62500000) ≤ -Real.log (302291 / 500000) ∧
    -Real.log (302291 / 500000) ≤ (503217969 / 1000000000) := by
  have h := checkLog_sound (w := (197709 / 802291)) (n := 12)
    (lo := (31451123 / 62500000)) (hi := (503217969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 302291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 302291) = 1/(302291 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-503217969 / 1000000000) (-31451123 / 62500000) (Real.log (302291 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (166908643 / 500000000) ≤ -Real.log (15625 / 21817) ∧
    -Real.log (15625 / 21817) ≤ (333817287 / 1000000000) := by
  have h := checkLog_sound (w := (3096 / 18721)) (n := 12)
    (lo := (166908643 / 500000000)) (hi := (333817287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21817 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21817 / 15625) = 1/(15625 / 21817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (166908643 / 500000000) (333817287 / 1000000000) (Real.log (21817 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (21817 / 15625) = -Real.log (15625 / 21817) := by
    rw [show ((21817 / 15625) : ℝ) = ((15625 / 21817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (100931603 / 200000000) ≤ -Real.log (9433 / 15625) ∧
    -Real.log (9433 / 15625) ≤ (15770563 / 31250000) := by
  have h := checkLog_sound (w := (3096 / 12529)) (n := 12)
    (lo := (100931603 / 200000000)) (hi := (15770563 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 9433) = 1/(9433 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-15770563 / 31250000) (-100931603 / 200000000) (Real.log (9433 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (256374051 / 1000000000) ≤ -Real.log (250000 / 323059) ∧
    -Real.log (250000 / 323059) ≤ (64093513 / 250000000) := by
  have h := checkLog_sound (w := (73059 / 573059)) (n := 12)
    (lo := (256374051 / 1000000000)) (hi := (64093513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323059 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323059 / 250000) = 1/(250000 / 323059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (256374051 / 1000000000) (64093513 / 250000000) (Real.log (323059 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (323059 / 250000) = -Real.log (250000 / 323059) := by
    rw [show ((323059 / 250000) : ℝ) = ((250000 / 323059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (172822287 / 500000000) ≤ -Real.log (176941 / 250000) ∧
    -Real.log (176941 / 250000) ≤ (13825783 / 40000000) := by
  have h := checkLog_sound (w := (73059 / 426941)) (n := 12)
    (lo := (172822287 / 500000000)) (hi := (13825783 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 176941) = 1/(176941 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-13825783 / 40000000) (-172822287 / 500000000) (Real.log (176941 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (128458187 / 500000000) ≤ -Real.log (1000000 / 1292937) ∧
    -Real.log (1000000 / 1292937) ≤ (2055331 / 8000000) := by
  have h := checkLog_sound (w := (292937 / 2292937)) (n := 12)
    (lo := (128458187 / 500000000)) (hi := (2055331 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292937 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292937 / 1000000) = 1/(1000000 / 1292937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (128458187 / 500000000) (2055331 / 8000000) (Real.log (1292937 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1292937 / 1000000) = -Real.log (1000000 / 1292937) := by
    rw [show ((1292937 / 1000000) : ℝ) = ((1000000 / 1292937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (86658877 / 250000000) ≤ -Real.log (707063 / 1000000) ∧
    -Real.log (707063 / 1000000) ≤ (346635509 / 1000000000) := by
  have h := checkLog_sound (w := (292937 / 1707063)) (n := 12)
    (lo := (86658877 / 250000000)) (hi := (346635509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707063) = 1/(707063 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-346635509 / 1000000000) (-86658877 / 250000000) (Real.log (707063 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (41820599 / 50000000) ≤ -Real.log (500000000000 / 1154035350043) ∧
    -Real.log (500000000000 / 1154035350043) ≤ (418205991 / 500000000) := by
  have h := checkLog_sound (w := (154035350043 / 2154035350043)) (n := 12)
    (lo := (179081 / 1250000)) (hi := (143264801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154035350043 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1154035350043 / 1000000000000) = 1/(500000000000 / 1154035350043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (41820599 / 50000000) (418205991 / 500000000) (Real.log (1154035350043 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1154035350043 / 500000000000) = -Real.log (500000000000 / 1154035350043) := by
    rw [show ((1154035350043 / 500000000000) : ℝ) = ((500000000000 / 1154035350043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (419237651 / 500000000) ≤ -Real.log (250000000000 / 578209477367) ∧
    -Real.log (250000000000 / 578209477367) ≤ (104809413 / 125000000) := by
  have h := checkLog_sound (w := (78209477367 / 1078209477367)) (n := 12)
    (lo := (72664061 / 500000000)) (hi := (145328123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578209477367 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(578209477367 / 500000000000) = 1/(250000000000 / 578209477367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (419237651 / 500000000) (104809413 / 125000000) (Real.log (578209477367 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (578209477367 / 250000000000) = -Real.log (250000000000 / 578209477367) := by
    rw [show ((578209477367 / 250000000000) : ℝ) = ((250000000000 / 578209477367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4816149 / 8000000) ≤ -Real.log (15625000000 / 28528135791) ∧
    -Real.log (15625000000 / 28528135791) ≤ (301009313 / 500000000) := by
  have h := checkLog_sound (w := (12903135791 / 44153135791)) (n := 12)
    (lo := (4816149 / 8000000)) (hi := (301009313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28528135791 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28528135791 / 15625000000) = 1/(15625000000 / 28528135791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4816149 / 8000000) (301009313 / 500000000) (Real.log (28528135791 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28528135791 / 15625000000) = -Real.log (15625000000 / 28528135791) := by
    rw [show ((28528135791 / 15625000000) : ℝ) = ((15625000000 / 28528135791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (301775941 / 500000000) ≤ -Real.log (500000000000 / 914301130169) ∧
    -Real.log (500000000000 / 914301130169) ≤ (603551883 / 1000000000) := by
  have h := checkLog_sound (w := (414301130169 / 1414301130169)) (n := 12)
    (lo := (301775941 / 500000000)) (hi := (603551883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((914301130169 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(914301130169 / 500000000000) = 1/(500000000000 / 914301130169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (301775941 / 500000000) (603551883 / 1000000000) (Real.log (914301130169 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (914301130169 / 500000000000) = -Real.log (500000000000 / 914301130169) := by
    rw [show ((914301130169 / 500000000000) : ℝ) = ((500000000000 / 914301130169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0248

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0249Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0249
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

theorem reflection_log_1_neg : (243405631 / 1000000000) ≤ -Real.log (5120 / 6531) ∧
    -Real.log (5120 / 6531) ≤ (3803213 / 15625000) := by
  have h := checkLog_sound (w := (1411 / 11651)) (n := 12)
    (lo := (243405631 / 1000000000)) (hi := (3803213 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6531 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6531 / 5120) = 1/(5120 / 6531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (243405631 / 1000000000) (3803213 / 15625000) (Real.log (6531 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6531 / 5120) = -Real.log (5120 / 6531) := by
    rw [show ((6531 / 5120) : ℝ) = ((5120 / 6531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16119607 / 50000000) ≤ -Real.log (3709 / 5120) ∧
    -Real.log (3709 / 5120) ≤ (322392141 / 1000000000) := by
  have h := checkLog_sound (w := (1411 / 8829)) (n := 12)
    (lo := (16119607 / 50000000)) (hi := (322392141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3709) = 1/(3709 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-322392141 / 1000000000) (-16119607 / 50000000) (Real.log (3709 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (121473089 / 500000000) ≤ -Real.log (40 / 51) ∧
    -Real.log (40 / 51) ≤ (242946179 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 91)) (n := 12)
    (lo := (121473089 / 500000000)) (hi := (242946179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51 / 40) = 1/(40 / 51) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (121473089 / 500000000) (242946179 / 1000000000) (Real.log (51 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (51 / 40) = -Real.log (40 / 51) := by
    rw [show ((51 / 40) : ℝ) = ((40 / 51) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (40197953 / 125000000) ≤ -Real.log (29 / 40) ∧
    -Real.log (29 / 40) ≤ (2572669 / 8000000) := by
  have h := checkLog_sound (w := (11 / 69)) (n := 12)
    (lo := (40197953 / 125000000)) (hi := (2572669 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 29) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 29) = 1/(29 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2572669 / 8000000) (-40197953 / 125000000) (Real.log (29 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (439010693 / 1000000000) ≤ -Real.log (2560 / 3971) ∧
    -Real.log (2560 / 3971) ≤ (219505347 / 500000000) := by
  have h := checkLog_sound (w := (1411 / 6531)) (n := 12)
    (lo := (439010693 / 1000000000)) (hi := (219505347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3971 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3971 / 2560) = 1/(2560 / 3971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (439010693 / 1000000000) (219505347 / 500000000) (Real.log (3971 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3971 / 2560) = -Real.log (2560 / 3971) := by
    rw [show ((3971 / 2560) : ℝ) = ((2560 / 3971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (801115259 / 1000000000) ≤ -Real.log (1149 / 2560) ∧
    -Real.log (1149 / 2560) ≤ (801115261 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 2429)) (n := 12)
    (lo := (107968079 / 1000000000)) (hi := (1349601 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1149) = 1/(1149 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-801115261 / 1000000000) (-801115259 / 1000000000) (Real.log (1149 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (43825493 / 100000000) ≤ -Real.log (20 / 31) ∧
    -Real.log (20 / 31) ≤ (438254931 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 51)) (n := 12)
    (lo := (43825493 / 100000000)) (hi := (438254931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31 / 20) = 1/(20 / 31) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (43825493 / 100000000) (438254931 / 1000000000) (Real.log (31 / 20)) := by
  have h := reflection_log_7_neg
  have he : Real.log (31 / 20) = -Real.log (20 / 31) := by
    rw [show ((31 / 20) : ℝ) = ((20 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (159701539 / 200000000) ≤ -Real.log (9 / 20) ∧
    -Real.log (9 / 20) ≤ (798507697 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10 / 9) = 1/(9 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-798507697 / 1000000000) (-159701539 / 200000000) (Real.log (9 / 20)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166285891 / 500000000) ≤ -Real.log (20000 / 27891) ∧
    -Real.log (20000 / 27891) ≤ (332571783 / 1000000000) := by
  have h := checkLog_sound (w := (7891 / 47891)) (n := 12)
    (lo := (166285891 / 500000000)) (hi := (332571783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27891 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27891 / 20000) = 1/(20000 / 27891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166285891 / 500000000) (332571783 / 1000000000) (Real.log (27891 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (27891 / 20000) = -Real.log (20000 / 27891) := by
    rw [show ((27891 / 20000) : ℝ) = ((20000 / 27891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (100356659 / 200000000) ≤ -Real.log (12109 / 20000) ∧
    -Real.log (12109 / 20000) ≤ (1960091 / 3906250) := by
  have h := checkLog_sound (w := (7891 / 32109)) (n := 12)
    (lo := (100356659 / 200000000)) (hi := (1960091 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 12109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 12109) = 1/(12109 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1960091 / 3906250) (-100356659 / 200000000) (Real.log (12109 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (41649341 / 125000000) ≤ -Real.log (1000000 / 1395419) ∧
    -Real.log (1000000 / 1395419) ≤ (333194729 / 1000000000) := by
  have h := checkLog_sound (w := (395419 / 2395419)) (n := 12)
    (lo := (41649341 / 125000000)) (hi := (333194729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1395419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1395419 / 1000000) = 1/(1000000 / 1395419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (41649341 / 125000000) (333194729 / 1000000000) (Real.log (1395419 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1395419 / 1000000) = -Real.log (1000000 / 1395419) := by
    rw [show ((1395419 / 1000000) : ℝ) = ((1000000 / 1395419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (251609811 / 500000000) ≤ -Real.log (604581 / 1000000) ∧
    -Real.log (604581 / 1000000) ≤ (503219623 / 1000000000) := by
  have h := checkLog_sound (w := (395419 / 1604581)) (n := 12)
    (lo := (251609811 / 500000000)) (hi := (503219623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 604581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 604581) = 1/(604581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-503219623 / 1000000000) (-251609811 / 500000000) (Real.log (604581 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (255832207 / 1000000000) ≤ -Real.log (62500 / 80721) ∧
    -Real.log (62500 / 80721) ≤ (15989513 / 62500000) := by
  have h := checkLog_sound (w := (18221 / 143221)) (n := 12)
    (lo := (255832207 / 1000000000)) (hi := (15989513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80721 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80721 / 62500) = 1/(62500 / 80721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (255832207 / 1000000000) (15989513 / 62500000) (Real.log (80721 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (80721 / 62500) = -Real.log (62500 / 80721) := by
    rw [show ((80721 / 62500) : ℝ) = ((62500 / 80721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (10770501 / 31250000) ≤ -Real.log (44279 / 62500) ∧
    -Real.log (44279 / 62500) ≤ (344656033 / 1000000000) := by
  have h := checkLog_sound (w := (18221 / 106779)) (n := 12)
    (lo := (10770501 / 31250000)) (hi := (344656033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44279) = 1/(44279 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-344656033 / 1000000000) (-10770501 / 31250000) (Real.log (44279 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10254993 / 40000000) ≤ -Real.log (1000000 / 1292237) ∧
    -Real.log (1000000 / 1292237) ≤ (128187413 / 500000000) := by
  have h := checkLog_sound (w := (292237 / 2292237)) (n := 12)
    (lo := (10254993 / 40000000)) (hi := (128187413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292237 / 1000000) = 1/(1000000 / 1292237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10254993 / 40000000) (128187413 / 500000000) (Real.log (1292237 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1292237 / 1000000) = -Real.log (1000000 / 1292237) := by
    rw [show ((1292237 / 1000000) : ℝ) = ((1000000 / 1292237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (345645987 / 1000000000) ≤ -Real.log (707763 / 1000000) ∧
    -Real.log (707763 / 1000000) ≤ (86411497 / 250000000) := by
  have h := checkLog_sound (w := (292237 / 1707763)) (n := 12)
    (lo := (345645987 / 1000000000)) (hi := (86411497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707763) = 1/(707763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-86411497 / 250000000) (-345645987 / 1000000000) (Real.log (707763 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (834355077 / 1000000000) ≤ -Real.log (500000000000 / 1151664051531) ∧
    -Real.log (500000000000 / 1151664051531) ≤ (834355079 / 1000000000) := by
  have h := checkLog_sound (w := (151664051531 / 2151664051531)) (n := 12)
    (lo := (141207897 / 1000000000)) (hi := (70603949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151664051531 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1151664051531 / 1000000000000) = 1/(500000000000 / 1151664051531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (834355077 / 1000000000) (834355079 / 1000000000) (Real.log (1151664051531 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1151664051531 / 500000000000) = -Real.log (500000000000 / 1151664051531) := by
    rw [show ((1151664051531 / 500000000000) : ℝ) = ((500000000000 / 1151664051531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (16728287 / 20000000) ≤ -Real.log (500000000000 / 1154038085881) ∧
    -Real.log (500000000000 / 1154038085881) ≤ (52275897 / 62500000) := by
  have h := checkLog_sound (w := (154038085881 / 2154038085881)) (n := 12)
    (lo := (14326717 / 100000000)) (hi := (143267171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154038085881 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1154038085881 / 1000000000000) = 1/(500000000000 / 1154038085881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (16728287 / 20000000) (52275897 / 62500000) (Real.log (1154038085881 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1154038085881 / 500000000000) = -Real.log (500000000000 / 1154038085881) := by
    rw [show ((1154038085881 / 500000000000) : ℝ) = ((500000000000 / 1154038085881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7506103 / 12500000) ≤ -Real.log (500000000000 / 911504324849) ∧
    -Real.log (500000000000 / 911504324849) ≤ (600488241 / 1000000000) := by
  have h := checkLog_sound (w := (411504324849 / 1411504324849)) (n := 12)
    (lo := (7506103 / 12500000)) (hi := (600488241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911504324849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911504324849 / 500000000000) = 1/(500000000000 / 911504324849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (7506103 / 12500000) (600488241 / 1000000000) (Real.log (911504324849 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (911504324849 / 500000000000) = -Real.log (500000000000 / 911504324849) := by
    rw [show ((911504324849 / 500000000000) : ℝ) = ((500000000000 / 911504324849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (150505203 / 250000000) ≤ -Real.log (125000000000 / 228225585401) ∧
    -Real.log (125000000000 / 228225585401) ≤ (602020813 / 1000000000) := by
  have h := checkLog_sound (w := (103225585401 / 353225585401)) (n := 12)
    (lo := (150505203 / 250000000)) (hi := (602020813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228225585401 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228225585401 / 125000000000) = 1/(125000000000 / 228225585401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (150505203 / 250000000) (602020813 / 1000000000) (Real.log (228225585401 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (228225585401 / 125000000000) = -Real.log (125000000000 / 228225585401) := by
    rw [show ((228225585401 / 125000000000) : ℝ) = ((125000000000 / 228225585401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0249

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0250Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0250
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

theorem reflection_log_1_neg : (121473089 / 500000000) ≤ -Real.log (40 / 51) ∧
    -Real.log (40 / 51) ≤ (242946179 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 91)) (n := 12)
    (lo := (121473089 / 500000000)) (hi := (242946179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51 / 40) = 1/(40 / 51) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (121473089 / 500000000) (242946179 / 1000000000) (Real.log (51 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (51 / 40) = -Real.log (40 / 51) := by
    rw [show ((51 / 40) : ℝ) = ((40 / 51) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (40197953 / 125000000) ≤ -Real.log (29 / 40) ∧
    -Real.log (29 / 40) ≤ (2572669 / 8000000) := by
  have h := checkLog_sound (w := (11 / 69)) (n := 12)
    (lo := (40197953 / 125000000)) (hi := (2572669 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 29) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 29) = 1/(29 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2572669 / 8000000) (-40197953 / 125000000) (Real.log (29 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (121243257 / 500000000) ≤ -Real.log (1024 / 1305) ∧
    -Real.log (1024 / 1305) ≤ (48497303 / 200000000) := by
  have h := checkLog_sound (w := (281 / 2329)) (n := 12)
    (lo := (121243257 / 500000000)) (hi := (48497303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305 / 1024) = 1/(1024 / 1305) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (121243257 / 500000000) (48497303 / 200000000) (Real.log (1305 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1305 / 1024) = -Real.log (1024 / 1305) := by
    rw [show ((1305 / 1024) : ℝ) = ((1024 / 1305) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (4009697 / 12500000) ≤ -Real.log (743 / 1024) ∧
    -Real.log (743 / 1024) ≤ (320775761 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 1767)) (n := 12)
    (lo := (4009697 / 12500000)) (hi := (320775761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 743) = 1/(743 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-320775761 / 1000000000) (-4009697 / 12500000) (Real.log (743 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (43825493 / 100000000) ≤ -Real.log (20 / 31) ∧
    -Real.log (20 / 31) ≤ (438254931 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 51)) (n := 12)
    (lo := (43825493 / 100000000)) (hi := (438254931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31 / 20) = 1/(20 / 31) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (43825493 / 100000000) (438254931 / 1000000000) (Real.log (31 / 20)) := by
  have h := reflection_log_5_neg
  have he : Real.log (31 / 20) = -Real.log (20 / 31) := by
    rw [show ((31 / 20) : ℝ) = ((20 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (159701539 / 200000000) ≤ -Real.log (9 / 20) ∧
    -Real.log (9 / 20) ≤ (798507697 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10 / 9) = 1/(9 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-798507697 / 1000000000) (-159701539 / 200000000) (Real.log (9 / 20)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (109374649 / 250000000) ≤ -Real.log (512 / 793) ∧
    -Real.log (512 / 793) ≤ (437498597 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 1305)) (n := 12)
    (lo := (109374649 / 250000000)) (hi := (437498597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793 / 512) = 1/(512 / 793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (109374649 / 250000000) (437498597 / 1000000000) (Real.log (793 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (793 / 512) = -Real.log (512 / 793) := by
    rw [show ((793 / 512) : ℝ) = ((512 / 793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (795906913 / 1000000000) ≤ -Real.log (231 / 512) ∧
    -Real.log (231 / 512) ≤ (159181383 / 200000000) := by
  have h := checkLog_sound (w := (25 / 487)) (n := 12)
    (lo := (102759733 / 1000000000)) (hi := (51379867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 231) = 1/(231 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159181383 / 200000000) (-795906913 / 1000000000) (Real.log (231 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10373389 / 31250000) ≤ -Real.log (1000000 / 1393681) ∧
    -Real.log (1000000 / 1393681) ≤ (331948449 / 1000000000) := by
  have h := checkLog_sound (w := (393681 / 2393681)) (n := 12)
    (lo := (10373389 / 31250000)) (hi := (331948449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1393681 / 1000000) = 1/(1000000 / 1393681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10373389 / 31250000) (331948449 / 1000000000) (Real.log (1393681 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1393681 / 1000000) = -Real.log (1000000 / 1393681) := by
    rw [show ((1393681 / 1000000) : ℝ) = ((1000000 / 1393681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (125087257 / 250000000) ≤ -Real.log (606319 / 1000000) ∧
    -Real.log (606319 / 1000000) ≤ (500349029 / 1000000000) := by
  have h := checkLog_sound (w := (393681 / 1606319)) (n := 12)
    (lo := (125087257 / 250000000)) (hi := (500349029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 606319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 606319) = 1/(606319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-500349029 / 1000000000) (-125087257 / 250000000) (Real.log (606319 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (332572499 / 1000000000) ≤ -Real.log (1000000 / 1394551) ∧
    -Real.log (1000000 / 1394551) ≤ (133029 / 400000) := by
  have h := checkLog_sound (w := (394551 / 2394551)) (n := 12)
    (lo := (332572499 / 1000000000)) (hi := (133029 / 400000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1394551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1394551 / 1000000) = 1/(1000000 / 1394551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (332572499 / 1000000000) (133029 / 400000) (Real.log (1394551 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1394551 / 1000000) = -Real.log (1000000 / 1394551) := by
    rw [show ((1394551 / 1000000) : ℝ) = ((1000000 / 1394551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (501784947 / 1000000000) ≤ -Real.log (605449 / 1000000) ∧
    -Real.log (605449 / 1000000) ≤ (125446237 / 250000000) := by
  have h := checkLog_sound (w := (394551 / 1605449)) (n := 12)
    (lo := (501784947 / 1000000000)) (hi := (125446237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 605449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 605449) = 1/(605449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-125446237 / 250000000) (-501784947 / 1000000000) (Real.log (605449 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51058169 / 200000000) ≤ -Real.log (1000000 / 1290837) ∧
    -Real.log (1000000 / 1290837) ≤ (127645423 / 500000000) := by
  have h := checkLog_sound (w := (290837 / 2290837)) (n := 12)
    (lo := (51058169 / 200000000)) (hi := (127645423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290837 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290837 / 1000000) = 1/(1000000 / 1290837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51058169 / 200000000) (127645423 / 500000000) (Real.log (1290837 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1290837 / 1000000) = -Real.log (1000000 / 1290837) := by
    rw [show ((1290837 / 1000000) : ℝ) = ((1000000 / 1290837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (343669877 / 1000000000) ≤ -Real.log (709163 / 1000000) ∧
    -Real.log (709163 / 1000000) ≤ (171834939 / 500000000) := by
  have h := checkLog_sound (w := (290837 / 1709163)) (n := 12)
    (lo := (343669877 / 1000000000)) (hi := (171834939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709163) = 1/(709163 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-171834939 / 500000000) (-343669877 / 1000000000) (Real.log (709163 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (127916491 / 500000000) ≤ -Real.log (1000000 / 1291537) ∧
    -Real.log (1000000 / 1291537) ≤ (255832983 / 1000000000) := by
  have h := checkLog_sound (w := (291537 / 2291537)) (n := 12)
    (lo := (127916491 / 500000000)) (hi := (255832983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1291537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1291537 / 1000000) = 1/(1000000 / 1291537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (127916491 / 500000000) (255832983 / 1000000000) (Real.log (1291537 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1291537 / 1000000) = -Real.log (1000000 / 1291537) := by
    rw [show ((1291537 / 1000000) : ℝ) = ((1000000 / 1291537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (86164361 / 250000000) ≤ -Real.log (708463 / 1000000) ∧
    -Real.log (708463 / 1000000) ≤ (68931489 / 200000000) := by
  have h := checkLog_sound (w := (291537 / 1708463)) (n := 12)
    (lo := (86164361 / 250000000)) (hi := (68931489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 708463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 708463) = 1/(708463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-68931489 / 200000000) (-86164361 / 250000000) (Real.log (708463 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (208074369 / 250000000) ≤ -Real.log (500000000000 / 1149296822299) ∧
    -Real.log (500000000000 / 1149296822299) ≤ (416148739 / 500000000) := by
  have h := checkLog_sound (w := (149296822299 / 2149296822299)) (n := 12)
    (lo := (17393787 / 125000000)) (hi := (139150297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149296822299 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1149296822299 / 1000000000000) = 1/(500000000000 / 1149296822299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (208074369 / 250000000) (416148739 / 500000000) (Real.log (1149296822299 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1149296822299 / 500000000000) = -Real.log (500000000000 / 1149296822299) := by
    rw [show ((1149296822299 / 500000000000) : ℝ) = ((500000000000 / 1149296822299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (417178723 / 500000000) ≤ -Real.log (500000000000 / 1151666779531) ∧
    -Real.log (500000000000 / 1151666779531) ≤ (104294681 / 125000000) := by
  have h := checkLog_sound (w := (151666779531 / 2151666779531)) (n := 12)
    (lo := (70605133 / 500000000)) (hi := (141210267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151666779531 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1151666779531 / 1000000000000) = 1/(500000000000 / 1151666779531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (417178723 / 500000000) (104294681 / 125000000) (Real.log (1151666779531 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1151666779531 / 500000000000) = -Real.log (500000000000 / 1151666779531) := by
    rw [show ((1151666779531 / 500000000000) : ℝ) = ((500000000000 / 1151666779531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (299480361 / 500000000) ≤ -Real.log (500000000000 / 910113048763) ∧
    -Real.log (500000000000 / 910113048763) ≤ (598960723 / 1000000000) := by
  have h := checkLog_sound (w := (410113048763 / 1410113048763)) (n := 12)
    (lo := (299480361 / 500000000)) (hi := (598960723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((910113048763 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(910113048763 / 500000000000) = 1/(500000000000 / 910113048763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (299480361 / 500000000) (598960723 / 1000000000) (Real.log (910113048763 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (910113048763 / 500000000000) = -Real.log (500000000000 / 910113048763) := by
    rw [show ((910113048763 / 500000000000) : ℝ) = ((500000000000 / 910113048763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (300245213 / 500000000) ≤ -Real.log (500000000000 / 911506317197) ∧
    -Real.log (500000000000 / 911506317197) ≤ (600490427 / 1000000000) := by
  have h := checkLog_sound (w := (411506317197 / 1411506317197)) (n := 12)
    (lo := (300245213 / 500000000)) (hi := (600490427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911506317197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911506317197 / 500000000000) = 1/(500000000000 / 911506317197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (300245213 / 500000000) (600490427 / 1000000000) (Real.log (911506317197 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (911506317197 / 500000000000) = -Real.log (500000000000 / 911506317197) := by
    rw [show ((911506317197 / 500000000000) : ℝ) = ((500000000000 / 911506317197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0250

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0251Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0251
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

theorem reflection_log_1_neg : (121243257 / 500000000) ≤ -Real.log (1024 / 1305) ∧
    -Real.log (1024 / 1305) ≤ (48497303 / 200000000) := by
  have h := checkLog_sound (w := (281 / 2329)) (n := 12)
    (lo := (121243257 / 500000000)) (hi := (48497303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305 / 1024) = 1/(1024 / 1305) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (121243257 / 500000000) (48497303 / 200000000) (Real.log (1305 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1305 / 1024) = -Real.log (1024 / 1305) := by
    rw [show ((1305 / 1024) : ℝ) = ((1024 / 1305) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (4009697 / 12500000) ≤ -Real.log (743 / 1024) ∧
    -Real.log (743 / 1024) ≤ (320775761 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 1767)) (n := 12)
    (lo := (4009697 / 12500000)) (hi := (320775761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 743) = 1/(743 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-320775761 / 1000000000) (-4009697 / 12500000) (Real.log (743 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (121013319 / 500000000) ≤ -Real.log (2560 / 3261) ∧
    -Real.log (2560 / 3261) ≤ (242026639 / 1000000000) := by
  have h := checkLog_sound (w := (701 / 5821)) (n := 12)
    (lo := (121013319 / 500000000)) (hi := (242026639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3261 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3261 / 2560) = 1/(2560 / 3261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (121013319 / 500000000) (242026639 / 1000000000) (Real.log (3261 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3261 / 2560) = -Real.log (2560 / 3261) := by
    rw [show ((3261 / 2560) : ℝ) = ((2560 / 3261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (319968549 / 1000000000) ≤ -Real.log (1859 / 2560) ∧
    -Real.log (1859 / 2560) ≤ (6399371 / 20000000) := by
  have h := checkLog_sound (w := (701 / 4419)) (n := 12)
    (lo := (319968549 / 1000000000)) (hi := (6399371 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1859) = 1/(1859 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6399371 / 20000000) (-319968549 / 1000000000) (Real.log (1859 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (109374649 / 250000000) ≤ -Real.log (512 / 793) ∧
    -Real.log (512 / 793) ≤ (437498597 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 1305)) (n := 12)
    (lo := (109374649 / 250000000)) (hi := (437498597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793 / 512) = 1/(512 / 793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (109374649 / 250000000) (437498597 / 1000000000) (Real.log (793 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (793 / 512) = -Real.log (512 / 793) := by
    rw [show ((793 / 512) : ℝ) = ((512 / 793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (795906913 / 1000000000) ≤ -Real.log (231 / 512) ∧
    -Real.log (231 / 512) ≤ (159181383 / 200000000) := by
  have h := checkLog_sound (w := (25 / 487)) (n := 12)
    (lo := (102759733 / 1000000000)) (hi := (51379867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 231) = 1/(231 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159181383 / 200000000) (-795906913 / 1000000000) (Real.log (231 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (436741689 / 1000000000) ≤ -Real.log (1280 / 1981) ∧
    -Real.log (1280 / 1981) ≤ (43674169 / 100000000) := by
  have h := checkLog_sound (w := (701 / 3261)) (n := 12)
    (lo := (436741689 / 1000000000)) (hi := (43674169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981 / 1280) = 1/(1280 / 1981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (436741689 / 1000000000) (43674169 / 100000000) (Real.log (1981 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1981 / 1280) = -Real.log (1280 / 1981) := by
    rw [show ((1981 / 1280) : ℝ) = ((1280 / 1981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (396656439 / 500000000) ≤ -Real.log (579 / 1280) ∧
    -Real.log (579 / 1280) ≤ (9916411 / 12500000) := by
  have h := checkLog_sound (w := (61 / 1219)) (n := 12)
    (lo := (50082849 / 500000000)) (hi := (100165699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 579) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 579) = 1/(579 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9916411 / 12500000) (-396656439 / 500000000) (Real.log (579 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (331325443 / 1000000000) ≤ -Real.log (1000000 / 1392813) ∧
    -Real.log (1000000 / 1392813) ≤ (82831361 / 250000000) := by
  have h := checkLog_sound (w := (392813 / 2392813)) (n := 12)
    (lo := (331325443 / 1000000000)) (hi := (82831361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1392813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1392813 / 1000000) = 1/(1000000 / 1392813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (331325443 / 1000000000) (82831361 / 250000000) (Real.log (1392813 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1392813 / 1000000) = -Real.log (1000000 / 1392813) := by
    rw [show ((1392813 / 1000000) : ℝ) = ((1000000 / 1392813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (249459231 / 500000000) ≤ -Real.log (607187 / 1000000) ∧
    -Real.log (607187 / 1000000) ≤ (498918463 / 1000000000) := by
  have h := checkLog_sound (w := (392813 / 1607187)) (n := 12)
    (lo := (249459231 / 500000000)) (hi := (498918463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 607187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 607187) = 1/(607187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-498918463 / 1000000000) (-249459231 / 500000000) (Real.log (607187 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66389833 / 200000000) ≤ -Real.log (500000 / 696841) ∧
    -Real.log (500000 / 696841) ≤ (165974583 / 500000000) := by
  have h := checkLog_sound (w := (196841 / 1196841)) (n := 12)
    (lo := (66389833 / 200000000)) (hi := (165974583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696841 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696841 / 500000) = 1/(500000 / 696841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66389833 / 200000000) (165974583 / 500000000) (Real.log (696841 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (696841 / 500000) = -Real.log (500000 / 696841) := by
    rw [show ((696841 / 500000) : ℝ) = ((500000 / 696841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (250175339 / 500000000) ≤ -Real.log (303159 / 500000) ∧
    -Real.log (303159 / 500000) ≤ (500350679 / 1000000000) := by
  have h := checkLog_sound (w := (196841 / 803159)) (n := 12)
    (lo := (250175339 / 500000000)) (hi := (500350679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 303159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 303159) = 1/(303159 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-500350679 / 1000000000) (-250175339 / 500000000) (Real.log (303159 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (63687491 / 250000000) ≤ -Real.log (1000000 / 1290139) ∧
    -Real.log (1000000 / 1290139) ≤ (50949993 / 200000000) := by
  have h := checkLog_sound (w := (290139 / 2290139)) (n := 12)
    (lo := (63687491 / 250000000)) (hi := (50949993 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290139 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290139 / 1000000) = 1/(1000000 / 1290139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (63687491 / 250000000) (50949993 / 200000000) (Real.log (1290139 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1290139 / 1000000) = -Real.log (1000000 / 1290139) := by
    rw [show ((1290139 / 1000000) : ℝ) = ((1000000 / 1290139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (171343051 / 500000000) ≤ -Real.log (709861 / 1000000) ∧
    -Real.log (709861 / 1000000) ≤ (342686103 / 1000000000) := by
  have h := checkLog_sound (w := (290139 / 1709861)) (n := 12)
    (lo := (171343051 / 500000000)) (hi := (342686103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709861) = 1/(709861 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-342686103 / 1000000000) (-171343051 / 500000000) (Real.log (709861 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (255291619 / 1000000000) ≤ -Real.log (500000 / 645419) ∧
    -Real.log (500000 / 645419) ≤ (12764581 / 50000000) := by
  have h := checkLog_sound (w := (145419 / 1145419)) (n := 12)
    (lo := (255291619 / 1000000000)) (hi := (12764581 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645419 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645419 / 500000) = 1/(500000 / 645419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (255291619 / 1000000000) (12764581 / 50000000) (Real.log (645419 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (645419 / 500000) = -Real.log (500000 / 645419) := by
    rw [show ((645419 / 500000) : ℝ) = ((500000 / 645419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (343671287 / 1000000000) ≤ -Real.log (354581 / 500000) ∧
    -Real.log (354581 / 500000) ≤ (42958911 / 125000000) := by
  have h := checkLog_sound (w := (145419 / 854581)) (n := 12)
    (lo := (343671287 / 1000000000)) (hi := (42958911 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 354581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 354581) = 1/(354581 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-42958911 / 125000000) (-343671287 / 1000000000) (Real.log (354581 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (166048781 / 200000000) ≤ -Real.log (50000000000 / 114693908137) ∧
    -Real.log (50000000000 / 114693908137) ≤ (830243907 / 1000000000) := by
  have h := checkLog_sound (w := (14693908137 / 214693908137)) (n := 12)
    (lo := (5483869 / 40000000)) (hi := (68548363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114693908137 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(114693908137 / 100000000000) = 1/(50000000000 / 114693908137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (166048781 / 200000000) (830243907 / 1000000000) (Real.log (114693908137 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (114693908137 / 50000000000) = -Real.log (50000000000 / 114693908137) := by
    rw [show ((114693908137 / 50000000000) : ℝ) = ((50000000000 / 114693908137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (832299843 / 1000000000) ≤ -Real.log (100000000000 / 229859908497) ∧
    -Real.log (100000000000 / 229859908497) ≤ (166459969 / 200000000) := by
  have h := checkLog_sound (w := (29859908497 / 429859908497)) (n := 12)
    (lo := (139152663 / 1000000000)) (hi := (17394083 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229859908497 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(229859908497 / 200000000000) = 1/(100000000000 / 229859908497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (832299843 / 1000000000) (166459969 / 200000000) (Real.log (229859908497 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (229859908497 / 100000000000) = -Real.log (100000000000 / 229859908497) := by
    rw [show ((229859908497 / 100000000000) : ℝ) = ((100000000000 / 229859908497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (597436067 / 1000000000) ≤ -Real.log (500000000000 / 908726497159) ∧
    -Real.log (500000000000 / 908726497159) ≤ (149359017 / 250000000) := by
  have h := checkLog_sound (w := (408726497159 / 1408726497159)) (n := 12)
    (lo := (597436067 / 1000000000)) (hi := (149359017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((908726497159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(908726497159 / 500000000000) = 1/(500000000000 / 908726497159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (597436067 / 1000000000) (149359017 / 250000000) (Real.log (908726497159 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (908726497159 / 500000000000) = -Real.log (500000000000 / 908726497159) := by
    rw [show ((908726497159 / 500000000000) : ℝ) = ((500000000000 / 908726497159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (598962907 / 1000000000) ≤ -Real.log (100000000000 / 182023007437) ∧
    -Real.log (100000000000 / 182023007437) ≤ (149740727 / 250000000) := by
  have h := checkLog_sound (w := (82023007437 / 282023007437)) (n := 12)
    (lo := (598962907 / 1000000000)) (hi := (149740727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182023007437 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182023007437 / 100000000000) = 1/(100000000000 / 182023007437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (598962907 / 1000000000) (149740727 / 250000000) (Real.log (182023007437 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (182023007437 / 100000000000) = -Real.log (100000000000 / 182023007437) := by
    rw [show ((182023007437 / 100000000000) : ℝ) = ((100000000000 / 182023007437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0251

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0252Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0252
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

theorem reflection_log_1_neg : (121013319 / 500000000) ≤ -Real.log (2560 / 3261) ∧
    -Real.log (2560 / 3261) ≤ (242026639 / 1000000000) := by
  have h := checkLog_sound (w := (701 / 5821)) (n := 12)
    (lo := (121013319 / 500000000)) (hi := (242026639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3261 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3261 / 2560) = 1/(2560 / 3261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (121013319 / 500000000) (242026639 / 1000000000) (Real.log (3261 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3261 / 2560) = -Real.log (2560 / 3261) := by
    rw [show ((3261 / 2560) : ℝ) = ((2560 / 3261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (319968549 / 1000000000) ≤ -Real.log (1859 / 2560) ∧
    -Real.log (1859 / 2560) ≤ (6399371 / 20000000) := by
  have h := checkLog_sound (w := (701 / 4419)) (n := 12)
    (lo := (319968549 / 1000000000)) (hi := (6399371 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1859) = 1/(1859 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6399371 / 20000000) (-319968549 / 1000000000) (Real.log (1859 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (4831331 / 20000000) ≤ -Real.log (5120 / 6519) ∧
    -Real.log (5120 / 6519) ≤ (241566551 / 1000000000) := by
  have h := checkLog_sound (w := (1399 / 11639)) (n := 12)
    (lo := (4831331 / 20000000)) (hi := (241566551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6519 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6519 / 5120) = 1/(5120 / 6519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (4831331 / 20000000) (241566551 / 1000000000) (Real.log (6519 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6519 / 5120) = -Real.log (5120 / 6519) := by
    rw [show ((6519 / 5120) : ℝ) = ((5120 / 6519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (319161989 / 1000000000) ≤ -Real.log (3721 / 5120) ∧
    -Real.log (3721 / 5120) ≤ (31916199 / 100000000) := by
  have h := checkLog_sound (w := (1399 / 8841)) (n := 12)
    (lo := (319161989 / 1000000000)) (hi := (31916199 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3721) = 1/(3721 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-31916199 / 100000000) (-319161989 / 1000000000) (Real.log (3721 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (436741689 / 1000000000) ≤ -Real.log (1280 / 1981) ∧
    -Real.log (1280 / 1981) ≤ (43674169 / 100000000) := by
  have h := checkLog_sound (w := (701 / 3261)) (n := 12)
    (lo := (436741689 / 1000000000)) (hi := (43674169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981 / 1280) = 1/(1280 / 1981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (436741689 / 1000000000) (43674169 / 100000000) (Real.log (1981 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1981 / 1280) = -Real.log (1280 / 1981) := by
    rw [show ((1981 / 1280) : ℝ) = ((1280 / 1981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (396656439 / 500000000) ≤ -Real.log (579 / 1280) ∧
    -Real.log (579 / 1280) ≤ (9916411 / 12500000) := by
  have h := checkLog_sound (w := (61 / 1219)) (n := 12)
    (lo := (50082849 / 500000000)) (hi := (100165699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 579) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 579) = 1/(579 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-9916411 / 12500000) (-396656439 / 500000000) (Real.log (579 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (435984209 / 1000000000) ≤ -Real.log (2560 / 3959) ∧
    -Real.log (2560 / 3959) ≤ (43598421 / 100000000) := by
  have h := checkLog_sound (w := (1399 / 6519)) (n := 12)
    (lo := (435984209 / 1000000000)) (hi := (43598421 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3959 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3959 / 2560) = 1/(2560 / 3959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (435984209 / 1000000000) (43598421 / 100000000) (Real.log (3959 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3959 / 2560) = -Real.log (2560 / 3959) := by
    rw [show ((3959 / 2560) : ℝ) = ((2560 / 3959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (158145111 / 200000000) ≤ -Real.log (1161 / 2560) ∧
    -Real.log (1161 / 2560) ≤ (790725557 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 2441)) (n := 12)
    (lo := (780627 / 8000000)) (hi := (12197297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1161) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1161) = 1/(1161 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-790725557 / 1000000000) (-158145111 / 200000000) (Real.log (1161 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (330702049 / 1000000000) ≤ -Real.log (200000 / 278389) ∧
    -Real.log (200000 / 278389) ≤ (6614041 / 20000000) := by
  have h := checkLog_sound (w := (78389 / 478389)) (n := 12)
    (lo := (330702049 / 1000000000)) (hi := (6614041 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278389 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(278389 / 200000) = 1/(200000 / 278389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (330702049 / 1000000000) (6614041 / 20000000) (Real.log (278389 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (278389 / 200000) = -Real.log (200000 / 278389) := by
    rw [show ((278389 / 200000) : ℝ) = ((200000 / 278389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (24874497 / 50000000) ≤ -Real.log (121611 / 200000) ∧
    -Real.log (121611 / 200000) ≤ (497489941 / 1000000000) := by
  have h := checkLog_sound (w := (78389 / 321611)) (n := 12)
    (lo := (24874497 / 50000000)) (hi := (497489941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 121611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 121611) = 1/(121611 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-497489941 / 1000000000) (-24874497 / 50000000) (Real.log (121611 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (331326161 / 1000000000) ≤ -Real.log (500000 / 696407) ∧
    -Real.log (500000 / 696407) ≤ (165663081 / 500000000) := by
  have h := checkLog_sound (w := (196407 / 1196407)) (n := 12)
    (lo := (331326161 / 1000000000)) (hi := (165663081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696407 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696407 / 500000) = 1/(500000 / 696407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (331326161 / 1000000000) (165663081 / 500000000) (Real.log (696407 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (696407 / 500000) = -Real.log (500000 / 696407) := by
    rw [show ((696407 / 500000) : ℝ) = ((500000 / 696407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (498920109 / 1000000000) ≤ -Real.log (303593 / 500000) ∧
    -Real.log (303593 / 500000) ≤ (49892011 / 100000000) := by
  have h := checkLog_sound (w := (196407 / 803593)) (n := 12)
    (lo := (498920109 / 1000000000)) (hi := (49892011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 303593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 303593) = 1/(303593 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-49892011 / 100000000) (-498920109 / 1000000000) (Real.log (303593 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (254208791 / 1000000000) ≤ -Real.log (1000000 / 1289441) ∧
    -Real.log (1000000 / 1289441) ≤ (31776099 / 125000000) := by
  have h := checkLog_sound (w := (289441 / 2289441)) (n := 12)
    (lo := (254208791 / 1000000000)) (hi := (31776099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289441 / 1000000) = 1/(1000000 / 1289441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (254208791 / 1000000000) (31776099 / 125000000) (Real.log (1289441 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1289441 / 1000000) = -Real.log (1000000 / 1289441) := by
    rw [show ((1289441 / 1000000) : ℝ) = ((1000000 / 1289441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (170851647 / 500000000) ≤ -Real.log (710559 / 1000000) ∧
    -Real.log (710559 / 1000000) ≤ (68340659 / 200000000) := by
  have h := checkLog_sound (w := (289441 / 1710559)) (n := 12)
    (lo := (170851647 / 500000000)) (hi := (68340659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 710559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 710559) = 1/(710559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-68340659 / 200000000) (-170851647 / 500000000) (Real.log (710559 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (254750739 / 1000000000) ≤ -Real.log (50000 / 64507) ∧
    -Real.log (50000 / 64507) ≤ (12737537 / 50000000) := by
  have h := checkLog_sound (w := (14507 / 114507)) (n := 12)
    (lo := (254750739 / 1000000000)) (hi := (12737537 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64507 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64507 / 50000) = 1/(50000 / 64507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (254750739 / 1000000000) (12737537 / 50000000) (Real.log (64507 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (64507 / 50000) = -Real.log (50000 / 64507) := by
    rw [show ((64507 / 50000) : ℝ) = ((50000 / 64507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (342687511 / 1000000000) ≤ -Real.log (35493 / 50000) ∧
    -Real.log (35493 / 50000) ≤ (42835939 / 125000000) := by
  have h := checkLog_sound (w := (14507 / 85493)) (n := 12)
    (lo := (342687511 / 1000000000)) (hi := (42835939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 35493) = 1/(35493 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-42835939 / 125000000) (-342687511 / 1000000000) (Real.log (35493 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (828191989 / 1000000000) ≤ -Real.log (250000000000 / 572294035901) ∧
    -Real.log (250000000000 / 572294035901) ≤ (828191991 / 1000000000) := by
  have h := checkLog_sound (w := (72294035901 / 1072294035901)) (n := 12)
    (lo := (135044809 / 1000000000)) (hi := (13504481 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572294035901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572294035901 / 500000000000) = 1/(250000000000 / 572294035901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (828191989 / 1000000000) (828191991 / 1000000000) (Real.log (572294035901 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (572294035901 / 250000000000) = -Real.log (250000000000 / 572294035901) := by
    rw [show ((572294035901 / 250000000000) : ℝ) = ((250000000000 / 572294035901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (83024627 / 100000000) ≤ -Real.log (62500000000 / 143367724223) ∧
    -Real.log (62500000000 / 143367724223) ≤ (6486299 / 7812500) := by
  have h := checkLog_sound (w := (18367724223 / 268367724223)) (n := 12)
    (lo := (13709909 / 100000000)) (hi := (137099091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143367724223 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(143367724223 / 125000000000) = 1/(62500000000 / 143367724223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (83024627 / 100000000) (6486299 / 7812500) (Real.log (143367724223 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (143367724223 / 62500000000) = -Real.log (62500000000 / 143367724223) := by
    rw [show ((143367724223 / 62500000000) : ℝ) = ((62500000000 / 143367724223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (119182417 / 200000000) ≤ -Real.log (125000000000 / 226835667411) ∧
    -Real.log (125000000000 / 226835667411) ≤ (297956043 / 500000000) := by
  have h := checkLog_sound (w := (101835667411 / 351835667411)) (n := 12)
    (lo := (119182417 / 200000000)) (hi := (297956043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226835667411 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226835667411 / 125000000000) = 1/(125000000000 / 226835667411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (119182417 / 200000000) (297956043 / 500000000) (Real.log (226835667411 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (226835667411 / 125000000000) = -Real.log (125000000000 / 226835667411) := by
    rw [show ((226835667411 / 125000000000) : ℝ) = ((125000000000 / 226835667411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (597438251 / 1000000000) ≤ -Real.log (500000000000 / 908728481673) ∧
    -Real.log (500000000000 / 908728481673) ≤ (149359563 / 250000000) := by
  have h := checkLog_sound (w := (408728481673 / 1408728481673)) (n := 12)
    (lo := (597438251 / 1000000000)) (hi := (149359563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((908728481673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(908728481673 / 500000000000) = 1/(500000000000 / 908728481673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (597438251 / 1000000000) (149359563 / 250000000) (Real.log (908728481673 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (908728481673 / 500000000000) = -Real.log (500000000000 / 908728481673) := by
    rw [show ((908728481673 / 500000000000) : ℝ) = ((500000000000 / 908728481673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0252

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0253Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0253
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

theorem reflection_log_1_neg : (4831331 / 20000000) ≤ -Real.log (5120 / 6519) ∧
    -Real.log (5120 / 6519) ≤ (241566551 / 1000000000) := by
  have h := checkLog_sound (w := (1399 / 11639)) (n := 12)
    (lo := (4831331 / 20000000)) (hi := (241566551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6519 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6519 / 5120) = 1/(5120 / 6519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (4831331 / 20000000) (241566551 / 1000000000) (Real.log (6519 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6519 / 5120) = -Real.log (5120 / 6519) := by
    rw [show ((6519 / 5120) : ℝ) = ((5120 / 6519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (319161989 / 1000000000) ≤ -Real.log (3721 / 5120) ∧
    -Real.log (3721 / 5120) ≤ (31916199 / 100000000) := by
  have h := checkLog_sound (w := (1399 / 8841)) (n := 12)
    (lo := (319161989 / 1000000000)) (hi := (31916199 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3721) = 1/(3721 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-31916199 / 100000000) (-319161989 / 1000000000) (Real.log (3721 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (241106251 / 1000000000) ≤ -Real.log (1280 / 1629) ∧
    -Real.log (1280 / 1629) ≤ (60276563 / 250000000) := by
  have h := checkLog_sound (w := (349 / 2909)) (n := 12)
    (lo := (241106251 / 1000000000)) (hi := (60276563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1629 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1629 / 1280) = 1/(1280 / 1629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (241106251 / 1000000000) (60276563 / 250000000) (Real.log (1629 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1629 / 1280) = -Real.log (1280 / 1629) := by
    rw [show ((1629 / 1280) : ℝ) = ((1280 / 1629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (318356079 / 1000000000) ≤ -Real.log (931 / 1280) ∧
    -Real.log (931 / 1280) ≤ (3979451 / 12500000) := by
  have h := checkLog_sound (w := (349 / 2211)) (n := 12)
    (lo := (318356079 / 1000000000)) (hi := (3979451 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 931) = 1/(931 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3979451 / 12500000) (-318356079 / 1000000000) (Real.log (931 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (435984209 / 1000000000) ≤ -Real.log (2560 / 3959) ∧
    -Real.log (2560 / 3959) ≤ (43598421 / 100000000) := by
  have h := checkLog_sound (w := (1399 / 6519)) (n := 12)
    (lo := (435984209 / 1000000000)) (hi := (43598421 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3959 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3959 / 2560) = 1/(2560 / 3959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (435984209 / 1000000000) (43598421 / 100000000) (Real.log (3959 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3959 / 2560) = -Real.log (2560 / 3959) := by
    rw [show ((3959 / 2560) : ℝ) = ((2560 / 3959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (158145111 / 200000000) ≤ -Real.log (1161 / 2560) ∧
    -Real.log (1161 / 2560) ≤ (790725557 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 2441)) (n := 12)
    (lo := (780627 / 8000000)) (hi := (12197297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1161) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1161) = 1/(1161 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-790725557 / 1000000000) (-158145111 / 200000000) (Real.log (1161 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (87045231 / 200000000) ≤ -Real.log (640 / 989) ∧
    -Real.log (640 / 989) ≤ (108806539 / 250000000) := by
  have h := checkLog_sound (w := (349 / 1629)) (n := 12)
    (lo := (87045231 / 200000000)) (hi := (108806539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989 / 640) = 1/(640 / 989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (87045231 / 200000000) (108806539 / 250000000) (Real.log (989 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (989 / 640) = -Real.log (640 / 989) := by
    rw [show ((989 / 640) : ℝ) = ((640 / 989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (197036227 / 250000000) ≤ -Real.log (291 / 640) ∧
    -Real.log (291 / 640) ≤ (78814491 / 100000000) := by
  have h := checkLog_sound (w := (29 / 611)) (n := 12)
    (lo := (2968679 / 31250000)) (hi := (94997729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 291) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 291) = 1/(291 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-78814491 / 100000000) (-197036227 / 250000000) (Real.log (291 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (330078267 / 1000000000) ≤ -Real.log (1000000 / 1391077) ∧
    -Real.log (1000000 / 1391077) ≤ (82519567 / 250000000) := by
  have h := checkLog_sound (w := (391077 / 2391077)) (n := 12)
    (lo := (330078267 / 1000000000)) (hi := (82519567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391077 / 1000000) = 1/(1000000 / 1391077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (330078267 / 1000000000) (82519567 / 250000000) (Real.log (1391077 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1391077 / 1000000) = -Real.log (1000000 / 1391077) := by
    rw [show ((1391077 / 1000000) : ℝ) = ((1000000 / 1391077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (15501983 / 31250000) ≤ -Real.log (608923 / 1000000) ∧
    -Real.log (608923 / 1000000) ≤ (496063457 / 1000000000) := by
  have h := checkLog_sound (w := (391077 / 1608923)) (n := 12)
    (lo := (15501983 / 31250000)) (hi := (496063457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 608923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 608923) = 1/(608923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-496063457 / 1000000000) (-15501983 / 31250000) (Real.log (608923 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20668923 / 62500000) ≤ -Real.log (500000 / 695973) ∧
    -Real.log (500000 / 695973) ≤ (330702769 / 1000000000) := by
  have h := checkLog_sound (w := (195973 / 1195973)) (n := 12)
    (lo := (20668923 / 62500000)) (hi := (330702769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695973 / 500000) = 1/(500000 / 695973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20668923 / 62500000) (330702769 / 1000000000) (Real.log (695973 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (695973 / 500000) = -Real.log (500000 / 695973) := by
    rw [show ((695973 / 500000) : ℝ) = ((500000 / 695973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (99498317 / 200000000) ≤ -Real.log (304027 / 500000) ∧
    -Real.log (304027 / 500000) ≤ (248745793 / 500000000) := by
  have h := checkLog_sound (w := (195973 / 804027)) (n := 12)
    (lo := (99498317 / 200000000)) (hi := (248745793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 304027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 304027) = 1/(304027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-248745793 / 500000000) (-99498317 / 200000000) (Real.log (304027 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2536681 / 10000000) ≤ -Real.log (125000 / 161093) ∧
    -Real.log (125000 / 161093) ≤ (253668101 / 1000000000) := by
  have h := checkLog_sound (w := (36093 / 286093)) (n := 12)
    (lo := (2536681 / 10000000)) (hi := (253668101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161093 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161093 / 125000) = 1/(125000 / 161093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2536681 / 10000000) (253668101 / 1000000000) (Real.log (161093 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (161093 / 125000) = -Real.log (125000 / 161093) := by
    rw [show ((161093 / 125000) : ℝ) = ((125000 / 161093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (340722857 / 1000000000) ≤ -Real.log (88907 / 125000) ∧
    -Real.log (88907 / 125000) ≤ (170361429 / 500000000) := by
  have h := checkLog_sound (w := (36093 / 213907)) (n := 12)
    (lo := (340722857 / 1000000000)) (hi := (170361429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88907) = 1/(88907 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-170361429 / 500000000) (-340722857 / 1000000000) (Real.log (88907 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (127104783 / 500000000) ≤ -Real.log (500000 / 644721) ∧
    -Real.log (500000 / 644721) ≤ (254209567 / 1000000000) := by
  have h := checkLog_sound (w := (144721 / 1144721)) (n := 12)
    (lo := (127104783 / 500000000)) (hi := (254209567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644721 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644721 / 500000) = 1/(500000 / 644721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (127104783 / 500000000) (254209567 / 1000000000) (Real.log (644721 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (644721 / 500000) = -Real.log (500000 / 644721) := by
    rw [show ((644721 / 500000) : ℝ) = ((500000 / 644721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (170852351 / 500000000) ≤ -Real.log (355279 / 500000) ∧
    -Real.log (355279 / 500000) ≤ (341704703 / 1000000000) := by
  have h := checkLog_sound (w := (144721 / 855279)) (n := 12)
    (lo := (170852351 / 500000000)) (hi := (341704703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 355279) = 1/(355279 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-341704703 / 1000000000) (-170852351 / 500000000) (Real.log (355279 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (413070861 / 500000000) ≤ -Real.log (50000000000 / 114224376481) ∧
    -Real.log (50000000000 / 114224376481) ≤ (206535431 / 250000000) := by
  have h := checkLog_sound (w := (14224376481 / 214224376481)) (n := 12)
    (lo := (66497271 / 500000000)) (hi := (132994543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114224376481 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(114224376481 / 100000000000) = 1/(50000000000 / 114224376481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (413070861 / 500000000) (206535431 / 250000000) (Real.log (114224376481 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (114224376481 / 50000000000) = -Real.log (50000000000 / 114224376481) := by
    rw [show ((114224376481 / 50000000000) : ℝ) = ((50000000000 / 114224376481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (51762147 / 62500000) ≤ -Real.log (250000000000 / 572295388239) ∧
    -Real.log (250000000000 / 572295388239) ≤ (414097177 / 500000000) := by
  have h := checkLog_sound (w := (72295388239 / 1072295388239)) (n := 12)
    (lo := (33761793 / 250000000)) (hi := (135047173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572295388239 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572295388239 / 500000000000) = 1/(250000000000 / 572295388239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (51762147 / 62500000) (414097177 / 500000000) (Real.log (572295388239 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (572295388239 / 250000000000) = -Real.log (250000000000 / 572295388239) := by
    rw [show ((572295388239 / 250000000000) : ℝ) = ((250000000000 / 572295388239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (297195479 / 500000000) ≤ -Real.log (500000000000 / 905963534929) ∧
    -Real.log (500000000000 / 905963534929) ≤ (594390959 / 1000000000) := by
  have h := checkLog_sound (w := (405963534929 / 1405963534929)) (n := 12)
    (lo := (297195479 / 500000000)) (hi := (594390959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((905963534929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(905963534929 / 500000000000) = 1/(500000000000 / 905963534929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (297195479 / 500000000) (594390959 / 1000000000) (Real.log (905963534929 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (905963534929 / 500000000000) = -Real.log (500000000000 / 905963534929) := by
    rw [show ((905963534929 / 500000000000) : ℝ) = ((500000000000 / 905963534929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (148978567 / 250000000) ≤ -Real.log (500000000000 / 907344650261) ∧
    -Real.log (500000000000 / 907344650261) ≤ (595914269 / 1000000000) := by
  have h := checkLog_sound (w := (407344650261 / 1407344650261)) (n := 12)
    (lo := (148978567 / 250000000)) (hi := (595914269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((907344650261 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(907344650261 / 500000000000) = 1/(500000000000 / 907344650261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (148978567 / 250000000) (595914269 / 1000000000) (Real.log (907344650261 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (907344650261 / 500000000000) = -Real.log (500000000000 / 907344650261) := by
    rw [show ((907344650261 / 500000000000) : ℝ) = ((500000000000 / 907344650261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0253

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0254Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0254
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

theorem reflection_log_1_neg : (241106251 / 1000000000) ≤ -Real.log (1280 / 1629) ∧
    -Real.log (1280 / 1629) ≤ (60276563 / 250000000) := by
  have h := checkLog_sound (w := (349 / 2909)) (n := 12)
    (lo := (241106251 / 1000000000)) (hi := (60276563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1629 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1629 / 1280) = 1/(1280 / 1629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (241106251 / 1000000000) (60276563 / 250000000) (Real.log (1629 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1629 / 1280) = -Real.log (1280 / 1629) := by
    rw [show ((1629 / 1280) : ℝ) = ((1280 / 1629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (318356079 / 1000000000) ≤ -Real.log (931 / 1280) ∧
    -Real.log (931 / 1280) ≤ (3979451 / 12500000) := by
  have h := checkLog_sound (w := (349 / 2211)) (n := 12)
    (lo := (318356079 / 1000000000)) (hi := (3979451 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 931) = 1/(931 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3979451 / 12500000) (-318356079 / 1000000000) (Real.log (931 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12032287 / 50000000) ≤ -Real.log (5120 / 6513) ∧
    -Real.log (5120 / 6513) ≤ (240645741 / 1000000000) := by
  have h := checkLog_sound (w := (1393 / 11633)) (n := 12)
    (lo := (12032287 / 50000000)) (hi := (240645741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6513 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6513 / 5120) = 1/(5120 / 6513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12032287 / 50000000) (240645741 / 1000000000) (Real.log (6513 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6513 / 5120) = -Real.log (5120 / 6513) := by
    rw [show ((6513 / 5120) : ℝ) = ((5120 / 6513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (158775409 / 500000000) ≤ -Real.log (3727 / 5120) ∧
    -Real.log (3727 / 5120) ≤ (317550819 / 1000000000) := by
  have h := checkLog_sound (w := (1393 / 8847)) (n := 12)
    (lo := (158775409 / 500000000)) (hi := (317550819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3727) = 1/(3727 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-317550819 / 1000000000) (-158775409 / 500000000) (Real.log (3727 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87045231 / 200000000) ≤ -Real.log (640 / 989) ∧
    -Real.log (640 / 989) ≤ (108806539 / 250000000) := by
  have h := checkLog_sound (w := (349 / 1629)) (n := 12)
    (lo := (87045231 / 200000000)) (hi := (108806539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989 / 640) = 1/(640 / 989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87045231 / 200000000) (108806539 / 250000000) (Real.log (989 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (989 / 640) = -Real.log (640 / 989) := by
    rw [show ((989 / 640) : ℝ) = ((640 / 989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (197036227 / 250000000) ≤ -Real.log (291 / 640) ∧
    -Real.log (291 / 640) ≤ (78814491 / 100000000) := by
  have h := checkLog_sound (w := (29 / 611)) (n := 12)
    (lo := (2968679 / 31250000)) (hi := (94997729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 291) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 291) = 1/(291 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-78814491 / 100000000) (-197036227 / 250000000) (Real.log (291 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (17378701 / 40000000) ≤ -Real.log (2560 / 3953) ∧
    -Real.log (2560 / 3953) ≤ (217233763 / 500000000) := by
  have h := checkLog_sound (w := (1393 / 6513)) (n := 12)
    (lo := (17378701 / 40000000)) (hi := (217233763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3953 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3953 / 2560) = 1/(2560 / 3953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (17378701 / 40000000) (217233763 / 500000000) (Real.log (3953 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3953 / 2560) = -Real.log (2560 / 3953) := by
    rw [show ((3953 / 2560) : ℝ) = ((2560 / 3953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (98196363 / 125000000) ≤ -Real.log (1167 / 2560) ∧
    -Real.log (1167 / 2560) ≤ (392785453 / 500000000) := by
  have h := checkLog_sound (w := (113 / 2447)) (n := 12)
    (lo := (23105931 / 250000000)) (hi := (3696949 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1167) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1167) = 1/(1167 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-392785453 / 500000000) (-98196363 / 125000000) (Real.log (1167 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (164727407 / 500000000) ≤ -Real.log (100000 / 139021) ∧
    -Real.log (100000 / 139021) ≤ (65890963 / 200000000) := by
  have h := checkLog_sound (w := (39021 / 239021)) (n := 12)
    (lo := (164727407 / 500000000)) (hi := (65890963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139021 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139021 / 100000) = 1/(100000 / 139021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (164727407 / 500000000) (65890963 / 200000000) (Real.log (139021 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (139021 / 100000) = -Real.log (100000 / 139021) := by
    rw [show ((139021 / 100000) : ℝ) = ((100000 / 139021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (494640643 / 1000000000) ≤ -Real.log (60979 / 100000) ∧
    -Real.log (60979 / 100000) ≤ (123660161 / 250000000) := by
  have h := checkLog_sound (w := (39021 / 160979)) (n := 12)
    (lo := (494640643 / 1000000000)) (hi := (123660161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 60979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 60979) = 1/(60979 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-123660161 / 250000000) (-494640643 / 1000000000) (Real.log (60979 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (165039493 / 500000000) ≤ -Real.log (500000 / 695539) ∧
    -Real.log (500000 / 695539) ≤ (330078987 / 1000000000) := by
  have h := checkLog_sound (w := (195539 / 1195539)) (n := 12)
    (lo := (165039493 / 500000000)) (hi := (330078987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695539 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695539 / 500000) = 1/(500000 / 695539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (165039493 / 500000000) (330078987 / 1000000000) (Real.log (695539 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (695539 / 500000) = -Real.log (500000 / 695539) := by
    rw [show ((695539 / 500000) : ℝ) = ((500000 / 695539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (248032549 / 500000000) ≤ -Real.log (304461 / 500000) ∧
    -Real.log (304461 / 500000) ≤ (496065099 / 1000000000) := by
  have h := checkLog_sound (w := (195539 / 804461)) (n := 12)
    (lo := (248032549 / 500000000)) (hi := (496065099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 304461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 304461) = 1/(304461 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-496065099 / 1000000000) (-248032549 / 500000000) (Real.log (304461 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (253127117 / 1000000000) ≤ -Real.log (1000000 / 1288047) ∧
    -Real.log (1000000 / 1288047) ≤ (126563559 / 500000000) := by
  have h := checkLog_sound (w := (288047 / 2288047)) (n := 12)
    (lo := (253127117 / 1000000000)) (hi := (126563559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1288047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1288047 / 1000000) = 1/(1000000 / 1288047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (253127117 / 1000000000) (126563559 / 500000000) (Real.log (1288047 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1288047 / 1000000) = -Real.log (1000000 / 1288047) := by
    rw [show ((1288047 / 1000000) : ℝ) = ((1000000 / 1288047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16987169 / 50000000) ≤ -Real.log (711953 / 1000000) ∧
    -Real.log (711953 / 1000000) ≤ (339743381 / 1000000000) := by
  have h := checkLog_sound (w := (288047 / 1711953)) (n := 12)
    (lo := (16987169 / 50000000)) (hi := (339743381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 711953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 711953) = 1/(711953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-339743381 / 1000000000) (-16987169 / 50000000) (Real.log (711953 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (63417219 / 250000000) ≤ -Real.log (200000 / 257749) ∧
    -Real.log (200000 / 257749) ≤ (253668877 / 1000000000) := by
  have h := checkLog_sound (w := (57749 / 457749)) (n := 12)
    (lo := (63417219 / 250000000)) (hi := (253668877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257749 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257749 / 200000) = 1/(200000 / 257749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (63417219 / 250000000) (253668877 / 1000000000) (Real.log (257749 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (257749 / 200000) = -Real.log (200000 / 257749) := by
    rw [show ((257749 / 200000) : ℝ) = ((200000 / 257749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (340724263 / 1000000000) ≤ -Real.log (142251 / 200000) ∧
    -Real.log (142251 / 200000) ≤ (42590533 / 125000000) := by
  have h := checkLog_sound (w := (57749 / 342251)) (n := 12)
    (lo := (340724263 / 1000000000)) (hi := (42590533 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 142251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 142251) = 1/(142251 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-42590533 / 125000000) (-340724263 / 1000000000) (Real.log (142251 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (824095457 / 1000000000) ≤ -Real.log (500000000000 / 1139908821069) ∧
    -Real.log (500000000000 / 1139908821069) ≤ (824095459 / 1000000000) := by
  have h := checkLog_sound (w := (139908821069 / 2139908821069)) (n := 12)
    (lo := (130948277 / 1000000000)) (hi := (65474139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139908821069 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1139908821069 / 1000000000000) = 1/(500000000000 / 1139908821069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (824095457 / 1000000000) (824095459 / 1000000000) (Real.log (1139908821069 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1139908821069 / 500000000000) = -Real.log (500000000000 / 1139908821069) := by
    rw [show ((1139908821069 / 500000000000) : ℝ) = ((500000000000 / 1139908821069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (826144083 / 1000000000) ≤ -Real.log (25000000000 / 57112323089) ∧
    -Real.log (25000000000 / 57112323089) ≤ (165228817 / 200000000) := by
  have h := checkLog_sound (w := (7112323089 / 107112323089)) (n := 12)
    (lo := (132996903 / 1000000000)) (hi := (16624613 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57112323089 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(57112323089 / 50000000000) = 1/(25000000000 / 57112323089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (826144083 / 1000000000) (165228817 / 200000000) (Real.log (57112323089 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (57112323089 / 25000000000) = -Real.log (25000000000 / 57112323089) := by
    rw [show ((57112323089 / 25000000000) : ℝ) = ((25000000000 / 57112323089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (296435249 / 500000000) ≤ -Real.log (62500000000 / 113073387569) ∧
    -Real.log (62500000000 / 113073387569) ≤ (592870499 / 1000000000) := by
  have h := checkLog_sound (w := (50573387569 / 175573387569)) (n := 12)
    (lo := (296435249 / 500000000)) (hi := (592870499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113073387569 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113073387569 / 62500000000) = 1/(62500000000 / 113073387569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (296435249 / 500000000) (592870499 / 1000000000) (Real.log (113073387569 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (113073387569 / 62500000000) = -Real.log (62500000000 / 113073387569) := by
    rw [show ((113073387569 / 62500000000) : ℝ) = ((62500000000 / 113073387569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (29719657 / 50000000) ≤ -Real.log (250000000000 / 452982755833) ∧
    -Real.log (250000000000 / 452982755833) ≤ (594393141 / 1000000000) := by
  have h := checkLog_sound (w := (202982755833 / 702982755833)) (n := 12)
    (lo := (29719657 / 50000000)) (hi := (594393141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((452982755833 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(452982755833 / 250000000000) = 1/(250000000000 / 452982755833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (29719657 / 50000000) (594393141 / 1000000000) (Real.log (452982755833 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (452982755833 / 250000000000) = -Real.log (250000000000 / 452982755833) := by
    rw [show ((452982755833 / 250000000000) : ℝ) = ((250000000000 / 452982755833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0254

end


