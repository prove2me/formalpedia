-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0148Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0148Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:08:37.410189+00:00
-- url     : https://prove2.me/theorems/de7ac8be-c182-4958-8a7c-a17dacfe6080
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0148Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0149Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0148Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0149Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0150Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0151Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0152Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0153Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0154Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0155Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0148Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0149Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0150Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0151Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0152Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0153Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0154Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0155Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0148Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0149Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0150Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0151Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0152Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0153Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0154Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0155Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0148Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0149Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0150Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0151Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0152Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0153Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0154Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0155Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0148Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0148
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

theorem reflection_log_1_neg : (146130707 / 500000000) ≤ -Real.log (2560 / 3429) ∧
    -Real.log (2560 / 3429) ≤ (58452283 / 200000000) := by
  have h := checkLog_sound (w := (869 / 5989)) (n := 12)
    (lo := (146130707 / 500000000)) (hi := (58452283 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3429 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3429 / 2560) = 1/(2560 / 3429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (146130707 / 500000000) (58452283 / 200000000) (Real.log (3429 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3429 / 2560) = -Real.log (2560 / 3429) := by
    rw [show ((3429 / 2560) : ℝ) = ((2560 / 3429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (103671797 / 250000000) ≤ -Real.log (1691 / 2560) ∧
    -Real.log (1691 / 2560) ≤ (414687189 / 1000000000) := by
  have h := checkLog_sound (w := (869 / 4251)) (n := 12)
    (lo := (103671797 / 250000000)) (hi := (414687189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1691) = 1/(1691 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-414687189 / 1000000000) (-103671797 / 250000000) (Real.log (1691 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (291386141 / 1000000000) ≤ -Real.log (1280 / 1713) ∧
    -Real.log (1280 / 1713) ≤ (145693071 / 500000000) := by
  have h := checkLog_sound (w := (433 / 2993)) (n := 12)
    (lo := (291386141 / 1000000000)) (hi := (145693071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1713 / 1280) = 1/(1280 / 1713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (291386141 / 1000000000) (145693071 / 500000000) (Real.log (1713 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1713 / 1280) = -Real.log (1280 / 1713) := by
    rw [show ((1713 / 1280) : ℝ) = ((1280 / 1713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (206457331 / 500000000) ≤ -Real.log (847 / 1280) ∧
    -Real.log (847 / 1280) ≤ (412914663 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2127)) (n := 12)
    (lo := (206457331 / 500000000)) (hi := (412914663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 847) = 1/(847 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-412914663 / 1000000000) (-206457331 / 500000000) (Real.log (847 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (518142539 / 1000000000) ≤ -Real.log (1280 / 2149) ∧
    -Real.log (1280 / 2149) ≤ (25907127 / 50000000) := by
  have h := checkLog_sound (w := (869 / 3429)) (n := 12)
    (lo := (518142539 / 1000000000)) (hi := (25907127 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2149 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2149 / 1280) = 1/(1280 / 2149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (518142539 / 1000000000) (25907127 / 50000000) (Real.log (2149 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2149 / 1280) = -Real.log (1280 / 2149) := by
    rw [show ((2149 / 1280) : ℝ) = ((1280 / 2149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1136022141 / 1000000000) ≤ -Real.log (411 / 1280) ∧
    -Real.log (411 / 1280) ≤ (1136022143 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1051)) (n := 12)
    (lo := (442874961 / 1000000000)) (hi := (221437481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 411) = 1/(411 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1136022143 / 1000000000) (-1136022141 / 1000000000) (Real.log (411 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (258372783 / 500000000) ≤ -Real.log (640 / 1073) ∧
    -Real.log (640 / 1073) ≤ (516745567 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 1713)) (n := 12)
    (lo := (258372783 / 500000000)) (hi := (516745567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1073 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1073 / 640) = 1/(640 / 1073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (258372783 / 500000000) (516745567 / 1000000000) (Real.log (1073 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1073 / 640) = -Real.log (640 / 1073) := by
    rw [show ((1073 / 640) : ℝ) = ((640 / 1073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (564374691 / 500000000) ≤ -Real.log (207 / 640) ∧
    -Real.log (207 / 640) ≤ (141093673 / 125000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 207) = 1/(207 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-141093673 / 125000000) (-564374691 / 500000000) (Real.log (207 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79738579 / 200000000) ≤ -Real.log (250000 / 372469) ∧
    -Real.log (250000 / 372469) ≤ (12459153 / 31250000) := by
  have h := checkLog_sound (w := (122469 / 622469)) (n := 12)
    (lo := (79738579 / 200000000)) (hi := (12459153 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372469 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372469 / 250000) = 1/(250000 / 372469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79738579 / 200000000) (12459153 / 31250000) (Real.log (372469 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (372469 / 250000) = -Real.log (250000 / 372469) := by
    rw [show ((372469 / 250000) : ℝ) = ((250000 / 372469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (134620289 / 200000000) ≤ -Real.log (127531 / 250000) ∧
    -Real.log (127531 / 250000) ≤ (336550723 / 500000000) := by
  have h := checkLog_sound (w := (122469 / 377531)) (n := 12)
    (lo := (134620289 / 200000000)) (hi := (336550723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 127531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 127531) = 1/(127531 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-336550723 / 500000000) (-134620289 / 200000000) (Real.log (127531 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (39990099 / 100000000) ≤ -Real.log (1000000 / 1491677) ∧
    -Real.log (1000000 / 1491677) ≤ (399900991 / 1000000000) := by
  have h := checkLog_sound (w := (491677 / 2491677)) (n := 12)
    (lo := (39990099 / 100000000)) (hi := (399900991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1491677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1491677 / 1000000) = 1/(1000000 / 1491677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (39990099 / 100000000) (399900991 / 1000000000) (Real.log (1491677 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1491677 / 1000000) = -Real.log (1000000 / 1491677) := by
    rw [show ((1491677 / 1000000) : ℝ) = ((1000000 / 1491677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (338319103 / 500000000) ≤ -Real.log (508323 / 1000000) ∧
    -Real.log (508323 / 1000000) ≤ (676638207 / 1000000000) := by
  have h := checkLog_sound (w := (491677 / 1508323)) (n := 12)
    (lo := (338319103 / 500000000)) (hi := (676638207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 508323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 508323) = 1/(508323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-676638207 / 1000000000) (-338319103 / 500000000) (Real.log (508323 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (315506847 / 1000000000) ≤ -Real.log (500000 / 685477) ∧
    -Real.log (500000 / 685477) ≤ (9859589 / 31250000) := by
  have h := checkLog_sound (w := (185477 / 1185477)) (n := 12)
    (lo := (315506847 / 1000000000)) (hi := (9859589 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685477 / 500000) = 1/(500000 / 685477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (315506847 / 1000000000) (9859589 / 31250000) (Real.log (685477 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (685477 / 500000) = -Real.log (500000 / 685477) := by
    rw [show ((685477 / 500000) : ℝ) = ((500000 / 685477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (463550893 / 1000000000) ≤ -Real.log (314523 / 500000) ∧
    -Real.log (314523 / 500000) ≤ (231775447 / 500000000) := by
  have h := checkLog_sound (w := (185477 / 814523)) (n := 12)
    (lo := (463550893 / 1000000000)) (hi := (231775447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 314523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 314523) = 1/(314523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-231775447 / 500000000) (-463550893 / 1000000000) (Real.log (314523 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (79160477 / 250000000) ≤ -Real.log (1000000 / 1372511) ∧
    -Real.log (1000000 / 1372511) ≤ (316641909 / 1000000000) := by
  have h := checkLog_sound (w := (372511 / 2372511)) (n := 12)
    (lo := (79160477 / 250000000)) (hi := (316641909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1372511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1372511 / 1000000) = 1/(1000000 / 1372511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (79160477 / 250000000) (316641909 / 1000000000) (Real.log (1372511 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1372511 / 1000000) = -Real.log (1000000 / 1372511) := by
    rw [show ((1372511 / 1000000) : ℝ) = ((1000000 / 1372511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (233014569 / 500000000) ≤ -Real.log (627489 / 1000000) ∧
    -Real.log (627489 / 1000000) ≤ (466029139 / 1000000000) := by
  have h := checkLog_sound (w := (372511 / 1627489)) (n := 12)
    (lo := (233014569 / 500000000)) (hi := (466029139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 627489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 627489) = 1/(627489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-466029139 / 1000000000) (-233014569 / 500000000) (Real.log (627489 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (53589717 / 50000000) ≤ -Real.log (100000000000 / 292061537979) ∧
    -Real.log (100000000000 / 292061537979) ≤ (535897171 / 500000000) := by
  have h := checkLog_sound (w := (92061537979 / 492061537979)) (n := 12)
    (lo := (9466179 / 25000000)) (hi := (378647161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292061537979 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(292061537979 / 200000000000) = 1/(100000000000 / 292061537979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (53589717 / 50000000) (535897171 / 500000000) (Real.log (292061537979 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (292061537979 / 100000000000) = -Real.log (100000000000 / 292061537979) := by
    rw [show ((292061537979 / 100000000000) : ℝ) = ((100000000000 / 292061537979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (269134799 / 250000000) ≤ -Real.log (250000000000 / 733626552409) ∧
    -Real.log (250000000000 / 733626552409) ≤ (538269599 / 500000000) := by
  have h := checkLog_sound (w := (233626552409 / 1233626552409)) (n := 12)
    (lo := (23962001 / 62500000)) (hi := (383392017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733626552409 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(733626552409 / 500000000000) = 1/(250000000000 / 733626552409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (269134799 / 250000000) (538269599 / 500000000) (Real.log (733626552409 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (733626552409 / 250000000000) = -Real.log (250000000000 / 733626552409) := by
    rw [show ((733626552409 / 250000000000) : ℝ) = ((250000000000 / 733626552409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (38952887 / 50000000) ≤ -Real.log (500000000000 / 1089708860719) ∧
    -Real.log (500000000000 / 1089708860719) ≤ (389528871 / 500000000) := by
  have h := checkLog_sound (w := (89708860719 / 2089708860719)) (n := 12)
    (lo := (536941 / 6250000)) (hi := (85910561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089708860719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1089708860719 / 1000000000000) = 1/(500000000000 / 1089708860719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (38952887 / 50000000) (389528871 / 500000000) (Real.log (1089708860719 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1089708860719 / 500000000000) = -Real.log (500000000000 / 1089708860719) := by
    rw [show ((1089708860719 / 500000000000) : ℝ) = ((500000000000 / 1089708860719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (391335523 / 500000000) ≤ -Real.log (500000000000 / 1093653434563) ∧
    -Real.log (500000000000 / 1093653434563) ≤ (97833881 / 125000000) := by
  have h := checkLog_sound (w := (93653434563 / 2093653434563)) (n := 12)
    (lo := (44761933 / 500000000)) (hi := (89523867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093653434563 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1093653434563 / 1000000000000) = 1/(500000000000 / 1093653434563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (391335523 / 500000000) (97833881 / 125000000) (Real.log (1093653434563 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1093653434563 / 500000000000) = -Real.log (500000000000 / 1093653434563) := by
    rw [show ((1093653434563 / 500000000000) : ℝ) = ((500000000000 / 1093653434563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0148

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0149Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0149
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

theorem reflection_log_1_neg : (291386141 / 1000000000) ≤ -Real.log (1280 / 1713) ∧
    -Real.log (1280 / 1713) ≤ (145693071 / 500000000) := by
  have h := checkLog_sound (w := (433 / 2993)) (n := 12)
    (lo := (291386141 / 1000000000)) (hi := (145693071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1713 / 1280) = 1/(1280 / 1713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (291386141 / 1000000000) (145693071 / 500000000) (Real.log (1713 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1713 / 1280) = -Real.log (1280 / 1713) := by
    rw [show ((1713 / 1280) : ℝ) = ((1280 / 1713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (206457331 / 500000000) ≤ -Real.log (847 / 1280) ∧
    -Real.log (847 / 1280) ≤ (412914663 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2127)) (n := 12)
    (lo := (206457331 / 500000000)) (hi := (412914663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 847) = 1/(847 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-412914663 / 1000000000) (-206457331 / 500000000) (Real.log (847 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (290510101 / 1000000000) ≤ -Real.log (2560 / 3423) ∧
    -Real.log (2560 / 3423) ≤ (145255051 / 500000000) := by
  have h := checkLog_sound (w := (863 / 5983)) (n := 12)
    (lo := (290510101 / 1000000000)) (hi := (145255051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3423 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3423 / 2560) = 1/(2560 / 3423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (290510101 / 1000000000) (145255051 / 500000000) (Real.log (3423 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3423 / 2560) = -Real.log (2560 / 3423) := by
    rw [show ((3423 / 2560) : ℝ) = ((2560 / 3423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (51393159 / 125000000) ≤ -Real.log (1697 / 2560) ∧
    -Real.log (1697 / 2560) ≤ (411145273 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 4257)) (n := 12)
    (lo := (51393159 / 125000000)) (hi := (411145273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1697) = 1/(1697 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-411145273 / 1000000000) (-51393159 / 125000000) (Real.log (1697 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (258372783 / 500000000) ≤ -Real.log (640 / 1073) ∧
    -Real.log (640 / 1073) ≤ (516745567 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 1713)) (n := 12)
    (lo := (258372783 / 500000000)) (hi := (516745567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1073 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1073 / 640) = 1/(640 / 1073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (258372783 / 500000000) (516745567 / 1000000000) (Real.log (1073 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1073 / 640) = -Real.log (640 / 1073) := by
    rw [show ((1073 / 640) : ℝ) = ((640 / 1073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (564374691 / 500000000) ≤ -Real.log (207 / 640) ∧
    -Real.log (207 / 640) ≤ (141093673 / 125000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 207) = 1/(207 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-141093673 / 125000000) (-564374691 / 500000000) (Real.log (207 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (257673319 / 500000000) ≤ -Real.log (1280 / 2143) ∧
    -Real.log (1280 / 2143) ≤ (515346639 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 3423)) (n := 12)
    (lo := (257673319 / 500000000)) (hi := (515346639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2143 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2143 / 1280) = 1/(1280 / 2143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (257673319 / 500000000) (515346639 / 1000000000) (Real.log (2143 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2143 / 1280) = -Real.log (1280 / 2143) := by
    rw [show ((2143 / 1280) : ℝ) = ((1280 / 2143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (560764567 / 500000000) ≤ -Real.log (417 / 1280) ∧
    -Real.log (417 / 1280) ≤ (70095571 / 62500000) := by
  have h := checkLog_sound (w := (223 / 1057)) (n := 12)
    (lo := (214190977 / 500000000)) (hi := (85676391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 417) = 1/(417 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-70095571 / 62500000) (-560764567 / 500000000) (Real.log (417 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (198742341 / 500000000) ≤ -Real.log (1000000 / 1488077) ∧
    -Real.log (1000000 / 1488077) ≤ (397484683 / 1000000000) := by
  have h := checkLog_sound (w := (488077 / 2488077)) (n := 12)
    (lo := (198742341 / 500000000)) (hi := (397484683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1488077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1488077 / 1000000) = 1/(1000000 / 1488077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (198742341 / 500000000) (397484683 / 1000000000) (Real.log (1488077 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1488077 / 1000000) = -Real.log (1000000 / 1488077) := by
    rw [show ((1488077 / 1000000) : ℝ) = ((1000000 / 1488077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (133916211 / 200000000) ≤ -Real.log (511923 / 1000000) ∧
    -Real.log (511923 / 1000000) ≤ (2615551 / 3906250) := by
  have h := checkLog_sound (w := (488077 / 1511923)) (n := 12)
    (lo := (133916211 / 200000000)) (hi := (2615551 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 511923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 511923) = 1/(511923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2615551 / 3906250) (-133916211 / 200000000) (Real.log (511923 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (199346783 / 500000000) ≤ -Real.log (1000000 / 1489877) ∧
    -Real.log (1000000 / 1489877) ≤ (398693567 / 1000000000) := by
  have h := checkLog_sound (w := (489877 / 2489877)) (n := 12)
    (lo := (199346783 / 500000000)) (hi := (398693567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489877 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489877 / 1000000) = 1/(1000000 / 1489877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (199346783 / 500000000) (398693567 / 1000000000) (Real.log (1489877 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1489877 / 1000000) = -Real.log (1000000 / 1489877) := by
    rw [show ((1489877 / 1000000) : ℝ) = ((1000000 / 1489877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (134620681 / 200000000) ≤ -Real.log (510123 / 1000000) ∧
    -Real.log (510123 / 1000000) ≤ (336551703 / 500000000) := by
  have h := checkLog_sound (w := (489877 / 1510123)) (n := 12)
    (lo := (134620681 / 200000000)) (hi := (336551703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 510123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 510123) = 1/(510123 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-336551703 / 500000000) (-134620681 / 200000000) (Real.log (510123 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (314373417 / 1000000000) ≤ -Real.log (1000000 / 1369401) ∧
    -Real.log (1000000 / 1369401) ≤ (157186709 / 500000000) := by
  have h := checkLog_sound (w := (369401 / 2369401)) (n := 12)
    (lo := (314373417 / 1000000000)) (hi := (157186709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1369401 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1369401 / 1000000) = 1/(1000000 / 1369401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (314373417 / 1000000000) (157186709 / 500000000) (Real.log (1369401 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1369401 / 1000000) = -Real.log (1000000 / 1369401) := by
    rw [show ((1369401 / 1000000) : ℝ) = ((1000000 / 1369401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (461085117 / 1000000000) ≤ -Real.log (630599 / 1000000) ∧
    -Real.log (630599 / 1000000) ≤ (230542559 / 500000000) := by
  have h := checkLog_sound (w := (369401 / 1630599)) (n := 12)
    (lo := (461085117 / 1000000000)) (hi := (230542559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 630599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 630599) = 1/(630599 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-230542559 / 500000000) (-461085117 / 1000000000) (Real.log (630599 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (315507577 / 1000000000) ≤ -Real.log (200000 / 274191) ∧
    -Real.log (200000 / 274191) ≤ (157753789 / 500000000) := by
  have h := checkLog_sound (w := (74191 / 474191)) (n := 12)
    (lo := (315507577 / 1000000000)) (hi := (157753789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274191 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274191 / 200000) = 1/(200000 / 274191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (315507577 / 1000000000) (157753789 / 500000000) (Real.log (274191 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (274191 / 200000) = -Real.log (200000 / 274191) := by
    rw [show ((274191 / 200000) : ℝ) = ((200000 / 274191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (231776241 / 500000000) ≤ -Real.log (125809 / 200000) ∧
    -Real.log (125809 / 200000) ≤ (463552483 / 1000000000) := by
  have h := checkLog_sound (w := (74191 / 325809)) (n := 12)
    (lo := (231776241 / 500000000)) (hi := (463552483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 125809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 125809) = 1/(125809 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-463552483 / 1000000000) (-231776241 / 500000000) (Real.log (125809 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1067065737 / 1000000000) ≤ -Real.log (50000000000 / 145341877587) ∧
    -Real.log (50000000000 / 145341877587) ≤ (1067065739 / 1000000000) := by
  have h := checkLog_sound (w := (45341877587 / 245341877587)) (n := 12)
    (lo := (373918557 / 1000000000)) (hi := (186959279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145341877587 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(145341877587 / 100000000000) = 1/(50000000000 / 145341877587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1067065737 / 1000000000) (1067065739 / 1000000000) (Real.log (145341877587 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (145341877587 / 50000000000) = -Real.log (50000000000 / 145341877587) := by
    rw [show ((145341877587 / 50000000000) : ℝ) = ((50000000000 / 145341877587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1071796971 / 1000000000) ≤ -Real.log (500000000000 / 1460311532709) ∧
    -Real.log (500000000000 / 1460311532709) ≤ (1071796973 / 1000000000) := by
  have h := checkLog_sound (w := (460311532709 / 2460311532709)) (n := 12)
    (lo := (378649791 / 1000000000)) (hi := (5916403 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1460311532709 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1460311532709 / 1000000000000) = 1/(500000000000 / 1460311532709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1071796971 / 1000000000) (1071796973 / 1000000000) (Real.log (1460311532709 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1460311532709 / 500000000000) = -Real.log (500000000000 / 1460311532709) := by
    rw [show ((1460311532709 / 500000000000) : ℝ) = ((500000000000 / 1460311532709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (155091707 / 200000000) ≤ -Real.log (500000000000 / 1085793824601) ∧
    -Real.log (500000000000 / 1085793824601) ≤ (775458537 / 1000000000) := by
  have h := checkLog_sound (w := (85793824601 / 2085793824601)) (n := 12)
    (lo := (16462271 / 200000000)) (hi := (20577839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085793824601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1085793824601 / 1000000000000) = 1/(500000000000 / 1085793824601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (155091707 / 200000000) (775458537 / 1000000000) (Real.log (1085793824601 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1085793824601 / 500000000000) = -Real.log (500000000000 / 1085793824601) := by
    rw [show ((1085793824601 / 500000000000) : ℝ) = ((500000000000 / 1085793824601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (779060059 / 1000000000) ≤ -Real.log (250000000000 / 544855693949) ∧
    -Real.log (250000000000 / 544855693949) ≤ (779060061 / 1000000000) := by
  have h := checkLog_sound (w := (44855693949 / 1044855693949)) (n := 12)
    (lo := (85912879 / 1000000000)) (hi := (1073911 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544855693949 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(544855693949 / 500000000000) = 1/(250000000000 / 544855693949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (779060059 / 1000000000) (779060061 / 1000000000) (Real.log (544855693949 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (544855693949 / 250000000000) = -Real.log (250000000000 / 544855693949) := by
    rw [show ((544855693949 / 250000000000) : ℝ) = ((250000000000 / 544855693949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0149

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0150Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0150
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

theorem reflection_log_1_neg : (290510101 / 1000000000) ≤ -Real.log (2560 / 3423) ∧
    -Real.log (2560 / 3423) ≤ (145255051 / 500000000) := by
  have h := checkLog_sound (w := (863 / 5983)) (n := 12)
    (lo := (290510101 / 1000000000)) (hi := (145255051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3423 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3423 / 2560) = 1/(2560 / 3423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (290510101 / 1000000000) (145255051 / 500000000) (Real.log (3423 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3423 / 2560) = -Real.log (2560 / 3423) := by
    rw [show ((3423 / 2560) : ℝ) = ((2560 / 3423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (51393159 / 125000000) ≤ -Real.log (1697 / 2560) ∧
    -Real.log (1697 / 2560) ≤ (411145273 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 4257)) (n := 12)
    (lo := (51393159 / 125000000)) (hi := (411145273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1697) = 1/(1697 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-411145273 / 1000000000) (-51393159 / 125000000) (Real.log (1697 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (72408323 / 250000000) ≤ -Real.log (128 / 171) ∧
    -Real.log (128 / 171) ≤ (289633293 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 299)) (n := 12)
    (lo := (72408323 / 250000000)) (hi := (289633293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171 / 128) = 1/(128 / 171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (72408323 / 250000000) (289633293 / 1000000000) (Real.log (171 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (171 / 128) = -Real.log (128 / 171) := by
    rw [show ((171 / 128) : ℝ) = ((128 / 171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (409379007 / 1000000000) ≤ -Real.log (85 / 128) ∧
    -Real.log (85 / 128) ≤ (6396547 / 15625000) := by
  have h := checkLog_sound (w := (43 / 213)) (n := 12)
    (lo := (409379007 / 1000000000)) (hi := (6396547 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 85) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 85) = 1/(85 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6396547 / 15625000) (-409379007 / 1000000000) (Real.log (85 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (257673319 / 500000000) ≤ -Real.log (1280 / 2143) ∧
    -Real.log (1280 / 2143) ≤ (515346639 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 3423)) (n := 12)
    (lo := (257673319 / 500000000)) (hi := (515346639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2143 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2143 / 1280) = 1/(1280 / 2143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (257673319 / 500000000) (515346639 / 1000000000) (Real.log (2143 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2143 / 1280) = -Real.log (1280 / 2143) := by
    rw [show ((2143 / 1280) : ℝ) = ((1280 / 2143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (560764567 / 500000000) ≤ -Real.log (417 / 1280) ∧
    -Real.log (417 / 1280) ≤ (70095571 / 62500000) := by
  have h := checkLog_sound (w := (223 / 1057)) (n := 12)
    (lo := (214190977 / 500000000)) (hi := (85676391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 417) = 1/(417 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-70095571 / 62500000) (-560764567 / 500000000) (Real.log (417 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (513945751 / 1000000000) ≤ -Real.log (64 / 107) ∧
    -Real.log (64 / 107) ≤ (64243219 / 125000000) := by
  have h := checkLog_sound (w := (43 / 171)) (n := 12)
    (lo := (513945751 / 1000000000)) (hi := (64243219 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107 / 64) = 1/(64 / 107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (513945751 / 1000000000) (64243219 / 125000000) (Real.log (107 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (107 / 64) = -Real.log (64 / 107) := by
    rw [show ((107 / 64) : ℝ) = ((64 / 107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (222872129 / 200000000) ≤ -Real.log (21 / 64) ∧
    -Real.log (21 / 64) ≤ (1114360647 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 21) = 1/(21 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1114360647 / 1000000000) (-222872129 / 200000000) (Real.log (21 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (198138513 / 500000000) ≤ -Real.log (1000000 / 1486281) ∧
    -Real.log (1000000 / 1486281) ≤ (396277027 / 1000000000) := by
  have h := checkLog_sound (w := (486281 / 2486281)) (n := 12)
    (lo := (198138513 / 500000000)) (hi := (396277027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1486281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1486281 / 1000000) = 1/(1000000 / 1486281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (198138513 / 500000000) (396277027 / 1000000000) (Real.log (1486281 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1486281 / 1000000) = -Real.log (1000000 / 1486281) := by
    rw [show ((1486281 / 1000000) : ℝ) = ((1000000 / 1486281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (133215771 / 200000000) ≤ -Real.log (513719 / 1000000) ∧
    -Real.log (513719 / 1000000) ≤ (83259857 / 125000000) := by
  have h := checkLog_sound (w := (486281 / 1513719)) (n := 12)
    (lo := (133215771 / 200000000)) (hi := (83259857 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 513719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 513719) = 1/(513719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83259857 / 125000000) (-133215771 / 200000000) (Real.log (513719 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (198742677 / 500000000) ≤ -Real.log (500000 / 744039) ∧
    -Real.log (500000 / 744039) ≤ (79497071 / 200000000) := by
  have h := checkLog_sound (w := (244039 / 1244039)) (n := 12)
    (lo := (198742677 / 500000000)) (hi := (79497071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744039 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744039 / 500000) = 1/(500000 / 744039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (198742677 / 500000000) (79497071 / 200000000) (Real.log (744039 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (744039 / 500000) = -Real.log (500000 / 744039) := by
    rw [show ((744039 / 500000) : ℝ) = ((500000 / 744039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (669583009 / 1000000000) ≤ -Real.log (255961 / 500000) ∧
    -Real.log (255961 / 500000) ≤ (66958301 / 100000000) := by
  have h := checkLog_sound (w := (244039 / 755961)) (n := 12)
    (lo := (669583009 / 1000000000)) (hi := (66958301 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 255961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 255961) = 1/(255961 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-66958301 / 100000000) (-669583009 / 1000000000) (Real.log (255961 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (156620813 / 500000000) ≤ -Real.log (250000 / 341963) ∧
    -Real.log (250000 / 341963) ≤ (313241627 / 1000000000) := by
  have h := checkLog_sound (w := (91963 / 591963)) (n := 12)
    (lo := (156620813 / 500000000)) (hi := (313241627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341963 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341963 / 250000) = 1/(250000 / 341963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (156620813 / 500000000) (313241627 / 1000000000) (Real.log (341963 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (341963 / 250000) = -Real.log (250000 / 341963) := by
    rw [show ((341963 / 250000) : ℝ) = ((250000 / 341963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (91726347 / 200000000) ≤ -Real.log (158037 / 250000) ∧
    -Real.log (158037 / 250000) ≤ (57328967 / 125000000) := by
  have h := checkLog_sound (w := (91963 / 408037)) (n := 12)
    (lo := (91726347 / 200000000)) (hi := (57328967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 158037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 158037) = 1/(158037 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-57328967 / 125000000) (-91726347 / 200000000) (Real.log (158037 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (78593537 / 250000000) ≤ -Real.log (500000 / 684701) ∧
    -Real.log (500000 / 684701) ≤ (314374149 / 1000000000) := by
  have h := checkLog_sound (w := (184701 / 1184701)) (n := 12)
    (lo := (78593537 / 250000000)) (hi := (314374149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684701 / 500000) = 1/(500000 / 684701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (78593537 / 250000000) (314374149 / 1000000000) (Real.log (684701 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (684701 / 500000) = -Real.log (500000 / 684701) := by
    rw [show ((684701 / 500000) : ℝ) = ((500000 / 684701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (461086703 / 1000000000) ≤ -Real.log (315299 / 500000) ∧
    -Real.log (315299 / 500000) ≤ (28817919 / 62500000) := by
  have h := checkLog_sound (w := (184701 / 815299)) (n := 12)
    (lo := (461086703 / 1000000000)) (hi := (28817919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 315299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 315299) = 1/(315299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-28817919 / 62500000) (-461086703 / 1000000000) (Real.log (315299 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1062355881 / 1000000000) ≤ -Real.log (100000000000 / 289317895581) ∧
    -Real.log (100000000000 / 289317895581) ≤ (1062355883 / 1000000000) := by
  have h := checkLog_sound (w := (89317895581 / 489317895581)) (n := 12)
    (lo := (369208701 / 1000000000)) (hi := (184604351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289317895581 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(289317895581 / 200000000000) = 1/(100000000000 / 289317895581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1062355881 / 1000000000) (1062355883 / 1000000000) (Real.log (289317895581 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (289317895581 / 100000000000) = -Real.log (100000000000 / 289317895581) := by
    rw [show ((289317895581 / 100000000000) : ℝ) = ((100000000000 / 289317895581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1067068363 / 1000000000) ≤ -Real.log (500000000000 / 1453422591723) ∧
    -Real.log (500000000000 / 1453422591723) ≤ (213413673 / 200000000) := by
  have h := checkLog_sound (w := (453422591723 / 2453422591723)) (n := 12)
    (lo := (373921183 / 1000000000)) (hi := (11685037 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453422591723 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1453422591723 / 1000000000000) = 1/(500000000000 / 1453422591723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1067068363 / 1000000000) (213413673 / 200000000) (Real.log (1453422591723 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1453422591723 / 500000000000) = -Real.log (500000000000 / 1453422591723) := by
    rw [show ((1453422591723 / 500000000000) : ℝ) = ((500000000000 / 1453422591723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9648417 / 12500000) ≤ -Real.log (250000000000 / 540954017097) ∧
    -Real.log (250000000000 / 540954017097) ≤ (385936681 / 500000000) := by
  have h := checkLog_sound (w := (40954017097 / 1040954017097)) (n := 12)
    (lo := (3936309 / 50000000)) (hi := (78726181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540954017097 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(540954017097 / 500000000000) = 1/(250000000000 / 540954017097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (9648417 / 12500000) (385936681 / 500000000) (Real.log (540954017097 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (540954017097 / 250000000000) = -Real.log (250000000000 / 540954017097) := by
    rw [show ((540954017097 / 250000000000) : ℝ) = ((250000000000 / 540954017097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (775460851 / 1000000000) ≤ -Real.log (125000000000 / 271449084837) ∧
    -Real.log (125000000000 / 271449084837) ≤ (775460853 / 1000000000) := by
  have h := checkLog_sound (w := (21449084837 / 521449084837)) (n := 12)
    (lo := (82313671 / 1000000000)) (hi := (10289209 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271449084837 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(271449084837 / 250000000000) = 1/(125000000000 / 271449084837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (775460851 / 1000000000) (775460853 / 1000000000) (Real.log (271449084837 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (271449084837 / 125000000000) = -Real.log (125000000000 / 271449084837) := by
    rw [show ((271449084837 / 125000000000) : ℝ) = ((125000000000 / 271449084837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0150

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0151Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0151
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

theorem reflection_log_1_neg : (72408323 / 250000000) ≤ -Real.log (128 / 171) ∧
    -Real.log (128 / 171) ≤ (289633293 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 299)) (n := 12)
    (lo := (72408323 / 250000000)) (hi := (289633293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171 / 128) = 1/(128 / 171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (72408323 / 250000000) (289633293 / 1000000000) (Real.log (171 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (171 / 128) = -Real.log (128 / 171) := by
    rw [show ((171 / 128) : ℝ) = ((128 / 171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (409379007 / 1000000000) ≤ -Real.log (85 / 128) ∧
    -Real.log (85 / 128) ≤ (6396547 / 15625000) := by
  have h := checkLog_sound (w := (43 / 213)) (n := 12)
    (lo := (409379007 / 1000000000)) (hi := (6396547 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 85) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 85) = 1/(85 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6396547 / 15625000) (-409379007 / 1000000000) (Real.log (85 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (144377857 / 500000000) ≤ -Real.log (2560 / 3417) ∧
    -Real.log (2560 / 3417) ≤ (57751143 / 200000000) := by
  have h := checkLog_sound (w := (857 / 5977)) (n := 12)
    (lo := (144377857 / 500000000)) (hi := (57751143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3417 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3417 / 2560) = 1/(2560 / 3417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (144377857 / 500000000) (57751143 / 200000000) (Real.log (3417 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3417 / 2560) = -Real.log (2560 / 3417) := by
    rw [show ((3417 / 2560) : ℝ) = ((2560 / 3417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (25475991 / 62500000) ≤ -Real.log (1703 / 2560) ∧
    -Real.log (1703 / 2560) ≤ (407615857 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 4263)) (n := 12)
    (lo := (25475991 / 62500000)) (hi := (407615857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1703) = 1/(1703 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-407615857 / 1000000000) (-25475991 / 62500000) (Real.log (1703 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (513945751 / 1000000000) ≤ -Real.log (64 / 107) ∧
    -Real.log (64 / 107) ≤ (64243219 / 125000000) := by
  have h := checkLog_sound (w := (43 / 171)) (n := 12)
    (lo := (513945751 / 1000000000)) (hi := (64243219 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107 / 64) = 1/(64 / 107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (513945751 / 1000000000) (64243219 / 125000000) (Real.log (107 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (107 / 64) = -Real.log (64 / 107) := by
    rw [show ((107 / 64) : ℝ) = ((64 / 107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (222872129 / 200000000) ≤ -Real.log (21 / 64) ∧
    -Real.log (21 / 64) ≤ (1114360647 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 21) = 1/(21 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1114360647 / 1000000000) (-222872129 / 200000000) (Real.log (21 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (256271449 / 500000000) ≤ -Real.log (1280 / 2137) ∧
    -Real.log (1280 / 2137) ≤ (512542899 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 3417)) (n := 12)
    (lo := (256271449 / 500000000)) (hi := (512542899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2137 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2137 / 1280) = 1/(1280 / 2137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (256271449 / 500000000) (512542899 / 1000000000) (Real.log (2137 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2137 / 1280) = -Real.log (1280 / 2137) := by
    rw [show ((2137 / 1280) : ℝ) = ((1280 / 2137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1107243177 / 1000000000) ≤ -Real.log (423 / 1280) ∧
    -Real.log (423 / 1280) ≤ (1107243179 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1063)) (n := 12)
    (lo := (414095997 / 1000000000)) (hi := (207047999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 423) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 423) = 1/(423 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1107243179 / 1000000000) (-1107243177 / 1000000000) (Real.log (423 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (39506791 / 100000000) ≤ -Real.log (200000 / 296897) ∧
    -Real.log (200000 / 296897) ≤ (395067911 / 1000000000) := by
  have h := checkLog_sound (w := (96897 / 496897)) (n := 12)
    (lo := (39506791 / 100000000)) (hi := (395067911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296897 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296897 / 200000) = 1/(200000 / 296897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (39506791 / 100000000) (395067911 / 1000000000) (Real.log (296897 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (296897 / 200000) = -Real.log (200000 / 296897) := by
    rw [show ((296897 / 200000) : ℝ) = ((200000 / 296897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (662588877 / 1000000000) ≤ -Real.log (103103 / 200000) ∧
    -Real.log (103103 / 200000) ≤ (331294439 / 500000000) := by
  have h := checkLog_sound (w := (96897 / 303103)) (n := 12)
    (lo := (662588877 / 1000000000)) (hi := (331294439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 103103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 103103) = 1/(103103 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-331294439 / 500000000) (-662588877 / 1000000000) (Real.log (103103 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (396277699 / 1000000000) ≤ -Real.log (500000 / 743141) ∧
    -Real.log (500000 / 743141) ≤ (3962777 / 10000000) := by
  have h := checkLog_sound (w := (243141 / 1243141)) (n := 12)
    (lo := (396277699 / 1000000000)) (hi := (3962777 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743141 / 500000) = 1/(500000 / 743141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (396277699 / 1000000000) (3962777 / 10000000) (Real.log (743141 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (743141 / 500000) = -Real.log (500000 / 743141) := by
    rw [show ((743141 / 500000) : ℝ) = ((500000 / 743141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (333040401 / 500000000) ≤ -Real.log (256859 / 500000) ∧
    -Real.log (256859 / 500000) ≤ (666080803 / 1000000000) := by
  have h := checkLog_sound (w := (243141 / 756859)) (n := 12)
    (lo := (333040401 / 500000000)) (hi := (666080803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 256859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 256859) = 1/(256859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-666080803 / 1000000000) (-333040401 / 500000000) (Real.log (256859 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (312111479 / 1000000000) ≤ -Real.log (1000000 / 1366307) ∧
    -Real.log (1000000 / 1366307) ≤ (7802787 / 25000000) := by
  have h := checkLog_sound (w := (366307 / 2366307)) (n := 12)
    (lo := (312111479 / 1000000000)) (hi := (7802787 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1366307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1366307 / 1000000) = 1/(1000000 / 1366307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (312111479 / 1000000000) (7802787 / 25000000) (Real.log (1366307 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1366307 / 1000000) = -Real.log (1000000 / 1366307) := by
    rw [show ((1366307 / 1000000) : ℝ) = ((1000000 / 1366307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (114047667 / 250000000) ≤ -Real.log (633693 / 1000000) ∧
    -Real.log (633693 / 1000000) ≤ (456190669 / 1000000000) := by
  have h := checkLog_sound (w := (366307 / 1633693)) (n := 12)
    (lo := (114047667 / 250000000)) (hi := (456190669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 633693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 633693) = 1/(633693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-456190669 / 1000000000) (-114047667 / 250000000) (Real.log (633693 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (313242357 / 1000000000) ≤ -Real.log (1000000 / 1367853) ∧
    -Real.log (1000000 / 1367853) ≤ (156621179 / 500000000) := by
  have h := checkLog_sound (w := (367853 / 2367853)) (n := 12)
    (lo := (313242357 / 1000000000)) (hi := (156621179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1367853 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1367853 / 1000000) = 1/(1000000 / 1367853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (313242357 / 1000000000) (156621179 / 500000000) (Real.log (1367853 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1367853 / 1000000) = -Real.log (1000000 / 1367853) := by
    rw [show ((1367853 / 1000000) : ℝ) = ((1000000 / 1367853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (114658329 / 250000000) ≤ -Real.log (632147 / 1000000) ∧
    -Real.log (632147 / 1000000) ≤ (458633317 / 1000000000) := by
  have h := checkLog_sound (w := (367853 / 1632147)) (n := 12)
    (lo := (114658329 / 250000000)) (hi := (458633317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 632147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 632147) = 1/(632147 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-458633317 / 1000000000) (-114658329 / 250000000) (Real.log (632147 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (264414197 / 250000000) ≤ -Real.log (10000000000 / 28796155301) ∧
    -Real.log (10000000000 / 28796155301) ≤ (105765679 / 100000000) := by
  have h := checkLog_sound (w := (8796155301 / 48796155301)) (n := 12)
    (lo := (45563701 / 125000000)) (hi := (364509609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28796155301 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(28796155301 / 20000000000) = 1/(10000000000 / 28796155301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (264414197 / 250000000) (105765679 / 100000000) (Real.log (28796155301 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28796155301 / 10000000000) = -Real.log (10000000000 / 28796155301) := by
    rw [show ((28796155301 / 10000000000) : ℝ) = ((10000000000 / 28796155301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1062358501 / 1000000000) ≤ -Real.log (125000000000 / 361648316781) ∧
    -Real.log (125000000000 / 361648316781) ≤ (1062358503 / 1000000000) := by
  have h := checkLog_sound (w := (111648316781 / 611648316781)) (n := 12)
    (lo := (369211321 / 1000000000)) (hi := (184605661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361648316781 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(361648316781 / 250000000000) = 1/(125000000000 / 361648316781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1062358501 / 1000000000) (1062358503 / 1000000000) (Real.log (361648316781 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (361648316781 / 125000000000) = -Real.log (125000000000 / 361648316781) := by
    rw [show ((361648316781 / 125000000000) : ℝ) = ((125000000000 / 361648316781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (192075537 / 250000000) ≤ -Real.log (500000000000 / 1078051201449) ∧
    -Real.log (500000000000 / 1078051201449) ≤ (15366043 / 20000000) := by
  have h := checkLog_sound (w := (78051201449 / 2078051201449)) (n := 12)
    (lo := (9394371 / 125000000)) (hi := (75154969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078051201449 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1078051201449 / 1000000000000) = 1/(500000000000 / 1078051201449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (192075537 / 250000000) (15366043 / 20000000) (Real.log (1078051201449 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1078051201449 / 500000000000) = -Real.log (500000000000 / 1078051201449) := by
    rw [show ((1078051201449 / 500000000000) : ℝ) = ((500000000000 / 1078051201449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (771875673 / 1000000000) ≤ -Real.log (62500000000 / 135238817079) ∧
    -Real.log (62500000000 / 135238817079) ≤ (30875027 / 40000000) := by
  have h := checkLog_sound (w := (10238817079 / 260238817079)) (n := 12)
    (lo := (78728493 / 1000000000)) (hi := (39364247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135238817079 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(135238817079 / 125000000000) = 1/(62500000000 / 135238817079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (771875673 / 1000000000) (30875027 / 40000000) (Real.log (135238817079 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (135238817079 / 62500000000) = -Real.log (62500000000 / 135238817079) := by
    rw [show ((135238817079 / 62500000000) : ℝ) = ((62500000000 / 135238817079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0151

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0152Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0152
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

theorem reflection_log_1_neg : (144377857 / 500000000) ≤ -Real.log (2560 / 3417) ∧
    -Real.log (2560 / 3417) ≤ (57751143 / 200000000) := by
  have h := checkLog_sound (w := (857 / 5977)) (n := 12)
    (lo := (144377857 / 500000000)) (hi := (57751143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3417 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3417 / 2560) = 1/(2560 / 3417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (144377857 / 500000000) (57751143 / 200000000) (Real.log (3417 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3417 / 2560) = -Real.log (2560 / 3417) := by
    rw [show ((3417 / 2560) : ℝ) = ((2560 / 3417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (25475991 / 62500000) ≤ -Real.log (1703 / 2560) ∧
    -Real.log (1703 / 2560) ≤ (407615857 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 4263)) (n := 12)
    (lo := (25475991 / 62500000)) (hi := (407615857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1703) = 1/(1703 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-407615857 / 1000000000) (-25475991 / 62500000) (Real.log (1703 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (57575473 / 200000000) ≤ -Real.log (1280 / 1707) ∧
    -Real.log (1280 / 1707) ≤ (143938683 / 500000000) := by
  have h := checkLog_sound (w := (427 / 2987)) (n := 12)
    (lo := (57575473 / 200000000)) (hi := (143938683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1707 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1707 / 1280) = 1/(1280 / 1707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (57575473 / 200000000) (143938683 / 500000000) (Real.log (1707 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1707 / 1280) = -Real.log (1280 / 1707) := by
    rw [show ((1707 / 1280) : ℝ) = ((1280 / 1707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (405855809 / 1000000000) ≤ -Real.log (853 / 1280) ∧
    -Real.log (853 / 1280) ≤ (40585581 / 100000000) := by
  have h := checkLog_sound (w := (427 / 2133)) (n := 12)
    (lo := (405855809 / 1000000000)) (hi := (40585581 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 853) = 1/(853 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-40585581 / 100000000) (-405855809 / 1000000000) (Real.log (853 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (256271449 / 500000000) ≤ -Real.log (1280 / 2137) ∧
    -Real.log (1280 / 2137) ≤ (512542899 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 3417)) (n := 12)
    (lo := (256271449 / 500000000)) (hi := (512542899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2137 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2137 / 1280) = 1/(1280 / 2137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (256271449 / 500000000) (512542899 / 1000000000) (Real.log (2137 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2137 / 1280) = -Real.log (1280 / 2137) := by
    rw [show ((2137 / 1280) : ℝ) = ((1280 / 2137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1107243177 / 1000000000) ≤ -Real.log (423 / 1280) ∧
    -Real.log (423 / 1280) ≤ (1107243179 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1063)) (n := 12)
    (lo := (414095997 / 1000000000)) (hi := (207047999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 423) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 423) = 1/(423 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1107243179 / 1000000000) (-1107243177 / 1000000000) (Real.log (423 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (255569037 / 500000000) ≤ -Real.log (640 / 1067) ∧
    -Real.log (640 / 1067) ≤ (20445523 / 40000000) := by
  have h := checkLog_sound (w := (427 / 1707)) (n := 12)
    (lo := (255569037 / 500000000)) (hi := (20445523 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1067 / 640) = 1/(640 / 1067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (255569037 / 500000000) (20445523 / 40000000) (Real.log (1067 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1067 / 640) = -Real.log (640 / 1067) := by
    rw [show ((1067 / 640) : ℝ) = ((640 / 1067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (110017601 / 100000000) ≤ -Real.log (213 / 640) ∧
    -Real.log (213 / 640) ≤ (275044003 / 250000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 213) = 1/(213 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-275044003 / 250000000) (-110017601 / 100000000) (Real.log (213 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9846467 / 25000000) ≤ -Real.log (1000000 / 1482691) ∧
    -Real.log (1000000 / 1482691) ≤ (393858681 / 1000000000) := by
  have h := checkLog_sound (w := (482691 / 2482691)) (n := 12)
    (lo := (9846467 / 25000000)) (hi := (393858681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1482691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1482691 / 1000000) = 1/(1000000 / 1482691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9846467 / 25000000) (393858681 / 1000000000) (Real.log (1482691 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1482691 / 1000000) = -Real.log (1000000 / 1482691) := by
    rw [show ((1482691 / 1000000) : ℝ) = ((1000000 / 1482691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (82389363 / 125000000) ≤ -Real.log (517309 / 1000000) ∧
    -Real.log (517309 / 1000000) ≤ (131822981 / 200000000) := by
  have h := checkLog_sound (w := (482691 / 1517309)) (n := 12)
    (lo := (82389363 / 125000000)) (hi := (131822981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 517309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 517309) = 1/(517309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-131822981 / 200000000) (-82389363 / 125000000) (Real.log (517309 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (49383573 / 125000000) ≤ -Real.log (500000 / 742243) ∧
    -Real.log (500000 / 742243) ≤ (79013717 / 200000000) := by
  have h := checkLog_sound (w := (242243 / 1242243)) (n := 12)
    (lo := (49383573 / 125000000)) (hi := (79013717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742243 / 500000) = 1/(500000 / 742243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (49383573 / 125000000) (79013717 / 200000000) (Real.log (742243 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (742243 / 500000) = -Real.log (500000 / 742243) := by
    rw [show ((742243 / 500000) : ℝ) = ((500000 / 742243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (662590817 / 1000000000) ≤ -Real.log (257757 / 500000) ∧
    -Real.log (257757 / 500000) ≤ (331295409 / 500000000) := by
  have h := checkLog_sound (w := (242243 / 757757)) (n := 12)
    (lo := (662590817 / 1000000000)) (hi := (331295409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 257757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 257757) = 1/(257757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-331295409 / 500000000) (-662590817 / 1000000000) (Real.log (257757 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (77745563 / 250000000) ≤ -Real.log (200000 / 272953) ∧
    -Real.log (200000 / 272953) ≤ (310982253 / 1000000000) := by
  have h := checkLog_sound (w := (72953 / 472953)) (n := 12)
    (lo := (77745563 / 250000000)) (hi := (310982253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272953 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272953 / 200000) = 1/(200000 / 272953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (77745563 / 250000000) (310982253 / 1000000000) (Real.log (272953 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (272953 / 200000) = -Real.log (200000 / 272953) := by
    rw [show ((272953 / 200000) : ℝ) = ((200000 / 272953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (453760269 / 1000000000) ≤ -Real.log (127047 / 200000) ∧
    -Real.log (127047 / 200000) ≤ (45376027 / 100000000) := by
  have h := checkLog_sound (w := (72953 / 327047)) (n := 12)
    (lo := (453760269 / 1000000000)) (hi := (45376027 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 127047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 127047) = 1/(127047 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-45376027 / 100000000) (-453760269 / 1000000000) (Real.log (127047 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (312112211 / 1000000000) ≤ -Real.log (250000 / 341577) ∧
    -Real.log (250000 / 341577) ≤ (78028053 / 250000000) := by
  have h := checkLog_sound (w := (91577 / 591577)) (n := 12)
    (lo := (312112211 / 1000000000)) (hi := (78028053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341577 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341577 / 250000) = 1/(250000 / 341577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (312112211 / 1000000000) (78028053 / 250000000) (Real.log (341577 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (341577 / 250000) = -Real.log (250000 / 341577) := by
    rw [show ((341577 / 250000) : ℝ) = ((250000 / 341577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (456192247 / 1000000000) ≤ -Real.log (158423 / 250000) ∧
    -Real.log (158423 / 250000) ≤ (57024031 / 125000000) := by
  have h := checkLog_sound (w := (91577 / 408423)) (n := 12)
    (lo := (456192247 / 1000000000)) (hi := (57024031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 158423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 158423) = 1/(158423 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-57024031 / 125000000) (-456192247 / 1000000000) (Real.log (158423 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1052973583 / 1000000000) ≤ -Real.log (25000000000 / 71654030763) ∧
    -Real.log (25000000000 / 71654030763) ≤ (210594717 / 200000000) := by
  have h := checkLog_sound (w := (21654030763 / 121654030763)) (n := 12)
    (lo := (359826403 / 1000000000)) (hi := (89956601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71654030763 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(71654030763 / 50000000000) = 1/(25000000000 / 71654030763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1052973583 / 1000000000) (210594717 / 200000000) (Real.log (71654030763 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (71654030763 / 25000000000) = -Real.log (25000000000 / 71654030763) := by
    rw [show ((71654030763 / 25000000000) : ℝ) = ((25000000000 / 71654030763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1057659401 / 1000000000) ≤ -Real.log (62500000000 / 179976440989) ∧
    -Real.log (62500000000 / 179976440989) ≤ (1057659403 / 1000000000) := by
  have h := checkLog_sound (w := (54976440989 / 304976440989)) (n := 12)
    (lo := (364512221 / 1000000000)) (hi := (182256111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179976440989 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(179976440989 / 125000000000) = 1/(62500000000 / 179976440989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1057659401 / 1000000000) (1057659403 / 1000000000) (Real.log (179976440989 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179976440989 / 62500000000) = -Real.log (62500000000 / 179976440989) := by
    rw [show ((179976440989 / 62500000000) : ℝ) = ((62500000000 / 179976440989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (764742521 / 1000000000) ≤ -Real.log (500000000000 / 1074220564043) ∧
    -Real.log (500000000000 / 1074220564043) ≤ (764742523 / 1000000000) := by
  have h := checkLog_sound (w := (74220564043 / 2074220564043)) (n := 12)
    (lo := (71595341 / 1000000000)) (hi := (35797671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1074220564043 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1074220564043 / 1000000000000) = 1/(500000000000 / 1074220564043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (764742521 / 1000000000) (764742523 / 1000000000) (Real.log (1074220564043 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1074220564043 / 500000000000) = -Real.log (500000000000 / 1074220564043) := by
    rw [show ((1074220564043 / 500000000000) : ℝ) = ((500000000000 / 1074220564043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (384152229 / 500000000) ≤ -Real.log (500000000000 / 1078053691699) ∧
    -Real.log (500000000000 / 1078053691699) ≤ (38415223 / 50000000) := by
  have h := checkLog_sound (w := (78053691699 / 2078053691699)) (n := 12)
    (lo := (37578639 / 500000000)) (hi := (75157279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078053691699 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1078053691699 / 1000000000000) = 1/(500000000000 / 1078053691699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (384152229 / 500000000) (38415223 / 50000000) (Real.log (1078053691699 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1078053691699 / 500000000000) = -Real.log (500000000000 / 1078053691699) := by
    rw [show ((1078053691699 / 500000000000) : ℝ) = ((500000000000 / 1078053691699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0152

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0153Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0153
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

theorem reflection_log_1_neg : (57575473 / 200000000) ≤ -Real.log (1280 / 1707) ∧
    -Real.log (1280 / 1707) ≤ (143938683 / 500000000) := by
  have h := checkLog_sound (w := (427 / 2987)) (n := 12)
    (lo := (57575473 / 200000000)) (hi := (143938683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1707 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1707 / 1280) = 1/(1280 / 1707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (57575473 / 200000000) (143938683 / 500000000) (Real.log (1707 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1707 / 1280) = -Real.log (1280 / 1707) := by
    rw [show ((1707 / 1280) : ℝ) = ((1280 / 1707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (405855809 / 1000000000) ≤ -Real.log (853 / 1280) ∧
    -Real.log (853 / 1280) ≤ (40585581 / 100000000) := by
  have h := checkLog_sound (w := (427 / 2133)) (n := 12)
    (lo := (405855809 / 1000000000)) (hi := (40585581 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 853) = 1/(853 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-40585581 / 100000000) (-405855809 / 1000000000) (Real.log (853 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (71749561 / 250000000) ≤ -Real.log (2560 / 3411) ∧
    -Real.log (2560 / 3411) ≤ (57399649 / 200000000) := by
  have h := checkLog_sound (w := (851 / 5971)) (n := 12)
    (lo := (71749561 / 250000000)) (hi := (57399649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3411 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3411 / 2560) = 1/(2560 / 3411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (71749561 / 250000000) (57399649 / 200000000) (Real.log (3411 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3411 / 2560) = -Real.log (2560 / 3411) := by
    rw [show ((3411 / 2560) : ℝ) = ((2560 / 3411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (202049427 / 500000000) ≤ -Real.log (1709 / 2560) ∧
    -Real.log (1709 / 2560) ≤ (80819771 / 200000000) := by
  have h := checkLog_sound (w := (851 / 4269)) (n := 12)
    (lo := (202049427 / 500000000)) (hi := (80819771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1709) = 1/(1709 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-80819771 / 200000000) (-202049427 / 500000000) (Real.log (1709 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (255569037 / 500000000) ≤ -Real.log (640 / 1067) ∧
    -Real.log (640 / 1067) ≤ (20445523 / 40000000) := by
  have h := checkLog_sound (w := (427 / 1707)) (n := 12)
    (lo := (255569037 / 500000000)) (hi := (20445523 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1067 / 640) = 1/(640 / 1067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (255569037 / 500000000) (20445523 / 40000000) (Real.log (1067 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1067 / 640) = -Real.log (640 / 1067) := by
    rw [show ((1067 / 640) : ℝ) = ((640 / 1067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (110017601 / 100000000) ≤ -Real.log (213 / 640) ∧
    -Real.log (213 / 640) ≤ (275044003 / 250000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 213) = 1/(213 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-275044003 / 250000000) (-110017601 / 100000000) (Real.log (213 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (20389251 / 40000000) ≤ -Real.log (1280 / 2131) ∧
    -Real.log (1280 / 2131) ≤ (127432819 / 250000000) := by
  have h := checkLog_sound (w := (851 / 3411)) (n := 12)
    (lo := (20389251 / 40000000)) (hi := (127432819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2131 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2131 / 1280) = 1/(1280 / 2131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (20389251 / 40000000) (127432819 / 250000000) (Real.log (2131 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2131 / 1280) = -Real.log (1280 / 2131) := by
    rw [show ((2131 / 1280) : ℝ) = ((1280 / 2131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1093158437 / 1000000000) ≤ -Real.log (429 / 1280) ∧
    -Real.log (429 / 1280) ≤ (1093158439 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 429) = 1/(429 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1093158439 / 1000000000) (-1093158437 / 1000000000) (Real.log (429 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78529867 / 200000000) ≤ -Real.log (1000000 / 1480899) ∧
    -Real.log (1000000 / 1480899) ≤ (49081167 / 125000000) := by
  have h := checkLog_sound (w := (480899 / 2480899)) (n := 12)
    (lo := (78529867 / 200000000)) (hi := (49081167 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1480899 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1480899 / 1000000) = 1/(1000000 / 1480899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78529867 / 200000000) (49081167 / 125000000) (Real.log (1480899 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1480899 / 1000000) = -Real.log (1000000 / 1480899) := by
    rw [show ((1480899 / 1000000) : ℝ) = ((1000000 / 1480899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (655656809 / 1000000000) ≤ -Real.log (519101 / 1000000) ∧
    -Real.log (519101 / 1000000) ≤ (65565681 / 100000000) := by
  have h := checkLog_sound (w := (480899 / 1519101)) (n := 12)
    (lo := (655656809 / 1000000000)) (hi := (65565681 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 519101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 519101) = 1/(519101 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-65565681 / 100000000) (-655656809 / 1000000000) (Real.log (519101 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (196929677 / 500000000) ≤ -Real.log (250000 / 370673) ∧
    -Real.log (250000 / 370673) ≤ (78771871 / 200000000) := by
  have h := checkLog_sound (w := (120673 / 620673)) (n := 12)
    (lo := (196929677 / 500000000)) (hi := (78771871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370673 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370673 / 250000) = 1/(250000 / 370673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (196929677 / 500000000) (78771871 / 200000000) (Real.log (370673 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (370673 / 250000) = -Real.log (250000 / 370673) := by
    rw [show ((370673 / 250000) : ℝ) = ((250000 / 370673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (659116837 / 1000000000) ≤ -Real.log (129327 / 250000) ∧
    -Real.log (129327 / 250000) ≤ (329558419 / 500000000) := by
  have h := checkLog_sound (w := (120673 / 379327)) (n := 12)
    (lo := (659116837 / 1000000000)) (hi := (329558419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 129327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 129327) = 1/(129327 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-329558419 / 500000000) (-659116837 / 1000000000) (Real.log (129327 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (309854683 / 1000000000) ≤ -Real.log (1000000 / 1363227) ∧
    -Real.log (1000000 / 1363227) ≤ (77463671 / 250000000) := by
  have h := checkLog_sound (w := (363227 / 2363227)) (n := 12)
    (lo := (309854683 / 1000000000)) (hi := (77463671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363227 / 1000000) = 1/(1000000 / 1363227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (309854683 / 1000000000) (77463671 / 250000000) (Real.log (1363227 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1363227 / 1000000) = -Real.log (1000000 / 1363227) := by
    rw [show ((1363227 / 1000000) : ℝ) = ((1000000 / 1363227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (112835511 / 250000000) ≤ -Real.log (636773 / 1000000) ∧
    -Real.log (636773 / 1000000) ≤ (90268409 / 200000000) := by
  have h := checkLog_sound (w := (363227 / 1636773)) (n := 12)
    (lo := (112835511 / 250000000)) (hi := (90268409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 636773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 636773) = 1/(636773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-90268409 / 200000000) (-112835511 / 250000000) (Real.log (636773 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (62196597 / 200000000) ≤ -Real.log (500000 / 682383) ∧
    -Real.log (500000 / 682383) ≤ (155491493 / 500000000) := by
  have h := checkLog_sound (w := (182383 / 1182383)) (n := 12)
    (lo := (62196597 / 200000000)) (hi := (155491493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682383 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682383 / 500000) = 1/(500000 / 682383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (62196597 / 200000000) (155491493 / 500000000) (Real.log (682383 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (682383 / 500000) = -Real.log (500000 / 682383) := by
    rw [show ((682383 / 500000) : ℝ) = ((500000 / 682383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (113440461 / 250000000) ≤ -Real.log (317617 / 500000) ∧
    -Real.log (317617 / 500000) ≤ (90752369 / 200000000) := by
  have h := checkLog_sound (w := (182383 / 817617)) (n := 12)
    (lo := (113440461 / 250000000)) (hi := (90752369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 317617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 317617) = 1/(317617 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-90752369 / 200000000) (-113440461 / 250000000) (Real.log (317617 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (32759567 / 31250000) ≤ -Real.log (20000000000 / 57056295403) ∧
    -Real.log (20000000000 / 57056295403) ≤ (524153073 / 500000000) := by
  have h := checkLog_sound (w := (17056295403 / 97056295403)) (n := 12)
    (lo := (88789741 / 250000000)) (hi := (71031793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57056295403 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(57056295403 / 40000000000) = 1/(20000000000 / 57056295403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (32759567 / 31250000) (524153073 / 500000000) (Real.log (57056295403 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (57056295403 / 20000000000) = -Real.log (20000000000 / 57056295403) := by
    rw [show ((57056295403 / 20000000000) : ℝ) = ((20000000000 / 57056295403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1052976191 / 1000000000) ≤ -Real.log (500000000000 / 1433084352069) ∧
    -Real.log (500000000000 / 1433084352069) ≤ (1052976193 / 1000000000) := by
  have h := checkLog_sound (w := (433084352069 / 2433084352069)) (n := 12)
    (lo := (359829011 / 1000000000)) (hi := (89957253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433084352069 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1433084352069 / 1000000000000) = 1/(500000000000 / 1433084352069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1052976191 / 1000000000) (1052976193 / 1000000000) (Real.log (1433084352069 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1433084352069 / 500000000000) = -Real.log (500000000000 / 1433084352069) := by
    rw [show ((1433084352069 / 500000000000) : ℝ) = ((500000000000 / 1433084352069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (761196727 / 1000000000) ≤ -Real.log (250000000000 / 535209171871) ∧
    -Real.log (250000000000 / 535209171871) ≤ (761196729 / 1000000000) := by
  have h := checkLog_sound (w := (35209171871 / 1035209171871)) (n := 12)
    (lo := (68049547 / 1000000000)) (hi := (17012387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((535209171871 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(535209171871 / 500000000000) = 1/(250000000000 / 535209171871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (761196727 / 1000000000) (761196729 / 1000000000) (Real.log (535209171871 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (535209171871 / 250000000000) = -Real.log (250000000000 / 535209171871) := by
    rw [show ((535209171871 / 250000000000) : ℝ) = ((250000000000 / 535209171871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (191186207 / 250000000) ≤ -Real.log (250000000000 / 537111521109) ∧
    -Real.log (250000000000 / 537111521109) ≤ (76474483 / 100000000) := by
  have h := checkLog_sound (w := (37111521109 / 1037111521109)) (n := 12)
    (lo := (4474853 / 62500000)) (hi := (71597649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537111521109 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(537111521109 / 500000000000) = 1/(250000000000 / 537111521109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (191186207 / 250000000) (76474483 / 100000000) (Real.log (537111521109 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (537111521109 / 250000000000) = -Real.log (250000000000 / 537111521109) := by
    rw [show ((537111521109 / 250000000000) : ℝ) = ((250000000000 / 537111521109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0153

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0154Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0154
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

theorem reflection_log_1_neg : (71749561 / 250000000) ≤ -Real.log (2560 / 3411) ∧
    -Real.log (2560 / 3411) ≤ (57399649 / 200000000) := by
  have h := checkLog_sound (w := (851 / 5971)) (n := 12)
    (lo := (71749561 / 250000000)) (hi := (57399649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3411 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3411 / 2560) = 1/(2560 / 3411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (71749561 / 250000000) (57399649 / 200000000) (Real.log (3411 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3411 / 2560) = -Real.log (2560 / 3411) := by
    rw [show ((3411 / 2560) : ℝ) = ((2560 / 3411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (202049427 / 500000000) ≤ -Real.log (1709 / 2560) ∧
    -Real.log (1709 / 2560) ≤ (80819771 / 200000000) := by
  have h := checkLog_sound (w := (851 / 4269)) (n := 12)
    (lo := (202049427 / 500000000)) (hi := (80819771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1709) = 1/(1709 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-80819771 / 200000000) (-202049427 / 500000000) (Real.log (1709 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5722367 / 20000000) ≤ -Real.log (160 / 213) ∧
    -Real.log (160 / 213) ≤ (286118351 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 373)) (n := 12)
    (lo := (5722367 / 20000000)) (hi := (286118351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213 / 160) = 1/(160 / 213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5722367 / 20000000) (286118351 / 1000000000) (Real.log (213 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (213 / 160) = -Real.log (160 / 213) := by
    rw [show ((213 / 160) : ℝ) = ((160 / 213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20117249 / 50000000) ≤ -Real.log (107 / 160) ∧
    -Real.log (107 / 160) ≤ (402344981 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 267)) (n := 12)
    (lo := (20117249 / 50000000)) (hi := (402344981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 107) = 1/(107 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-402344981 / 1000000000) (-20117249 / 50000000) (Real.log (107 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (20389251 / 40000000) ≤ -Real.log (1280 / 2131) ∧
    -Real.log (1280 / 2131) ≤ (127432819 / 250000000) := by
  have h := checkLog_sound (w := (851 / 3411)) (n := 12)
    (lo := (20389251 / 40000000)) (hi := (127432819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2131 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2131 / 1280) = 1/(1280 / 2131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (20389251 / 40000000) (127432819 / 250000000) (Real.log (2131 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2131 / 1280) = -Real.log (1280 / 2131) := by
    rw [show ((2131 / 1280) : ℝ) = ((1280 / 2131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1093158437 / 1000000000) ≤ -Real.log (429 / 1280) ∧
    -Real.log (429 / 1280) ≤ (1093158439 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 429) = 1/(429 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1093158439 / 1000000000) (-1093158437 / 1000000000) (Real.log (429 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (508322493 / 1000000000) ≤ -Real.log (80 / 133) ∧
    -Real.log (80 / 133) ≤ (254161247 / 500000000) := by
  have h := checkLog_sound (w := (53 / 213)) (n := 12)
    (lo := (508322493 / 1000000000)) (hi := (254161247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133 / 80) = 1/(80 / 133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (508322493 / 1000000000) (254161247 / 500000000) (Real.log (133 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (133 / 80) = -Real.log (80 / 133) := by
    rw [show ((133 / 80) : ℝ) = ((80 / 133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (135773721 / 125000000) ≤ -Real.log (27 / 80) ∧
    -Real.log (27 / 80) ≤ (108618977 / 100000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 27) = 1/(27 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-108618977 / 100000000) (-135773721 / 125000000) (Real.log (27 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (391438527 / 1000000000) ≤ -Real.log (1000000 / 1479107) ∧
    -Real.log (1000000 / 1479107) ≤ (6116227 / 15625000) := by
  have h := checkLog_sound (w := (479107 / 2479107)) (n := 12)
    (lo := (391438527 / 1000000000)) (hi := (6116227 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1479107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1479107 / 1000000) = 1/(1000000 / 1479107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (391438527 / 1000000000) (6116227 / 15625000) (Real.log (1479107 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1479107 / 1000000) = -Real.log (1000000 / 1479107) := by
    rw [show ((1479107 / 1000000) : ℝ) = ((1000000 / 1479107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81526329 / 125000000) ≤ -Real.log (520893 / 1000000) ∧
    -Real.log (520893 / 1000000) ≤ (652210633 / 1000000000) := by
  have h := checkLog_sound (w := (479107 / 1520893)) (n := 12)
    (lo := (81526329 / 125000000)) (hi := (652210633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 520893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 520893) = 1/(520893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-652210633 / 1000000000) (-81526329 / 125000000) (Real.log (520893 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (392650011 / 1000000000) ≤ -Real.log (10000 / 14809) ∧
    -Real.log (10000 / 14809) ≤ (98162503 / 250000000) := by
  have h := checkLog_sound (w := (4809 / 24809)) (n := 12)
    (lo := (392650011 / 1000000000)) (hi := (98162503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14809 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14809 / 10000) = 1/(10000 / 14809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (392650011 / 1000000000) (98162503 / 250000000) (Real.log (14809 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (14809 / 10000) = -Real.log (10000 / 14809) := by
    rw [show ((14809 / 10000) : ℝ) = ((10000 / 14809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (40978671 / 62500000) ≤ -Real.log (5191 / 10000) ∧
    -Real.log (5191 / 10000) ≤ (655658737 / 1000000000) := by
  have h := checkLog_sound (w := (4809 / 15191)) (n := 12)
    (lo := (40978671 / 62500000)) (hi := (655658737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 5191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 5191) = 1/(5191 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-655658737 / 1000000000) (-40978671 / 62500000) (Real.log (5191 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (77182011 / 250000000) ≤ -Real.log (250000 / 340423) ∧
    -Real.log (250000 / 340423) ≤ (61745609 / 200000000) := by
  have h := checkLog_sound (w := (90423 / 590423)) (n := 12)
    (lo := (77182011 / 250000000)) (hi := (61745609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340423 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340423 / 250000) = 1/(250000 / 340423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (77182011 / 250000000) (61745609 / 200000000) (Real.log (340423 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (340423 / 250000) = -Real.log (250000 / 340423) := by
    rw [show ((340423 / 250000) : ℝ) = ((250000 / 340423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (448934353 / 1000000000) ≤ -Real.log (159577 / 250000) ∧
    -Real.log (159577 / 250000) ≤ (224467177 / 500000000) := by
  have h := checkLog_sound (w := (90423 / 409577)) (n := 12)
    (lo := (448934353 / 1000000000)) (hi := (224467177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159577) = 1/(159577 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-224467177 / 500000000) (-448934353 / 1000000000) (Real.log (159577 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38731927 / 125000000) ≤ -Real.log (250000 / 340807) ∧
    -Real.log (250000 / 340807) ≤ (309855417 / 1000000000) := by
  have h := checkLog_sound (w := (90807 / 590807)) (n := 12)
    (lo := (38731927 / 125000000)) (hi := (309855417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340807 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340807 / 250000) = 1/(250000 / 340807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38731927 / 125000000) (309855417 / 1000000000) (Real.log (340807 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (340807 / 250000) = -Real.log (250000 / 340807) := by
    rw [show ((340807 / 250000) : ℝ) = ((250000 / 340807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (90268723 / 200000000) ≤ -Real.log (159193 / 250000) ∧
    -Real.log (159193 / 250000) ≤ (1763061 / 3906250) := by
  have h := checkLog_sound (w := (90807 / 409193)) (n := 12)
    (lo := (90268723 / 200000000)) (hi := (1763061 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159193) = 1/(159193 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1763061 / 3906250) (-90268723 / 200000000) (Real.log (159193 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1043649159 / 1000000000) ≤ -Real.log (100000000000 / 283956013999) ∧
    -Real.log (100000000000 / 283956013999) ≤ (1043649161 / 1000000000) := by
  have h := checkLog_sound (w := (83956013999 / 483956013999)) (n := 12)
    (lo := (350501979 / 1000000000)) (hi := (17525099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283956013999 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(283956013999 / 200000000000) = 1/(100000000000 / 283956013999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1043649159 / 1000000000) (1043649161 / 1000000000) (Real.log (283956013999 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (283956013999 / 100000000000) = -Real.log (100000000000 / 283956013999) := by
    rw [show ((283956013999 / 100000000000) : ℝ) = ((100000000000 / 283956013999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (524154373 / 500000000) ≤ -Real.log (7812500000 / 22287673377) ∧
    -Real.log (7812500000 / 22287673377) ≤ (262077187 / 250000000) := by
  have h := checkLog_sound (w := (6662673377 / 37912673377)) (n := 12)
    (lo := (177580783 / 500000000)) (hi := (355161567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22287673377 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(22287673377 / 15625000000) = 1/(7812500000 / 22287673377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (524154373 / 500000000) (262077187 / 250000000) (Real.log (22287673377 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (22287673377 / 7812500000) = -Real.log (7812500000 / 22287673377) := by
    rw [show ((22287673377 / 7812500000) : ℝ) = ((7812500000 / 22287673377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (757662397 / 1000000000) ≤ -Real.log (500000000000 / 1066641809283) ∧
    -Real.log (500000000000 / 1066641809283) ≤ (757662399 / 1000000000) := by
  have h := checkLog_sound (w := (66641809283 / 2066641809283)) (n := 12)
    (lo := (64515217 / 1000000000)) (hi := (32257609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1066641809283 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1066641809283 / 1000000000000) = 1/(500000000000 / 1066641809283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (757662397 / 1000000000) (757662399 / 1000000000) (Real.log (1066641809283 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1066641809283 / 500000000000) = -Real.log (500000000000 / 1066641809283) := by
    rw [show ((1066641809283 / 500000000000) : ℝ) = ((500000000000 / 1066641809283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (761199031 / 1000000000) ≤ -Real.log (500000000000 / 1070420809961) ∧
    -Real.log (500000000000 / 1070420809961) ≤ (761199033 / 1000000000) := by
  have h := checkLog_sound (w := (70420809961 / 2070420809961)) (n := 12)
    (lo := (68051851 / 1000000000)) (hi := (17012963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1070420809961 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1070420809961 / 1000000000000) = 1/(500000000000 / 1070420809961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (761199031 / 1000000000) (761199033 / 1000000000) (Real.log (1070420809961 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1070420809961 / 500000000000) = -Real.log (500000000000 / 1070420809961) := by
    rw [show ((1070420809961 / 500000000000) : ℝ) = ((500000000000 / 1070420809961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0154

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0155Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0155
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

theorem reflection_log_1_neg : (5722367 / 20000000) ≤ -Real.log (160 / 213) ∧
    -Real.log (160 / 213) ≤ (286118351 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 373)) (n := 12)
    (lo := (5722367 / 20000000)) (hi := (286118351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213 / 160) = 1/(160 / 213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5722367 / 20000000) (286118351 / 1000000000) (Real.log (213 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (213 / 160) = -Real.log (160 / 213) := by
    rw [show ((213 / 160) : ℝ) = ((160 / 213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20117249 / 50000000) ≤ -Real.log (107 / 160) ∧
    -Real.log (107 / 160) ≤ (402344981 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 267)) (n := 12)
    (lo := (20117249 / 50000000)) (hi := (402344981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 107) = 1/(107 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-402344981 / 1000000000) (-20117249 / 50000000) (Real.log (107 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (285237681 / 1000000000) ≤ -Real.log (512 / 681) ∧
    -Real.log (512 / 681) ≤ (142618841 / 500000000) := by
  have h := checkLog_sound (w := (169 / 1193)) (n := 12)
    (lo := (285237681 / 1000000000)) (hi := (142618841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681 / 512) = 1/(512 / 681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (285237681 / 1000000000) (142618841 / 500000000) (Real.log (681 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (681 / 512) = -Real.log (512 / 681) := by
    rw [show ((681 / 512) : ℝ) = ((512 / 681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (400594177 / 1000000000) ≤ -Real.log (343 / 512) ∧
    -Real.log (343 / 512) ≤ (200297089 / 500000000) := by
  have h := checkLog_sound (w := (169 / 855)) (n := 12)
    (lo := (400594177 / 1000000000)) (hi := (200297089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 343) = 1/(343 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-200297089 / 500000000) (-400594177 / 1000000000) (Real.log (343 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (508322493 / 1000000000) ≤ -Real.log (80 / 133) ∧
    -Real.log (80 / 133) ≤ (254161247 / 500000000) := by
  have h := checkLog_sound (w := (53 / 213)) (n := 12)
    (lo := (508322493 / 1000000000)) (hi := (254161247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133 / 80) = 1/(80 / 133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (508322493 / 1000000000) (254161247 / 500000000) (Real.log (133 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (133 / 80) = -Real.log (80 / 133) := by
    rw [show ((133 / 80) : ℝ) = ((80 / 133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (135773721 / 125000000) ≤ -Real.log (27 / 80) ∧
    -Real.log (27 / 80) ≤ (108618977 / 100000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 27) = 1/(27 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-108618977 / 100000000) (-135773721 / 125000000) (Real.log (27 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (126727931 / 250000000) ≤ -Real.log (256 / 425) ∧
    -Real.log (256 / 425) ≤ (20276469 / 40000000) := by
  have h := checkLog_sound (w := (169 / 681)) (n := 12)
    (lo := (126727931 / 250000000)) (hi := (20276469 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425 / 256) = 1/(256 / 425) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (126727931 / 250000000) (20276469 / 40000000) (Real.log (425 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (425 / 256) = -Real.log (256 / 425) := by
    rw [show ((425 / 256) : ℝ) = ((256 / 425) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (43170773 / 40000000) ≤ -Real.log (87 / 256) ∧
    -Real.log (87 / 256) ≤ (1079269327 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 215)) (n := 12)
    (lo := (77224429 / 200000000)) (hi := (193061073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 87) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 87) = 1/(87 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1079269327 / 1000000000) (-43170773 / 40000000) (Real.log (87 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (390228281 / 1000000000) ≤ -Real.log (500000 / 738659) ∧
    -Real.log (500000 / 738659) ≤ (195114141 / 500000000) := by
  have h := checkLog_sound (w := (238659 / 1238659)) (n := 12)
    (lo := (390228281 / 1000000000)) (hi := (195114141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738659 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738659 / 500000) = 1/(500000 / 738659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (390228281 / 1000000000) (195114141 / 500000000) (Real.log (738659 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (738659 / 500000) = -Real.log (500000 / 738659) := by
    rw [show ((738659 / 500000) : ℝ) = ((500000 / 738659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (64878203 / 100000000) ≤ -Real.log (261341 / 500000) ∧
    -Real.log (261341 / 500000) ≤ (648782031 / 1000000000) := by
  have h := checkLog_sound (w := (238659 / 761341)) (n := 12)
    (lo := (64878203 / 100000000)) (hi := (648782031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 261341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 261341) = 1/(261341 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-648782031 / 1000000000) (-64878203 / 100000000) (Real.log (261341 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (391439203 / 1000000000) ≤ -Real.log (250000 / 369777) ∧
    -Real.log (250000 / 369777) ≤ (97859801 / 250000000) := by
  have h := checkLog_sound (w := (119777 / 619777)) (n := 12)
    (lo := (391439203 / 1000000000)) (hi := (97859801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369777 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369777 / 250000) = 1/(250000 / 369777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (391439203 / 1000000000) (97859801 / 250000000) (Real.log (369777 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (369777 / 250000) = -Real.log (250000 / 369777) := by
    rw [show ((369777 / 250000) : ℝ) = ((250000 / 369777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81526569 / 125000000) ≤ -Real.log (130223 / 250000) ∧
    -Real.log (130223 / 250000) ≤ (652212553 / 1000000000) := by
  have h := checkLog_sound (w := (119777 / 380223)) (n := 12)
    (lo := (81526569 / 125000000)) (hi := (652212553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 130223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 130223) = 1/(130223 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-652212553 / 1000000000) (-81526569 / 125000000) (Real.log (130223 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (307602339 / 1000000000) ≤ -Real.log (6250 / 8501) ∧
    -Real.log (6250 / 8501) ≤ (15380117 / 50000000) := by
  have h := checkLog_sound (w := (2251 / 14751)) (n := 12)
    (lo := (307602339 / 1000000000)) (hi := (15380117 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8501 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8501 / 6250) = 1/(6250 / 8501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (307602339 / 1000000000) (15380117 / 50000000) (Real.log (8501 / 6250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (8501 / 6250) = -Real.log (6250 / 8501) := by
    rw [show ((8501 / 6250) : ℝ) = ((6250 / 8501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (446537133 / 1000000000) ≤ -Real.log (3999 / 6250) ∧
    -Real.log (3999 / 6250) ≤ (223268567 / 500000000) := by
  have h := checkLog_sound (w := (2251 / 10249)) (n := 12)
    (lo := (446537133 / 1000000000)) (hi := (223268567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 3999) = 1/(3999 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-223268567 / 500000000) (-446537133 / 1000000000) (Real.log (3999 / 6250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (154364389 / 500000000) ≤ -Real.log (1000000 / 1361693) ∧
    -Real.log (1000000 / 1361693) ≤ (308728779 / 1000000000) := by
  have h := checkLog_sound (w := (361693 / 2361693)) (n := 12)
    (lo := (154364389 / 500000000)) (hi := (308728779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361693 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1361693 / 1000000) = 1/(1000000 / 1361693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (154364389 / 500000000) (308728779 / 1000000000) (Real.log (1361693 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1361693 / 1000000) = -Real.log (1000000 / 1361693) := by
    rw [show ((1361693 / 1000000) : ℝ) = ((1000000 / 1361693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (5611699 / 12500000) ≤ -Real.log (638307 / 1000000) ∧
    -Real.log (638307 / 1000000) ≤ (448935921 / 1000000000) := by
  have h := checkLog_sound (w := (361693 / 1638307)) (n := 12)
    (lo := (5611699 / 12500000)) (hi := (448935921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 638307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 638307) = 1/(638307 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-448935921 / 1000000000) (-5611699 / 12500000) (Real.log (638307 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1039010311 / 1000000000) ≤ -Real.log (125000000000 / 353302294703) ∧
    -Real.log (125000000000 / 353302294703) ≤ (1039010313 / 1000000000) := by
  have h := checkLog_sound (w := (103302294703 / 603302294703)) (n := 12)
    (lo := (345863131 / 1000000000)) (hi := (86465783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353302294703 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(353302294703 / 250000000000) = 1/(125000000000 / 353302294703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1039010311 / 1000000000) (1039010313 / 1000000000) (Real.log (353302294703 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (353302294703 / 125000000000) = -Real.log (125000000000 / 353302294703) := by
    rw [show ((353302294703 / 125000000000) : ℝ) = ((125000000000 / 353302294703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (208730351 / 200000000) ≤ -Real.log (250000000000 / 709891877779) ∧
    -Real.log (250000000000 / 709891877779) ≤ (1043651757 / 1000000000) := by
  have h := checkLog_sound (w := (209891877779 / 1209891877779)) (n := 12)
    (lo := (14020183 / 40000000)) (hi := (2738317 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709891877779 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(709891877779 / 500000000000) = 1/(250000000000 / 709891877779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (208730351 / 200000000) (1043651757 / 1000000000) (Real.log (709891877779 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (709891877779 / 250000000000) = -Real.log (250000000000 / 709891877779) := by
    rw [show ((709891877779 / 250000000000) : ℝ) = ((250000000000 / 709891877779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (754139473 / 1000000000) ≤ -Real.log (12500000000 / 26572268067) ∧
    -Real.log (12500000000 / 26572268067) ≤ (30165579 / 40000000) := by
  have h := checkLog_sound (w := (1572268067 / 51572268067)) (n := 12)
    (lo := (60992293 / 1000000000)) (hi := (30496147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26572268067 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(26572268067 / 25000000000) = 1/(12500000000 / 26572268067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (754139473 / 1000000000) (30165579 / 40000000) (Real.log (26572268067 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26572268067 / 12500000000) = -Real.log (12500000000 / 26572268067) := by
    rw [show ((26572268067 / 12500000000) : ℝ) = ((12500000000 / 26572268067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (378832349 / 500000000) ≤ -Real.log (250000000000 / 533322131827) ∧
    -Real.log (250000000000 / 533322131827) ≤ (7576647 / 10000000) := by
  have h := checkLog_sound (w := (33322131827 / 1033322131827)) (n := 12)
    (lo := (32258759 / 500000000)) (hi := (64517519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((533322131827 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(533322131827 / 500000000000) = 1/(250000000000 / 533322131827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (378832349 / 500000000) (7576647 / 10000000) (Real.log (533322131827 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (533322131827 / 250000000000) = -Real.log (250000000000 / 533322131827) := by
    rw [show ((533322131827 / 250000000000) : ℝ) = ((250000000000 / 533322131827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0155

end


