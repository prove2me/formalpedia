-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0219Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0219Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:11:44.999188+00:00
-- url     : https://prove2.me/theorems/f389bdaf-9b9a-4a00-88d9-b6f0a0c200de
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0219Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0220Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0219Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0220Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0221Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0222Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0223Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0224Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0225Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0219Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0220Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0221Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0222Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0223Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0224Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0225Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0219Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0220Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0221Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0222Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0223Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0224Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0225Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0219Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0220Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0221Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0222Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0223Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0224Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0225Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0219Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0219
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

theorem reflection_log_1_neg : (32136497 / 125000000) ≤ -Real.log (5120 / 6621) ∧
    -Real.log (5120 / 6621) ≤ (257091977 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 11741)) (n := 12)
    (lo := (32136497 / 125000000)) (hi := (257091977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6621 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6621 / 5120) = 1/(5120 / 6621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (32136497 / 125000000) (257091977 / 1000000000) (Real.log (6621 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6621 / 5120) = -Real.log (5120 / 6621) := by
    rw [show ((6621 / 5120) : ℝ) = ((5120 / 6621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (173478347 / 500000000) ≤ -Real.log (3619 / 5120) ∧
    -Real.log (3619 / 5120) ≤ (69391339 / 200000000) := by
  have h := checkLog_sound (w := (1501 / 8739)) (n := 12)
    (lo := (173478347 / 500000000)) (hi := (69391339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3619) = 1/(3619 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-69391339 / 200000000) (-173478347 / 500000000) (Real.log (3619 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (25663877 / 100000000) ≤ -Real.log (2560 / 3309) ∧
    -Real.log (2560 / 3309) ≤ (256638771 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 5869)) (n := 12)
    (lo := (25663877 / 100000000)) (hi := (256638771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3309 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3309 / 2560) = 1/(2560 / 3309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (25663877 / 100000000) (256638771 / 1000000000) (Real.log (3309 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3309 / 2560) = -Real.log (2560 / 3309) := by
    rw [show ((3309 / 2560) : ℝ) = ((2560 / 3309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (346128079 / 1000000000) ≤ -Real.log (1811 / 2560) ∧
    -Real.log (1811 / 2560) ≤ (4326601 / 12500000) := by
  have h := checkLog_sound (w := (749 / 4371)) (n := 12)
    (lo := (346128079 / 1000000000)) (hi := (4326601 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1811) = 1/(1811 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4326601 / 12500000) (-346128079 / 1000000000) (Real.log (1811 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (46142199 / 100000000) ≤ -Real.log (2560 / 4061) ∧
    -Real.log (2560 / 4061) ≤ (461421991 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 6621)) (n := 12)
    (lo := (46142199 / 100000000)) (hi := (461421991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4061 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4061 / 2560) = 1/(2560 / 4061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (46142199 / 100000000) (461421991 / 1000000000) (Real.log (4061 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4061 / 2560) = -Real.log (2560 / 4061) := by
    rw [show ((4061 / 2560) : ℝ) = ((2560 / 4061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (882682191 / 1000000000) ≤ -Real.log (1059 / 2560) ∧
    -Real.log (1059 / 2560) ≤ (882682193 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 2339)) (n := 12)
    (lo := (189535011 / 1000000000)) (hi := (47383753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1059) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1059) = 1/(1059 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-882682193 / 1000000000) (-882682191 / 1000000000) (Real.log (1059 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (230341491 / 500000000) ≤ -Real.log (1280 / 2029) ∧
    -Real.log (1280 / 2029) ≤ (460682983 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 3309)) (n := 12)
    (lo := (230341491 / 500000000)) (hi := (460682983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2029 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2029 / 1280) = 1/(1280 / 2029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (230341491 / 500000000) (460682983 / 1000000000) (Real.log (2029 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2029 / 1280) = -Real.log (1280 / 2029) := by
    rw [show ((2029 / 1280) : ℝ) = ((1280 / 2029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (175970667 / 200000000) ≤ -Real.log (531 / 1280) ∧
    -Real.log (531 / 1280) ≤ (879853337 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1171)) (n := 12)
    (lo := (37341231 / 200000000)) (hi := (46676539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 531) = 1/(531 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-879853337 / 1000000000) (-175970667 / 200000000) (Real.log (531 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (175577669 / 500000000) ≤ -Real.log (250000 / 355177) ∧
    -Real.log (250000 / 355177) ≤ (351155339 / 1000000000) := by
  have h := checkLog_sound (w := (105177 / 605177)) (n := 12)
    (lo := (175577669 / 500000000)) (hi := (351155339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355177 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355177 / 250000) = 1/(250000 / 355177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (175577669 / 500000000) (351155339 / 1000000000) (Real.log (355177 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (355177 / 250000) = -Real.log (250000 / 355177) := by
    rw [show ((355177 / 250000) : ℝ) = ((250000 / 355177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (54594861 / 100000000) ≤ -Real.log (144823 / 250000) ∧
    -Real.log (144823 / 250000) ≤ (545948611 / 1000000000) := by
  have h := checkLog_sound (w := (105177 / 394823)) (n := 12)
    (lo := (54594861 / 100000000)) (hi := (545948611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 144823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 144823) = 1/(144823 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-545948611 / 1000000000) (-54594861 / 100000000) (Real.log (144823 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (175886223 / 500000000) ≤ -Real.log (200000 / 284317) ∧
    -Real.log (200000 / 284317) ≤ (351772447 / 1000000000) := by
  have h := checkLog_sound (w := (84317 / 484317)) (n := 12)
    (lo := (175886223 / 500000000)) (hi := (351772447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284317 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284317 / 200000) = 1/(200000 / 284317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (175886223 / 500000000) (351772447 / 1000000000) (Real.log (284317 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (284317 / 200000) = -Real.log (200000 / 284317) := by
    rw [show ((284317 / 200000) : ℝ) = ((200000 / 284317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (273731837 / 500000000) ≤ -Real.log (115683 / 200000) ∧
    -Real.log (115683 / 200000) ≤ (21898547 / 40000000) := by
  have h := checkLog_sound (w := (84317 / 315683)) (n := 12)
    (lo := (273731837 / 500000000)) (hi := (21898547 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 115683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 115683) = 1/(115683 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21898547 / 40000000) (-273731837 / 500000000) (Real.log (115683 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (272150073 / 1000000000) ≤ -Real.log (62500 / 82049) ∧
    -Real.log (62500 / 82049) ≤ (136075037 / 500000000) := by
  have h := checkLog_sound (w := (19549 / 144549)) (n := 12)
    (lo := (272150073 / 1000000000)) (hi := (136075037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82049 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82049 / 62500) = 1/(62500 / 82049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (272150073 / 1000000000) (136075037 / 500000000) (Real.log (82049 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (82049 / 62500) = -Real.log (62500 / 82049) := by
    rw [show ((82049 / 62500) : ℝ) = ((62500 / 82049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3000853 / 8000000) ≤ -Real.log (42951 / 62500) ∧
    -Real.log (42951 / 62500) ≤ (187553313 / 500000000) := by
  have h := checkLog_sound (w := (19549 / 105451)) (n := 12)
    (lo := (3000853 / 8000000)) (hi := (187553313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42951) = 1/(42951 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-187553313 / 500000000) (-3000853 / 8000000) (Real.log (42951 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136348807 / 500000000) ≤ -Real.log (1000000 / 1313503) ∧
    -Real.log (1000000 / 1313503) ≤ (54539523 / 200000000) := by
  have h := checkLog_sound (w := (313503 / 2313503)) (n := 12)
    (lo := (136348807 / 500000000)) (hi := (54539523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313503 / 1000000) = 1/(1000000 / 1313503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136348807 / 500000000) (54539523 / 200000000) (Real.log (1313503 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1313503 / 1000000) = -Real.log (1000000 / 1313503) := by
    rw [show ((1313503 / 1000000) : ℝ) = ((1000000 / 1313503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (376153423 / 1000000000) ≤ -Real.log (686497 / 1000000) ∧
    -Real.log (686497 / 1000000) ≤ (23509589 / 62500000) := by
  have h := checkLog_sound (w := (313503 / 1686497)) (n := 12)
    (lo := (376153423 / 1000000000)) (hi := (23509589 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 686497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 686497) = 1/(686497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-23509589 / 62500000) (-376153423 / 1000000000) (Real.log (686497 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (897103949 / 1000000000) ≤ -Real.log (500000000000 / 1226245140619) ∧
    -Real.log (500000000000 / 1226245140619) ≤ (897103951 / 1000000000) := by
  have h := checkLog_sound (w := (226245140619 / 2226245140619)) (n := 12)
    (lo := (203956769 / 1000000000)) (hi := (20395677 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226245140619 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1226245140619 / 1000000000000) = 1/(500000000000 / 1226245140619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (897103949 / 1000000000) (897103951 / 1000000000) (Real.log (1226245140619 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1226245140619 / 500000000000) = -Real.log (500000000000 / 1226245140619) := by
    rw [show ((1226245140619 / 500000000000) : ℝ) = ((500000000000 / 1226245140619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (22480903 / 25000000) ≤ -Real.log (250000000000 / 614431247461) ∧
    -Real.log (250000000000 / 614431247461) ≤ (449618061 / 500000000) := by
  have h := checkLog_sound (w := (114431247461 / 1114431247461)) (n := 12)
    (lo := (10304447 / 50000000)) (hi := (206088941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614431247461 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(614431247461 / 500000000000) = 1/(250000000000 / 614431247461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (22480903 / 25000000) (449618061 / 500000000) (Real.log (614431247461 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (614431247461 / 250000000000) = -Real.log (250000000000 / 614431247461) := by
    rw [show ((614431247461 / 250000000000) : ℝ) = ((250000000000 / 614431247461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (323628349 / 500000000) ≤ -Real.log (500000000000 / 955146562361) ∧
    -Real.log (500000000000 / 955146562361) ≤ (647256699 / 1000000000) := by
  have h := checkLog_sound (w := (455146562361 / 1455146562361)) (n := 12)
    (lo := (323628349 / 500000000)) (hi := (647256699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955146562361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955146562361 / 500000000000) = 1/(500000000000 / 955146562361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (323628349 / 500000000) (647256699 / 1000000000) (Real.log (955146562361 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (955146562361 / 500000000000) = -Real.log (500000000000 / 955146562361) := by
    rw [show ((955146562361 / 500000000000) : ℝ) = ((500000000000 / 955146562361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (648851037 / 1000000000) ≤ -Real.log (500000000000 / 956670604533) ∧
    -Real.log (500000000000 / 956670604533) ≤ (324425519 / 500000000) := by
  have h := checkLog_sound (w := (456670604533 / 1456670604533)) (n := 12)
    (lo := (648851037 / 1000000000)) (hi := (324425519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956670604533 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956670604533 / 500000000000) = 1/(500000000000 / 956670604533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (648851037 / 1000000000) (324425519 / 500000000) (Real.log (956670604533 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (956670604533 / 500000000000) = -Real.log (500000000000 / 956670604533) := by
    rw [show ((956670604533 / 500000000000) : ℝ) = ((500000000000 / 956670604533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0219

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0220Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0220
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

theorem reflection_log_1_neg : (25663877 / 100000000) ≤ -Real.log (2560 / 3309) ∧
    -Real.log (2560 / 3309) ≤ (256638771 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 5869)) (n := 12)
    (lo := (25663877 / 100000000)) (hi := (256638771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3309 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3309 / 2560) = 1/(2560 / 3309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (25663877 / 100000000) (256638771 / 1000000000) (Real.log (3309 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3309 / 2560) = -Real.log (2560 / 3309) := by
    rw [show ((3309 / 2560) : ℝ) = ((2560 / 3309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (346128079 / 1000000000) ≤ -Real.log (1811 / 2560) ∧
    -Real.log (1811 / 2560) ≤ (4326601 / 12500000) := by
  have h := checkLog_sound (w := (749 / 4371)) (n := 12)
    (lo := (346128079 / 1000000000)) (hi := (4326601 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1811) = 1/(1811 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4326601 / 12500000) (-346128079 / 1000000000) (Real.log (1811 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128092679 / 500000000) ≤ -Real.log (1024 / 1323) ∧
    -Real.log (1024 / 1323) ≤ (256185359 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2347)) (n := 12)
    (lo := (128092679 / 500000000)) (hi := (256185359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323 / 1024) = 1/(1024 / 1323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128092679 / 500000000) (256185359 / 1000000000) (Real.log (1323 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1323 / 1024) = -Real.log (1024 / 1323) := by
    rw [show ((1323 / 1024) : ℝ) = ((1024 / 1323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6906003 / 20000000) ≤ -Real.log (725 / 1024) ∧
    -Real.log (725 / 1024) ≤ (345300151 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1749)) (n := 12)
    (lo := (6906003 / 20000000)) (hi := (345300151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 725) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 725) = 1/(725 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-345300151 / 1000000000) (-6906003 / 20000000) (Real.log (725 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (230341491 / 500000000) ≤ -Real.log (1280 / 2029) ∧
    -Real.log (1280 / 2029) ≤ (460682983 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 3309)) (n := 12)
    (lo := (230341491 / 500000000)) (hi := (460682983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2029 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2029 / 1280) = 1/(1280 / 2029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (230341491 / 500000000) (460682983 / 1000000000) (Real.log (2029 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2029 / 1280) = -Real.log (1280 / 2029) := by
    rw [show ((2029 / 1280) : ℝ) = ((1280 / 2029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (175970667 / 200000000) ≤ -Real.log (531 / 1280) ∧
    -Real.log (531 / 1280) ≤ (879853337 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1171)) (n := 12)
    (lo := (37341231 / 200000000)) (hi := (46676539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 531) = 1/(531 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-879853337 / 1000000000) (-175970667 / 200000000) (Real.log (531 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (459943429 / 1000000000) ≤ -Real.log (512 / 811) ∧
    -Real.log (512 / 811) ≤ (45994343 / 100000000) := by
  have h := checkLog_sound (w := (299 / 1323)) (n := 12)
    (lo := (459943429 / 1000000000)) (hi := (45994343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811 / 512) = 1/(512 / 811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (459943429 / 1000000000) (45994343 / 100000000) (Real.log (811 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (811 / 512) = -Real.log (512 / 811) := by
    rw [show ((811 / 512) : ℝ) = ((512 / 811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (438516229 / 500000000) ≤ -Real.log (213 / 512) ∧
    -Real.log (213 / 512) ≤ (43851623 / 50000000) := by
  have h := checkLog_sound (w := (43 / 469)) (n := 12)
    (lo := (91942639 / 500000000)) (hi := (183885279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 213) = 1/(213 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-43851623 / 50000000) (-438516229 / 500000000) (Real.log (213 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (350539259 / 1000000000) ≤ -Real.log (1000000 / 1419833) ∧
    -Real.log (1000000 / 1419833) ≤ (17526963 / 50000000) := by
  have h := checkLog_sound (w := (419833 / 2419833)) (n := 12)
    (lo := (350539259 / 1000000000)) (hi := (17526963 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1419833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1419833 / 1000000) = 1/(1000000 / 1419833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (350539259 / 1000000000) (17526963 / 50000000) (Real.log (1419833 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1419833 / 1000000) = -Real.log (1000000 / 1419833) := by
    rw [show ((1419833 / 1000000) : ℝ) = ((1000000 / 1419833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (108887857 / 200000000) ≤ -Real.log (580167 / 1000000) ∧
    -Real.log (580167 / 1000000) ≤ (272219643 / 500000000) := by
  have h := checkLog_sound (w := (419833 / 1580167)) (n := 12)
    (lo := (108887857 / 200000000)) (hi := (272219643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 580167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 580167) = 1/(580167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-272219643 / 500000000) (-108887857 / 200000000) (Real.log (580167 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (175578021 / 500000000) ≤ -Real.log (1000000 / 1420709) ∧
    -Real.log (1000000 / 1420709) ≤ (351156043 / 1000000000) := by
  have h := checkLog_sound (w := (420709 / 2420709)) (n := 12)
    (lo := (175578021 / 500000000)) (hi := (351156043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1420709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1420709 / 1000000) = 1/(1000000 / 1420709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (175578021 / 500000000) (351156043 / 1000000000) (Real.log (1420709 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1420709 / 1000000) = -Real.log (1000000 / 1420709) := by
    rw [show ((1420709 / 1000000) : ℝ) = ((1000000 / 1420709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4265237 / 7812500) ≤ -Real.log (579291 / 1000000) ∧
    -Real.log (579291 / 1000000) ≤ (545950337 / 1000000000) := by
  have h := checkLog_sound (w := (420709 / 1579291)) (n := 12)
    (lo := (4265237 / 7812500)) (hi := (545950337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 579291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 579291) = 1/(579291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-545950337 / 1000000000) (-4265237 / 7812500) (Real.log (579291 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67900939 / 250000000) ≤ -Real.log (1000000 / 1312067) ∧
    -Real.log (1000000 / 1312067) ≤ (271603757 / 1000000000) := by
  have h := checkLog_sound (w := (312067 / 2312067)) (n := 12)
    (lo := (67900939 / 250000000)) (hi := (271603757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1312067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1312067 / 1000000) = 1/(1000000 / 1312067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67900939 / 250000000) (271603757 / 1000000000) (Real.log (1312067 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1312067 / 1000000) = -Real.log (1000000 / 1312067) := by
    rw [show ((1312067 / 1000000) : ℝ) = ((1000000 / 1312067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (374063829 / 1000000000) ≤ -Real.log (687933 / 1000000) ∧
    -Real.log (687933 / 1000000) ≤ (37406383 / 100000000) := by
  have h := checkLog_sound (w := (312067 / 1687933)) (n := 12)
    (lo := (374063829 / 1000000000)) (hi := (37406383 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 687933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 687933) = 1/(687933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-37406383 / 100000000) (-374063829 / 1000000000) (Real.log (687933 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136075417 / 500000000) ≤ -Real.log (200000 / 262557) ∧
    -Real.log (200000 / 262557) ≤ (54430167 / 200000000) := by
  have h := checkLog_sound (w := (62557 / 462557)) (n := 12)
    (lo := (136075417 / 500000000)) (hi := (54430167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262557 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(262557 / 200000) = 1/(200000 / 262557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136075417 / 500000000) (54430167 / 200000000) (Real.log (262557 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (262557 / 200000) = -Real.log (200000 / 262557) := by
    rw [show ((262557 / 200000) : ℝ) = ((200000 / 262557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4688851 / 12500000) ≤ -Real.log (137443 / 200000) ∧
    -Real.log (137443 / 200000) ≤ (375108081 / 1000000000) := by
  have h := checkLog_sound (w := (62557 / 337443)) (n := 12)
    (lo := (4688851 / 12500000)) (hi := (375108081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 137443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 137443) = 1/(137443 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-375108081 / 1000000000) (-4688851 / 12500000) (Real.log (137443 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (55936159 / 62500000) ≤ -Real.log (500000000000 / 1223641641113) ∧
    -Real.log (500000000000 / 1223641641113) ≤ (447489273 / 500000000) := by
  have h := checkLog_sound (w := (223641641113 / 2223641641113)) (n := 12)
    (lo := (50457841 / 250000000)) (hi := (40366273 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223641641113 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1223641641113 / 1000000000000) = 1/(500000000000 / 1223641641113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (55936159 / 62500000) (447489273 / 500000000) (Real.log (1223641641113 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1223641641113 / 500000000000) = -Real.log (500000000000 / 1223641641113) := by
    rw [show ((1223641641113 / 500000000000) : ℝ) = ((500000000000 / 1223641641113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (897106379 / 1000000000) ≤ -Real.log (125000000000 / 306562030137) ∧
    -Real.log (125000000000 / 306562030137) ≤ (897106381 / 1000000000) := by
  have h := checkLog_sound (w := (56562030137 / 556562030137)) (n := 12)
    (lo := (203959199 / 1000000000)) (hi := (254949 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306562030137 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(306562030137 / 250000000000) = 1/(125000000000 / 306562030137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (897106379 / 1000000000) (897106381 / 1000000000) (Real.log (306562030137 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (306562030137 / 125000000000) = -Real.log (125000000000 / 306562030137) := by
    rw [show ((306562030137 / 125000000000) : ℝ) = ((125000000000 / 306562030137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (129133517 / 200000000) ≤ -Real.log (31250000000 / 59601870749) ∧
    -Real.log (31250000000 / 59601870749) ≤ (322833793 / 500000000) := by
  have h := checkLog_sound (w := (28351870749 / 90851870749)) (n := 12)
    (lo := (129133517 / 200000000)) (hi := (322833793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59601870749 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59601870749 / 31250000000) = 1/(31250000000 / 59601870749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (129133517 / 200000000) (322833793 / 500000000) (Real.log (59601870749 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (59601870749 / 31250000000) = -Real.log (31250000000 / 59601870749) := by
    rw [show ((59601870749 / 31250000000) : ℝ) = ((31250000000 / 59601870749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (129451783 / 200000000) ≤ -Real.log (500000000000 / 955148679817) ∧
    -Real.log (500000000000 / 955148679817) ≤ (161814729 / 250000000) := by
  have h := checkLog_sound (w := (455148679817 / 1455148679817)) (n := 12)
    (lo := (129451783 / 200000000)) (hi := (161814729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955148679817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955148679817 / 500000000000) = 1/(500000000000 / 955148679817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (129451783 / 200000000) (161814729 / 250000000) (Real.log (955148679817 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (955148679817 / 500000000000) = -Real.log (500000000000 / 955148679817) := by
    rw [show ((955148679817 / 500000000000) : ℝ) = ((500000000000 / 955148679817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0220

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0221Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0221
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

theorem reflection_log_1_neg : (128092679 / 500000000) ≤ -Real.log (1024 / 1323) ∧
    -Real.log (1024 / 1323) ≤ (256185359 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2347)) (n := 12)
    (lo := (128092679 / 500000000)) (hi := (256185359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323 / 1024) = 1/(1024 / 1323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128092679 / 500000000) (256185359 / 1000000000) (Real.log (1323 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1323 / 1024) = -Real.log (1024 / 1323) := by
    rw [show ((1323 / 1024) : ℝ) = ((1024 / 1323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6906003 / 20000000) ≤ -Real.log (725 / 1024) ∧
    -Real.log (725 / 1024) ≤ (345300151 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1749)) (n := 12)
    (lo := (6906003 / 20000000)) (hi := (345300151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 725) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 725) = 1/(725 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-345300151 / 1000000000) (-6906003 / 20000000) (Real.log (725 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12786587 / 50000000) ≤ -Real.log (1280 / 1653) ∧
    -Real.log (1280 / 1653) ≤ (255731741 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2933)) (n := 12)
    (lo := (12786587 / 50000000)) (hi := (255731741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653 / 1280) = 1/(1280 / 1653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12786587 / 50000000) (255731741 / 1000000000) (Real.log (1653 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1653 / 1280) = -Real.log (1280 / 1653) := by
    rw [show ((1653 / 1280) : ℝ) = ((1280 / 1653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (172236453 / 500000000) ≤ -Real.log (907 / 1280) ∧
    -Real.log (907 / 1280) ≤ (344472907 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2187)) (n := 12)
    (lo := (172236453 / 500000000)) (hi := (344472907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 907) = 1/(907 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-344472907 / 1000000000) (-172236453 / 500000000) (Real.log (907 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (459943429 / 1000000000) ≤ -Real.log (512 / 811) ∧
    -Real.log (512 / 811) ≤ (45994343 / 100000000) := by
  have h := checkLog_sound (w := (299 / 1323)) (n := 12)
    (lo := (459943429 / 1000000000)) (hi := (45994343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811 / 512) = 1/(512 / 811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (459943429 / 1000000000) (45994343 / 100000000) (Real.log (811 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (811 / 512) = -Real.log (512 / 811) := by
    rw [show ((811 / 512) : ℝ) = ((512 / 811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (438516229 / 500000000) ≤ -Real.log (213 / 512) ∧
    -Real.log (213 / 512) ≤ (43851623 / 50000000) := by
  have h := checkLog_sound (w := (43 / 469)) (n := 12)
    (lo := (91942639 / 500000000)) (hi := (183885279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 213) = 1/(213 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-43851623 / 50000000) (-438516229 / 500000000) (Real.log (213 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (459203327 / 1000000000) ≤ -Real.log (640 / 1013) ∧
    -Real.log (640 / 1013) ≤ (1793763 / 3906250) := by
  have h := checkLog_sound (w := (373 / 1653)) (n := 12)
    (lo := (459203327 / 1000000000)) (hi := (1793763 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1013 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1013 / 640) = 1/(640 / 1013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (459203327 / 1000000000) (1793763 / 3906250) (Real.log (1013 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1013 / 640) = -Real.log (640 / 1013) := by
    rw [show ((1013 / 640) : ℝ) = ((640 / 1013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (874219517 / 1000000000) ≤ -Real.log (267 / 640) ∧
    -Real.log (267 / 640) ≤ (874219519 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 587)) (n := 12)
    (lo := (181072337 / 1000000000)) (hi := (90536169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 267) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 267) = 1/(267 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-874219519 / 1000000000) (-874219517 / 1000000000) (Real.log (267 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (349922799 / 1000000000) ≤ -Real.log (500000 / 709479) ∧
    -Real.log (500000 / 709479) ≤ (874807 / 2500000) := by
  have h := checkLog_sound (w := (209479 / 1209479)) (n := 12)
    (lo := (349922799 / 1000000000)) (hi := (874807 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709479 / 500000) = 1/(500000 / 709479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (349922799 / 1000000000) (874807 / 2500000) (Real.log (709479 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (709479 / 500000) = -Real.log (500000 / 709479) := by
    rw [show ((709479 / 500000) : ℝ) = ((500000 / 709479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (108586447 / 200000000) ≤ -Real.log (290521 / 500000) ∧
    -Real.log (290521 / 500000) ≤ (135733059 / 250000000) := by
  have h := checkLog_sound (w := (209479 / 790521)) (n := 12)
    (lo := (108586447 / 200000000)) (hi := (135733059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 290521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 290521) = 1/(290521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-135733059 / 250000000) (-108586447 / 200000000) (Real.log (290521 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (350539963 / 1000000000) ≤ -Real.log (500000 / 709917) ∧
    -Real.log (500000 / 709917) ≤ (87634991 / 250000000) := by
  have h := checkLog_sound (w := (209917 / 1209917)) (n := 12)
    (lo := (350539963 / 1000000000)) (hi := (87634991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709917 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709917 / 500000) = 1/(500000 / 709917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (350539963 / 1000000000) (87634991 / 250000000) (Real.log (709917 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (709917 / 500000) = -Real.log (500000 / 709917) := by
    rw [show ((709917 / 500000) : ℝ) = ((500000 / 709917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (544441009 / 1000000000) ≤ -Real.log (290083 / 500000) ∧
    -Real.log (290083 / 500000) ≤ (54444101 / 100000000) := by
  have h := checkLog_sound (w := (209917 / 790083)) (n := 12)
    (lo := (544441009 / 1000000000)) (hi := (54444101 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 290083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 290083) = 1/(290083 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-54444101 / 100000000) (-544441009 / 1000000000) (Real.log (290083 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13552857 / 50000000) ≤ -Real.log (20000 / 26227) ∧
    -Real.log (20000 / 26227) ≤ (271057141 / 1000000000) := by
  have h := checkLog_sound (w := (6227 / 46227)) (n := 12)
    (lo := (13552857 / 50000000)) (hi := (271057141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26227 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26227 / 20000) = 1/(20000 / 26227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13552857 / 50000000) (271057141 / 1000000000) (Real.log (26227 / 20000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (26227 / 20000) = -Real.log (20000 / 26227) := by
    rw [show ((26227 / 20000) : ℝ) = ((20000 / 26227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (373022119 / 1000000000) ≤ -Real.log (13773 / 20000) ∧
    -Real.log (13773 / 20000) ≤ (9325553 / 25000000) := by
  have h := checkLog_sound (w := (6227 / 33773)) (n := 12)
    (lo := (373022119 / 1000000000)) (hi := (9325553 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 13773) = 1/(13773 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-9325553 / 25000000) (-373022119 / 1000000000) (Real.log (13773 / 20000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (135802259 / 500000000) ≤ -Real.log (250000 / 328017) ∧
    -Real.log (250000 / 328017) ≤ (271604519 / 1000000000) := by
  have h := checkLog_sound (w := (78017 / 578017)) (n := 12)
    (lo := (135802259 / 500000000)) (hi := (271604519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328017 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328017 / 250000) = 1/(250000 / 328017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (135802259 / 500000000) (271604519 / 1000000000) (Real.log (328017 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (328017 / 250000) = -Real.log (250000 / 328017) := by
    rw [show ((328017 / 250000) : ℝ) = ((250000 / 328017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (374065283 / 1000000000) ≤ -Real.log (171983 / 250000) ∧
    -Real.log (171983 / 250000) ≤ (93516321 / 250000000) := by
  have h := checkLog_sound (w := (78017 / 421983)) (n := 12)
    (lo := (374065283 / 1000000000)) (hi := (93516321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171983) = 1/(171983 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-93516321 / 250000000) (-374065283 / 1000000000) (Real.log (171983 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (446427517 / 500000000) ≤ -Real.log (250000000000 / 610522991453) ∧
    -Real.log (250000000000 / 610522991453) ≤ (223213759 / 250000000) := by
  have h := checkLog_sound (w := (110522991453 / 1110522991453)) (n := 12)
    (lo := (99853927 / 500000000)) (hi := (39941571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610522991453 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(610522991453 / 500000000000) = 1/(250000000000 / 610522991453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (446427517 / 500000000) (223213759 / 250000000) (Real.log (610522991453 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (610522991453 / 250000000000) = -Real.log (250000000000 / 610522991453) := by
    rw [show ((610522991453 / 250000000000) : ℝ) = ((250000000000 / 610522991453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (223745243 / 250000000) ≤ -Real.log (25000000000 / 61182230603) ∧
    -Real.log (25000000000 / 61182230603) ≤ (447490487 / 500000000) := by
  have h := checkLog_sound (w := (11182230603 / 111182230603)) (n := 12)
    (lo := (3153653 / 15625000)) (hi := (201833793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61182230603 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(61182230603 / 50000000000) = 1/(25000000000 / 61182230603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (223745243 / 250000000) (447490487 / 500000000) (Real.log (61182230603 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (61182230603 / 25000000000) = -Real.log (25000000000 / 61182230603) := by
    rw [show ((61182230603 / 25000000000) : ℝ) = ((25000000000 / 61182230603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (32203963 / 50000000) ≤ -Real.log (25000000000 / 47605822987) ∧
    -Real.log (25000000000 / 47605822987) ≤ (644079261 / 1000000000) := by
  have h := checkLog_sound (w := (22605822987 / 72605822987)) (n := 12)
    (lo := (32203963 / 50000000)) (hi := (644079261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47605822987 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47605822987 / 25000000000) = 1/(25000000000 / 47605822987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (32203963 / 50000000) (644079261 / 1000000000) (Real.log (47605822987 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (47605822987 / 25000000000) = -Real.log (25000000000 / 47605822987) := by
    rw [show ((47605822987 / 25000000000) : ℝ) = ((25000000000 / 47605822987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (645669801 / 1000000000) ≤ -Real.log (125000000000 / 238408011257) ∧
    -Real.log (125000000000 / 238408011257) ≤ (322834901 / 500000000) := by
  have h := checkLog_sound (w := (113408011257 / 363408011257)) (n := 12)
    (lo := (645669801 / 1000000000)) (hi := (322834901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238408011257 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238408011257 / 125000000000) = 1/(125000000000 / 238408011257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (645669801 / 1000000000) (322834901 / 500000000) (Real.log (238408011257 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (238408011257 / 125000000000) = -Real.log (125000000000 / 238408011257) := by
    rw [show ((238408011257 / 125000000000) : ℝ) = ((125000000000 / 238408011257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0221

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0222Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0222
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

theorem reflection_log_1_neg : (12786587 / 50000000) ≤ -Real.log (1280 / 1653) ∧
    -Real.log (1280 / 1653) ≤ (255731741 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2933)) (n := 12)
    (lo := (12786587 / 50000000)) (hi := (255731741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653 / 1280) = 1/(1280 / 1653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12786587 / 50000000) (255731741 / 1000000000) (Real.log (1653 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1653 / 1280) = -Real.log (1280 / 1653) := by
    rw [show ((1653 / 1280) : ℝ) = ((1280 / 1653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (172236453 / 500000000) ≤ -Real.log (907 / 1280) ∧
    -Real.log (907 / 1280) ≤ (344472907 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2187)) (n := 12)
    (lo := (172236453 / 500000000)) (hi := (344472907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 907) = 1/(907 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-344472907 / 1000000000) (-172236453 / 500000000) (Real.log (907 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (255277917 / 1000000000) ≤ -Real.log (5120 / 6609) ∧
    -Real.log (5120 / 6609) ≤ (127638959 / 500000000) := by
  have h := checkLog_sound (w := (1489 / 11729)) (n := 12)
    (lo := (255277917 / 1000000000)) (hi := (127638959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6609 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6609 / 5120) = 1/(5120 / 6609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (255277917 / 1000000000) (127638959 / 500000000) (Real.log (6609 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6609 / 5120) = -Real.log (5120 / 6609) := by
    rw [show ((6609 / 5120) : ℝ) = ((5120 / 6609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (171823173 / 500000000) ≤ -Real.log (3631 / 5120) ∧
    -Real.log (3631 / 5120) ≤ (343646347 / 1000000000) := by
  have h := checkLog_sound (w := (1489 / 8751)) (n := 12)
    (lo := (171823173 / 500000000)) (hi := (343646347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3631) = 1/(3631 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-343646347 / 1000000000) (-171823173 / 500000000) (Real.log (3631 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (459203327 / 1000000000) ≤ -Real.log (640 / 1013) ∧
    -Real.log (640 / 1013) ≤ (1793763 / 3906250) := by
  have h := checkLog_sound (w := (373 / 1653)) (n := 12)
    (lo := (459203327 / 1000000000)) (hi := (1793763 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1013 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1013 / 640) = 1/(640 / 1013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (459203327 / 1000000000) (1793763 / 3906250) (Real.log (1013 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1013 / 640) = -Real.log (640 / 1013) := by
    rw [show ((1013 / 640) : ℝ) = ((640 / 1013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (874219517 / 1000000000) ≤ -Real.log (267 / 640) ∧
    -Real.log (267 / 640) ≤ (874219519 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 587)) (n := 12)
    (lo := (181072337 / 1000000000)) (hi := (90536169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 267) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 267) = 1/(267 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-874219519 / 1000000000) (-874219517 / 1000000000) (Real.log (267 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (229231339 / 500000000) ≤ -Real.log (2560 / 4049) ∧
    -Real.log (2560 / 4049) ≤ (458462679 / 1000000000) := by
  have h := checkLog_sound (w := (1489 / 6609)) (n := 12)
    (lo := (229231339 / 500000000)) (hi := (458462679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4049 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4049 / 2560) = 1/(2560 / 4049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (229231339 / 500000000) (458462679 / 1000000000) (Real.log (4049 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4049 / 2560) = -Real.log (2560 / 4049) := by
    rw [show ((4049 / 2560) : ℝ) = ((2560 / 4049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (435707233 / 500000000) ≤ -Real.log (1071 / 2560) ∧
    -Real.log (1071 / 2560) ≤ (217853617 / 250000000) := by
  have h := checkLog_sound (w := (209 / 2351)) (n := 12)
    (lo := (89133643 / 500000000)) (hi := (178267287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1071) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1071) = 1/(1071 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-217853617 / 250000000) (-435707233 / 500000000) (Real.log (1071 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (349305959 / 1000000000) ≤ -Real.log (1000000 / 1418083) ∧
    -Real.log (1000000 / 1418083) ≤ (8732649 / 25000000) := by
  have h := checkLog_sound (w := (418083 / 2418083)) (n := 12)
    (lo := (349305959 / 1000000000)) (hi := (8732649 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1418083 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1418083 / 1000000) = 1/(1000000 / 1418083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (349305959 / 1000000000) (8732649 / 25000000) (Real.log (1418083 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1418083 / 1000000) = -Real.log (1000000 / 1418083) := by
    rw [show ((1418083 / 1000000) : ℝ) = ((1000000 / 1418083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (541427453 / 1000000000) ≤ -Real.log (581917 / 1000000) ∧
    -Real.log (581917 / 1000000) ≤ (270713727 / 500000000) := by
  have h := checkLog_sound (w := (418083 / 1581917)) (n := 12)
    (lo := (541427453 / 1000000000)) (hi := (270713727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 581917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 581917) = 1/(581917 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-270713727 / 500000000) (-541427453 / 1000000000) (Real.log (581917 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21870219 / 62500000) ≤ -Real.log (1000000 / 1418959) ∧
    -Real.log (1000000 / 1418959) ≤ (69984701 / 200000000) := by
  have h := checkLog_sound (w := (418959 / 2418959)) (n := 12)
    (lo := (21870219 / 62500000)) (hi := (69984701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1418959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1418959 / 1000000) = 1/(1000000 / 1418959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21870219 / 62500000) (69984701 / 200000000) (Real.log (1418959 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1418959 / 1000000) = -Real.log (1000000 / 1418959) := by
    rw [show ((1418959 / 1000000) : ℝ) = ((1000000 / 1418959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (135733489 / 250000000) ≤ -Real.log (581041 / 1000000) ∧
    -Real.log (581041 / 1000000) ≤ (542933957 / 1000000000) := by
  have h := checkLog_sound (w := (418959 / 1581041)) (n := 12)
    (lo := (135733489 / 250000000)) (hi := (542933957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 581041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 581041) = 1/(581041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-542933957 / 1000000000) (-135733489 / 250000000) (Real.log (581041 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (270510989 / 1000000000) ≤ -Real.log (500000 / 655317) ∧
    -Real.log (500000 / 655317) ≤ (27051099 / 100000000) := by
  have h := checkLog_sound (w := (155317 / 1155317)) (n := 12)
    (lo := (270510989 / 1000000000)) (hi := (27051099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655317 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655317 / 500000) = 1/(500000 / 655317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (270510989 / 1000000000) (27051099 / 100000000) (Real.log (655317 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (655317 / 500000) = -Real.log (500000 / 655317) := by
    rw [show ((655317 / 500000) : ℝ) = ((500000 / 655317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (11624467 / 31250000) ≤ -Real.log (344683 / 500000) ∧
    -Real.log (344683 / 500000) ≤ (74396589 / 200000000) := by
  have h := checkLog_sound (w := (155317 / 844683)) (n := 12)
    (lo := (11624467 / 31250000)) (hi := (74396589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 344683) = 1/(344683 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-74396589 / 200000000) (-11624467 / 31250000) (Real.log (344683 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (271057903 / 1000000000) ≤ -Real.log (1000000 / 1311351) ∧
    -Real.log (1000000 / 1311351) ≤ (16941119 / 62500000) := by
  have h := checkLog_sound (w := (311351 / 2311351)) (n := 12)
    (lo := (271057903 / 1000000000)) (hi := (16941119 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311351 / 1000000) = 1/(1000000 / 1311351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (271057903 / 1000000000) (16941119 / 62500000) (Real.log (1311351 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1311351 / 1000000) = -Real.log (1000000 / 1311351) := by
    rw [show ((1311351 / 1000000) : ℝ) = ((1000000 / 1311351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (373023571 / 1000000000) ≤ -Real.log (688649 / 1000000) ∧
    -Real.log (688649 / 1000000) ≤ (93255893 / 250000000) := by
  have h := checkLog_sound (w := (311351 / 1688649)) (n := 12)
    (lo := (373023571 / 1000000000)) (hi := (93255893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 688649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 688649) = 1/(688649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-93255893 / 250000000) (-373023571 / 1000000000) (Real.log (688649 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (222683353 / 250000000) ≤ -Real.log (250000000000 / 609229065313) ∧
    -Real.log (250000000000 / 609229065313) ≤ (445366707 / 500000000) := by
  have h := checkLog_sound (w := (109229065313 / 1109229065313)) (n := 12)
    (lo := (24698279 / 125000000)) (hi := (197586233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609229065313 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(609229065313 / 500000000000) = 1/(250000000000 / 609229065313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (222683353 / 250000000) (445366707 / 500000000) (Real.log (609229065313 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (609229065313 / 250000000000) = -Real.log (250000000000 / 609229065313) := by
    rw [show ((609229065313 / 250000000000) : ℝ) = ((250000000000 / 609229065313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (44642873 / 50000000) ≤ -Real.log (500000000000 / 1221048944911) ∧
    -Real.log (500000000000 / 1221048944911) ≤ (446428731 / 500000000) := by
  have h := checkLog_sound (w := (221048944911 / 2221048944911)) (n := 12)
    (lo := (4992757 / 25000000)) (hi := (199710281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221048944911 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1221048944911 / 1000000000000) = 1/(500000000000 / 1221048944911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (44642873 / 50000000) (446428731 / 500000000) (Real.log (1221048944911 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1221048944911 / 500000000000) = -Real.log (500000000000 / 1221048944911) := by
    rw [show ((1221048944911 / 500000000000) : ℝ) = ((500000000000 / 1221048944911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (642493933 / 1000000000) ≤ -Real.log (100000000000 / 190121648007) ∧
    -Real.log (100000000000 / 190121648007) ≤ (321246967 / 500000000) := by
  have h := checkLog_sound (w := (90121648007 / 290121648007)) (n := 12)
    (lo := (642493933 / 1000000000)) (hi := (321246967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190121648007 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190121648007 / 100000000000) = 1/(100000000000 / 190121648007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (642493933 / 1000000000) (321246967 / 500000000) (Real.log (190121648007 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (190121648007 / 100000000000) = -Real.log (100000000000 / 190121648007) := by
    rw [show ((190121648007 / 100000000000) : ℝ) = ((100000000000 / 190121648007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (25763259 / 40000000) ≤ -Real.log (250000000000 / 476059284193) ∧
    -Real.log (250000000000 / 476059284193) ≤ (161020369 / 250000000) := by
  have h := checkLog_sound (w := (226059284193 / 726059284193)) (n := 12)
    (lo := (25763259 / 40000000)) (hi := (161020369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((476059284193 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(476059284193 / 250000000000) = 1/(250000000000 / 476059284193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (25763259 / 40000000) (161020369 / 250000000) (Real.log (476059284193 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (476059284193 / 250000000000) = -Real.log (250000000000 / 476059284193) := by
    rw [show ((476059284193 / 250000000000) : ℝ) = ((250000000000 / 476059284193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0222

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0223Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0223
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

theorem reflection_log_1_neg : (255277917 / 1000000000) ≤ -Real.log (5120 / 6609) ∧
    -Real.log (5120 / 6609) ≤ (127638959 / 500000000) := by
  have h := checkLog_sound (w := (1489 / 11729)) (n := 12)
    (lo := (255277917 / 1000000000)) (hi := (127638959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6609 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6609 / 5120) = 1/(5120 / 6609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (255277917 / 1000000000) (127638959 / 500000000) (Real.log (6609 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6609 / 5120) = -Real.log (5120 / 6609) := by
    rw [show ((6609 / 5120) : ℝ) = ((5120 / 6609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (171823173 / 500000000) ≤ -Real.log (3631 / 5120) ∧
    -Real.log (3631 / 5120) ≤ (343646347 / 1000000000) := by
  have h := checkLog_sound (w := (1489 / 8751)) (n := 12)
    (lo := (171823173 / 500000000)) (hi := (343646347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3631) = 1/(3631 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-343646347 / 1000000000) (-171823173 / 500000000) (Real.log (3631 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (254823887 / 1000000000) ≤ -Real.log (2560 / 3303) ∧
    -Real.log (2560 / 3303) ≤ (15926493 / 62500000) := by
  have h := checkLog_sound (w := (743 / 5863)) (n := 12)
    (lo := (254823887 / 1000000000)) (hi := (15926493 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3303 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3303 / 2560) = 1/(2560 / 3303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (254823887 / 1000000000) (15926493 / 62500000) (Real.log (3303 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3303 / 2560) = -Real.log (2560 / 3303) := by
    rw [show ((3303 / 2560) : ℝ) = ((2560 / 3303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (342820469 / 1000000000) ≤ -Real.log (1817 / 2560) ∧
    -Real.log (1817 / 2560) ≤ (34282047 / 100000000) := by
  have h := checkLog_sound (w := (743 / 4377)) (n := 12)
    (lo := (342820469 / 1000000000)) (hi := (34282047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1817) = 1/(1817 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-34282047 / 100000000) (-342820469 / 1000000000) (Real.log (1817 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (229231339 / 500000000) ≤ -Real.log (2560 / 4049) ∧
    -Real.log (2560 / 4049) ≤ (458462679 / 1000000000) := by
  have h := checkLog_sound (w := (1489 / 6609)) (n := 12)
    (lo := (229231339 / 500000000)) (hi := (458462679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4049 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4049 / 2560) = 1/(2560 / 4049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (229231339 / 500000000) (458462679 / 1000000000) (Real.log (4049 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4049 / 2560) = -Real.log (2560 / 4049) := by
    rw [show ((4049 / 2560) : ℝ) = ((2560 / 4049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (435707233 / 500000000) ≤ -Real.log (1071 / 2560) ∧
    -Real.log (1071 / 2560) ≤ (217853617 / 250000000) := by
  have h := checkLog_sound (w := (209 / 2351)) (n := 12)
    (lo := (89133643 / 500000000)) (hi := (178267287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1071) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1071) = 1/(1071 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-217853617 / 250000000) (-435707233 / 500000000) (Real.log (1071 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (11443037 / 25000000) ≤ -Real.log (1280 / 2023) ∧
    -Real.log (1280 / 2023) ≤ (457721481 / 1000000000) := by
  have h := checkLog_sound (w := (743 / 3303)) (n := 12)
    (lo := (11443037 / 25000000)) (hi := (457721481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2023 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2023 / 1280) = 1/(1280 / 2023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (11443037 / 25000000) (457721481 / 1000000000) (Real.log (2023 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2023 / 1280) = -Real.log (1280 / 2023) := by
    rw [show ((2023 / 1280) : ℝ) = ((1280 / 2023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (868617261 / 1000000000) ≤ -Real.log (537 / 1280) ∧
    -Real.log (537 / 1280) ≤ (868617263 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1177)) (n := 12)
    (lo := (175470081 / 1000000000)) (hi := (87735041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 537) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 537) = 1/(537 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-868617263 / 1000000000) (-868617261 / 1000000000) (Real.log (537 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (174344369 / 500000000) ≤ -Real.log (125000 / 177151) ∧
    -Real.log (125000 / 177151) ≤ (348688739 / 1000000000) := by
  have h := checkLog_sound (w := (52151 / 302151)) (n := 12)
    (lo := (174344369 / 500000000)) (hi := (348688739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177151 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177151 / 125000) = 1/(125000 / 177151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (174344369 / 500000000) (348688739 / 1000000000) (Real.log (177151 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (177151 / 125000) = -Real.log (125000 / 177151) := by
    rw [show ((177151 / 125000) : ℝ) = ((125000 / 177151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (539924931 / 1000000000) ≤ -Real.log (72849 / 125000) ∧
    -Real.log (72849 / 125000) ≤ (134981233 / 250000000) := by
  have h := checkLog_sound (w := (52151 / 197849)) (n := 12)
    (lo := (539924931 / 1000000000)) (hi := (134981233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 72849) = 1/(72849 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-134981233 / 250000000) (-539924931 / 1000000000) (Real.log (72849 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43663333 / 125000000) ≤ -Real.log (250000 / 354521) ∧
    -Real.log (250000 / 354521) ≤ (69861333 / 200000000) := by
  have h := checkLog_sound (w := (104521 / 604521)) (n := 12)
    (lo := (43663333 / 125000000)) (hi := (69861333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354521 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354521 / 250000) = 1/(250000 / 354521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43663333 / 125000000) (69861333 / 200000000) (Real.log (354521 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (354521 / 250000) = -Real.log (250000 / 354521) := by
    rw [show ((354521 / 250000) : ℝ) = ((250000 / 354521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (541429171 / 1000000000) ≤ -Real.log (145479 / 250000) ∧
    -Real.log (145479 / 250000) ≤ (135357293 / 250000000) := by
  have h := checkLog_sound (w := (104521 / 395479)) (n := 12)
    (lo := (541429171 / 1000000000)) (hi := (135357293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 145479) = 1/(145479 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-135357293 / 250000000) (-541429171 / 1000000000) (Real.log (145479 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (269965303 / 1000000000) ≤ -Real.log (1000000 / 1309919) ∧
    -Real.log (1000000 / 1309919) ≤ (33745663 / 125000000) := by
  have h := checkLog_sound (w := (309919 / 2309919)) (n := 12)
    (lo := (269965303 / 1000000000)) (hi := (33745663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1309919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1309919 / 1000000) = 1/(1000000 / 1309919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (269965303 / 1000000000) (33745663 / 125000000) (Real.log (1309919 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1309919 / 1000000) = -Real.log (1000000 / 1309919) := by
    rw [show ((1309919 / 1000000) : ℝ) = ((1000000 / 1309919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (46368287 / 125000000) ≤ -Real.log (690081 / 1000000) ∧
    -Real.log (690081 / 1000000) ≤ (370946297 / 1000000000) := by
  have h := checkLog_sound (w := (309919 / 1690081)) (n := 12)
    (lo := (46368287 / 125000000)) (hi := (370946297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 690081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 690081) = 1/(690081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-370946297 / 1000000000) (-46368287 / 125000000) (Real.log (690081 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (33813969 / 125000000) ≤ -Real.log (200000 / 262127) ∧
    -Real.log (200000 / 262127) ≤ (270511753 / 1000000000) := by
  have h := checkLog_sound (w := (62127 / 462127)) (n := 12)
    (lo := (33813969 / 125000000)) (hi := (270511753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(262127 / 200000) = 1/(200000 / 262127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (33813969 / 125000000) (270511753 / 1000000000) (Real.log (262127 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (262127 / 200000) = -Real.log (200000 / 262127) := by
    rw [show ((262127 / 200000) : ℝ) = ((200000 / 262127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (185992197 / 500000000) ≤ -Real.log (137873 / 200000) ∧
    -Real.log (137873 / 200000) ≤ (74396879 / 200000000) := by
  have h := checkLog_sound (w := (62127 / 337873)) (n := 12)
    (lo := (185992197 / 500000000)) (hi := (74396879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 137873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 137873) = 1/(137873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-74396879 / 200000000) (-185992197 / 500000000) (Real.log (137873 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (888613669 / 1000000000) ≤ -Real.log (100000000000 / 243175609823) ∧
    -Real.log (100000000000 / 243175609823) ≤ (888613671 / 1000000000) := by
  have h := checkLog_sound (w := (43175609823 / 443175609823)) (n := 12)
    (lo := (195466489 / 1000000000)) (hi := (19546649 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243175609823 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(243175609823 / 200000000000) = 1/(100000000000 / 243175609823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (888613669 / 1000000000) (888613671 / 1000000000) (Real.log (243175609823 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (243175609823 / 100000000000) = -Real.log (100000000000 / 243175609823) := by
    rw [show ((243175609823 / 100000000000) : ℝ) = ((100000000000 / 243175609823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (178147167 / 200000000) ≤ -Real.log (500000000000 / 1218461083731) ∧
    -Real.log (500000000000 / 1218461083731) ≤ (890735837 / 1000000000) := by
  have h := checkLog_sound (w := (218461083731 / 2218461083731)) (n := 12)
    (lo := (39517731 / 200000000)) (hi := (12349291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218461083731 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1218461083731 / 1000000000000) = 1/(500000000000 / 1218461083731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (178147167 / 200000000) (890735837 / 1000000000) (Real.log (1218461083731 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1218461083731 / 500000000000) = -Real.log (500000000000 / 1218461083731) := by
    rw [show ((1218461083731 / 500000000000) : ℝ) = ((500000000000 / 1218461083731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1602279 / 2500000) ≤ -Real.log (500000000000 / 949105249963) ∧
    -Real.log (500000000000 / 949105249963) ≤ (640911601 / 1000000000) := by
  have h := checkLog_sound (w := (449105249963 / 1449105249963)) (n := 12)
    (lo := (1602279 / 2500000)) (hi := (640911601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((949105249963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(949105249963 / 500000000000) = 1/(500000000000 / 949105249963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1602279 / 2500000) (640911601 / 1000000000) (Real.log (949105249963 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (949105249963 / 500000000000) = -Real.log (500000000000 / 949105249963) := by
    rw [show ((949105249963 / 500000000000) : ℝ) = ((500000000000 / 949105249963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (642496147 / 1000000000) ≤ -Real.log (500000000000 / 950610344303) ∧
    -Real.log (500000000000 / 950610344303) ≤ (160624037 / 250000000) := by
  have h := checkLog_sound (w := (450610344303 / 1450610344303)) (n := 12)
    (lo := (642496147 / 1000000000)) (hi := (160624037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((950610344303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(950610344303 / 500000000000) = 1/(500000000000 / 950610344303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (642496147 / 1000000000) (160624037 / 250000000) (Real.log (950610344303 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (950610344303 / 500000000000) = -Real.log (500000000000 / 950610344303) := by
    rw [show ((950610344303 / 500000000000) : ℝ) = ((500000000000 / 950610344303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0223

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0224Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0224
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

theorem reflection_log_1_neg : (254823887 / 1000000000) ≤ -Real.log (2560 / 3303) ∧
    -Real.log (2560 / 3303) ≤ (15926493 / 62500000) := by
  have h := checkLog_sound (w := (743 / 5863)) (n := 12)
    (lo := (254823887 / 1000000000)) (hi := (15926493 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3303 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3303 / 2560) = 1/(2560 / 3303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (254823887 / 1000000000) (15926493 / 62500000) (Real.log (3303 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3303 / 2560) = -Real.log (2560 / 3303) := by
    rw [show ((3303 / 2560) : ℝ) = ((2560 / 3303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (342820469 / 1000000000) ≤ -Real.log (1817 / 2560) ∧
    -Real.log (1817 / 2560) ≤ (34282047 / 100000000) := by
  have h := checkLog_sound (w := (743 / 4377)) (n := 12)
    (lo := (342820469 / 1000000000)) (hi := (34282047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1817) = 1/(1817 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-34282047 / 100000000) (-342820469 / 1000000000) (Real.log (1817 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (63592413 / 250000000) ≤ -Real.log (5120 / 6603) ∧
    -Real.log (5120 / 6603) ≤ (254369653 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 11723)) (n := 12)
    (lo := (63592413 / 250000000)) (hi := (254369653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6603 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6603 / 5120) = 1/(5120 / 6603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (63592413 / 250000000) (254369653 / 1000000000) (Real.log (6603 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6603 / 5120) = -Real.log (5120 / 6603) := by
    rw [show ((6603 / 5120) : ℝ) = ((5120 / 6603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (341995273 / 1000000000) ≤ -Real.log (3637 / 5120) ∧
    -Real.log (3637 / 5120) ≤ (170997637 / 500000000) := by
  have h := checkLog_sound (w := (1483 / 8757)) (n := 12)
    (lo := (341995273 / 1000000000)) (hi := (170997637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3637) = 1/(3637 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170997637 / 500000000) (-341995273 / 1000000000) (Real.log (3637 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (11443037 / 25000000) ≤ -Real.log (1280 / 2023) ∧
    -Real.log (1280 / 2023) ≤ (457721481 / 1000000000) := by
  have h := checkLog_sound (w := (743 / 3303)) (n := 12)
    (lo := (11443037 / 25000000)) (hi := (457721481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2023 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2023 / 1280) = 1/(1280 / 2023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (11443037 / 25000000) (457721481 / 1000000000) (Real.log (2023 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2023 / 1280) = -Real.log (1280 / 2023) := by
    rw [show ((2023 / 1280) : ℝ) = ((1280 / 2023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (868617261 / 1000000000) ≤ -Real.log (537 / 1280) ∧
    -Real.log (537 / 1280) ≤ (868617263 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1177)) (n := 12)
    (lo := (175470081 / 1000000000)) (hi := (87735041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 537) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 537) = 1/(537 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-868617263 / 1000000000) (-868617261 / 1000000000) (Real.log (537 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (114244933 / 250000000) ≤ -Real.log (2560 / 4043) ∧
    -Real.log (2560 / 4043) ≤ (456979733 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 6603)) (n := 12)
    (lo := (114244933 / 250000000)) (hi := (456979733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4043 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4043 / 2560) = 1/(2560 / 4043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (114244933 / 250000000) (456979733 / 1000000000) (Real.log (4043 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4043 / 2560) = -Real.log (2560 / 4043) := by
    rw [show ((4043 / 2560) : ℝ) = ((2560 / 4043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (865827859 / 1000000000) ≤ -Real.log (1077 / 2560) ∧
    -Real.log (1077 / 2560) ≤ (865827861 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 2357)) (n := 12)
    (lo := (172680679 / 1000000000)) (hi := (4317017 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1077) = 1/(1077 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-865827861 / 1000000000) (-865827859 / 1000000000) (Real.log (1077 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (348071843 / 1000000000) ≤ -Real.log (500000 / 708167) ∧
    -Real.log (500000 / 708167) ≤ (87017961 / 250000000) := by
  have h := checkLog_sound (w := (208167 / 1208167)) (n := 12)
    (lo := (348071843 / 1000000000)) (hi := (87017961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708167 / 500000) = 1/(500000 / 708167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (348071843 / 1000000000) (87017961 / 250000000) (Real.log (708167 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (708167 / 500000) = -Real.log (500000 / 708167) := by
    rw [show ((708167 / 500000) : ℝ) = ((500000 / 708167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (538426377 / 1000000000) ≤ -Real.log (291833 / 500000) ∧
    -Real.log (291833 / 500000) ≤ (269213189 / 500000000) := by
  have h := checkLog_sound (w := (208167 / 791833)) (n := 12)
    (lo := (538426377 / 1000000000)) (hi := (269213189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 291833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 291833) = 1/(291833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-269213189 / 500000000) (-538426377 / 1000000000) (Real.log (291833 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (87172361 / 250000000) ≤ -Real.log (1000000 / 1417209) ∧
    -Real.log (1000000 / 1417209) ≤ (69737889 / 200000000) := by
  have h := checkLog_sound (w := (417209 / 2417209)) (n := 12)
    (lo := (87172361 / 250000000)) (hi := (69737889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1417209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1417209 / 1000000) = 1/(1000000 / 1417209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (87172361 / 250000000) (69737889 / 200000000) (Real.log (1417209 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1417209 / 1000000) = -Real.log (1000000 / 1417209) := by
    rw [show ((1417209 / 1000000) : ℝ) = ((1000000 / 1417209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (539926647 / 1000000000) ≤ -Real.log (582791 / 1000000) ∧
    -Real.log (582791 / 1000000) ≤ (67490831 / 125000000) := by
  have h := checkLog_sound (w := (417209 / 1582791)) (n := 12)
    (lo := (539926647 / 1000000000)) (hi := (67490831 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 582791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 582791) = 1/(582791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-67490831 / 125000000) (-539926647 / 1000000000) (Real.log (582791 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (134709659 / 500000000) ≤ -Real.log (250000 / 327301) ∧
    -Real.log (250000 / 327301) ≤ (269419319 / 1000000000) := by
  have h := checkLog_sound (w := (77301 / 577301)) (n := 12)
    (lo := (134709659 / 500000000)) (hi := (269419319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327301 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327301 / 250000) = 1/(250000 / 327301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (134709659 / 500000000) (269419319 / 1000000000) (Real.log (327301 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (327301 / 250000) = -Real.log (250000 / 327301) := by
    rw [show ((327301 / 250000) : ℝ) = ((250000 / 327301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (369910723 / 1000000000) ≤ -Real.log (172699 / 250000) ∧
    -Real.log (172699 / 250000) ≤ (92477681 / 250000000) := by
  have h := checkLog_sound (w := (77301 / 422699)) (n := 12)
    (lo := (369910723 / 1000000000)) (hi := (92477681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 172699) = 1/(172699 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-92477681 / 250000000) (-369910723 / 1000000000) (Real.log (172699 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (134983033 / 500000000) ≤ -Real.log (6250 / 8187) ∧
    -Real.log (6250 / 8187) ≤ (269966067 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 14437)) (n := 12)
    (lo := (134983033 / 500000000)) (hi := (269966067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8187 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8187 / 6250) = 1/(6250 / 8187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134983033 / 500000000) (269966067 / 1000000000) (Real.log (8187 / 6250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (8187 / 6250) = -Real.log (6250 / 8187) := by
    rw [show ((8187 / 6250) : ℝ) = ((6250 / 8187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (185473873 / 500000000) ≤ -Real.log (4313 / 6250) ∧
    -Real.log (4313 / 6250) ≤ (370947747 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 10563)) (n := 12)
    (lo := (185473873 / 500000000)) (hi := (370947747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4313) = 1/(4313 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-370947747 / 1000000000) (-185473873 / 500000000) (Real.log (4313 / 6250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (44324911 / 50000000) ≤ -Real.log (125000000000 / 303327159711) ∧
    -Real.log (125000000000 / 303327159711) ≤ (443249111 / 500000000) := by
  have h := checkLog_sound (w := (53327159711 / 553327159711)) (n := 12)
    (lo := (302111 / 1562500)) (hi := (193351041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303327159711 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(303327159711 / 250000000000) = 1/(125000000000 / 303327159711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (44324911 / 50000000) (443249111 / 500000000) (Real.log (303327159711 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (303327159711 / 125000000000) = -Real.log (125000000000 / 303327159711) := by
    rw [show ((303327159711 / 125000000000) : ℝ) = ((125000000000 / 303327159711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (888616091 / 1000000000) ≤ -Real.log (250000000000 / 607940496679) ∧
    -Real.log (250000000000 / 607940496679) ≤ (888616093 / 1000000000) := by
  have h := checkLog_sound (w := (107940496679 / 1107940496679)) (n := 12)
    (lo := (195468911 / 1000000000)) (hi := (12216807 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607940496679 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(607940496679 / 500000000000) = 1/(250000000000 / 607940496679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (888616091 / 1000000000) (888616093 / 1000000000) (Real.log (607940496679 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (607940496679 / 250000000000) = -Real.log (250000000000 / 607940496679) := by
    rw [show ((607940496679 / 250000000000) : ℝ) = ((250000000000 / 607940496679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (319665021 / 500000000) ≤ -Real.log (250000000000 / 473802685597) ∧
    -Real.log (250000000000 / 473802685597) ≤ (639330043 / 1000000000) := by
  have h := checkLog_sound (w := (223802685597 / 723802685597)) (n := 12)
    (lo := (319665021 / 500000000)) (hi := (639330043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473802685597 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473802685597 / 250000000000) = 1/(250000000000 / 473802685597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (319665021 / 500000000) (639330043 / 1000000000) (Real.log (473802685597 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (473802685597 / 250000000000) = -Real.log (250000000000 / 473802685597) := by
    rw [show ((473802685597 / 250000000000) : ℝ) = ((250000000000 / 473802685597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (160228453 / 250000000) ≤ -Real.log (500000000000 / 949107349873) ∧
    -Real.log (500000000000 / 949107349873) ≤ (640913813 / 1000000000) := by
  have h := checkLog_sound (w := (449107349873 / 1449107349873)) (n := 12)
    (lo := (160228453 / 250000000)) (hi := (640913813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((949107349873 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(949107349873 / 500000000000) = 1/(500000000000 / 949107349873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (160228453 / 250000000) (640913813 / 1000000000) (Real.log (949107349873 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (949107349873 / 500000000000) = -Real.log (500000000000 / 949107349873) := by
    rw [show ((949107349873 / 500000000000) : ℝ) = ((500000000000 / 949107349873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0224

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0225Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0225
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

theorem reflection_log_1_neg : (63592413 / 250000000) ≤ -Real.log (5120 / 6603) ∧
    -Real.log (5120 / 6603) ≤ (254369653 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 11723)) (n := 12)
    (lo := (63592413 / 250000000)) (hi := (254369653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6603 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6603 / 5120) = 1/(5120 / 6603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (63592413 / 250000000) (254369653 / 1000000000) (Real.log (6603 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6603 / 5120) = -Real.log (5120 / 6603) := by
    rw [show ((6603 / 5120) : ℝ) = ((5120 / 6603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (341995273 / 1000000000) ≤ -Real.log (3637 / 5120) ∧
    -Real.log (3637 / 5120) ≤ (170997637 / 500000000) := by
  have h := checkLog_sound (w := (1483 / 8757)) (n := 12)
    (lo := (341995273 / 1000000000)) (hi := (170997637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3637) = 1/(3637 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170997637 / 500000000) (-341995273 / 1000000000) (Real.log (3637 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (253915209 / 1000000000) ≤ -Real.log (128 / 165) ∧
    -Real.log (128 / 165) ≤ (25391521 / 100000000) := by
  have h := checkLog_sound (w := (37 / 293)) (n := 12)
    (lo := (253915209 / 1000000000)) (hi := (25391521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165 / 128) = 1/(128 / 165) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (253915209 / 1000000000) (25391521 / 100000000) (Real.log (165 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (165 / 128) = -Real.log (128 / 165) := by
    rw [show ((165 / 128) : ℝ) = ((128 / 165) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (341170757 / 1000000000) ≤ -Real.log (91 / 128) ∧
    -Real.log (91 / 128) ≤ (170585379 / 500000000) := by
  have h := checkLog_sound (w := (37 / 219)) (n := 12)
    (lo := (341170757 / 1000000000)) (hi := (170585379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 91) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 91) = 1/(91 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170585379 / 500000000) (-341170757 / 1000000000) (Real.log (91 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (114244933 / 250000000) ≤ -Real.log (2560 / 4043) ∧
    -Real.log (2560 / 4043) ≤ (456979733 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 6603)) (n := 12)
    (lo := (114244933 / 250000000)) (hi := (456979733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4043 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4043 / 2560) = 1/(2560 / 4043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (114244933 / 250000000) (456979733 / 1000000000) (Real.log (4043 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4043 / 2560) = -Real.log (2560 / 4043) := by
    rw [show ((4043 / 2560) : ℝ) = ((2560 / 4043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (865827859 / 1000000000) ≤ -Real.log (1077 / 2560) ∧
    -Real.log (1077 / 2560) ≤ (865827861 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 2357)) (n := 12)
    (lo := (172680679 / 1000000000)) (hi := (4317017 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1077) = 1/(1077 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-865827861 / 1000000000) (-865827859 / 1000000000) (Real.log (1077 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (456237433 / 1000000000) ≤ -Real.log (64 / 101) ∧
    -Real.log (64 / 101) ≤ (228118717 / 500000000) := by
  have h := checkLog_sound (w := (37 / 165)) (n := 12)
    (lo := (456237433 / 1000000000)) (hi := (228118717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101 / 64) = 1/(64 / 101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (456237433 / 1000000000) (228118717 / 500000000) (Real.log (101 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (101 / 64) = -Real.log (64 / 101) := by
    rw [show ((101 / 64) : ℝ) = ((64 / 101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (107880777 / 125000000) ≤ -Real.log (27 / 64) ∧
    -Real.log (27 / 64) ≤ (431523109 / 500000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 27) = 1/(27 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-431523109 / 500000000) (-107880777 / 125000000) (Real.log (27 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17372693 / 50000000) ≤ -Real.log (1000000 / 1415459) ∧
    -Real.log (1000000 / 1415459) ≤ (347453861 / 1000000000) := by
  have h := checkLog_sound (w := (415459 / 2415459)) (n := 12)
    (lo := (17372693 / 50000000)) (hi := (347453861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1415459 / 1000000) = 1/(1000000 / 1415459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17372693 / 50000000) (347453861 / 1000000000) (Real.log (1415459 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1415459 / 1000000) = -Real.log (1000000 / 1415459) := by
    rw [show ((1415459 / 1000000) : ℝ) = ((1000000 / 1415459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107385671 / 200000000) ≤ -Real.log (584541 / 1000000) ∧
    -Real.log (584541 / 1000000) ≤ (134232089 / 250000000) := by
  have h := checkLog_sound (w := (415459 / 1584541)) (n := 12)
    (lo := (107385671 / 200000000)) (hi := (134232089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 584541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 584541) = 1/(584541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-134232089 / 250000000) (-107385671 / 200000000) (Real.log (584541 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (348072549 / 1000000000) ≤ -Real.log (200000 / 283267) ∧
    -Real.log (200000 / 283267) ≤ (6961451 / 20000000) := by
  have h := checkLog_sound (w := (83267 / 483267)) (n := 12)
    (lo := (348072549 / 1000000000)) (hi := (6961451 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283267 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(283267 / 200000) = 1/(200000 / 283267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (348072549 / 1000000000) (6961451 / 20000000) (Real.log (283267 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (283267 / 200000) = -Real.log (200000 / 283267) := by
    rw [show ((283267 / 200000) : ℝ) = ((200000 / 283267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53842809 / 100000000) ≤ -Real.log (116733 / 200000) ∧
    -Real.log (116733 / 200000) ≤ (538428091 / 1000000000) := by
  have h := checkLog_sound (w := (83267 / 316733)) (n := 12)
    (lo := (53842809 / 100000000)) (hi := (538428091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 116733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 116733) = 1/(116733 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-538428091 / 1000000000) (-53842809 / 100000000) (Real.log (116733 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1344369 / 5000000) ≤ -Real.log (100000 / 130849) ∧
    -Real.log (100000 / 130849) ≤ (268873801 / 1000000000) := by
  have h := checkLog_sound (w := (30849 / 230849)) (n := 12)
    (lo := (1344369 / 5000000)) (hi := (268873801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130849 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130849 / 100000) = 1/(100000 / 130849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1344369 / 5000000) (268873801 / 1000000000) (Real.log (130849 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (130849 / 100000) = -Real.log (100000 / 130849) := by
    rw [show ((130849 / 100000) : ℝ) = ((100000 / 130849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (184438833 / 500000000) ≤ -Real.log (69151 / 100000) ∧
    -Real.log (69151 / 100000) ≤ (368877667 / 1000000000) := by
  have h := checkLog_sound (w := (30849 / 169151)) (n := 12)
    (lo := (184438833 / 500000000)) (hi := (368877667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 69151) = 1/(69151 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-368877667 / 1000000000) (-184438833 / 500000000) (Real.log (69151 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (134710041 / 500000000) ≤ -Real.log (200000 / 261841) ∧
    -Real.log (200000 / 261841) ≤ (269420083 / 1000000000) := by
  have h := checkLog_sound (w := (61841 / 461841)) (n := 12)
    (lo := (134710041 / 500000000)) (hi := (269420083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261841 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261841 / 200000) = 1/(200000 / 261841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134710041 / 500000000) (269420083 / 1000000000) (Real.log (261841 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (261841 / 200000) = -Real.log (200000 / 261841) := by
    rw [show ((261841 / 200000) : ℝ) = ((200000 / 261841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (36991217 / 100000000) ≤ -Real.log (138159 / 200000) ∧
    -Real.log (138159 / 200000) ≤ (369912171 / 1000000000) := by
  have h := checkLog_sound (w := (61841 / 338159)) (n := 12)
    (lo := (36991217 / 100000000)) (hi := (369912171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138159) = 1/(138159 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-369912171 / 1000000000) (-36991217 / 100000000) (Real.log (138159 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (442191107 / 500000000) ≤ -Real.log (500000000000 / 1210743985451) ∧
    -Real.log (500000000000 / 1210743985451) ≤ (110547777 / 125000000) := by
  have h := checkLog_sound (w := (210743985451 / 2210743985451)) (n := 12)
    (lo := (95617517 / 500000000)) (hi := (38247007 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210743985451 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1210743985451 / 1000000000000) = 1/(500000000000 / 1210743985451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (442191107 / 500000000) (110547777 / 125000000) (Real.log (1210743985451 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1210743985451 / 500000000000) = -Real.log (500000000000 / 1210743985451) := by
    rw [show ((1210743985451 / 500000000000) : ℝ) = ((500000000000 / 1210743985451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (886500639 / 1000000000) ≤ -Real.log (500000000000 / 1213311574277) ∧
    -Real.log (500000000000 / 1213311574277) ≤ (886500641 / 1000000000) := by
  have h := checkLog_sound (w := (213311574277 / 2213311574277)) (n := 12)
    (lo := (193353459 / 1000000000)) (hi := (9667673 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213311574277 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1213311574277 / 1000000000000) = 1/(500000000000 / 1213311574277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (886500639 / 1000000000) (886500641 / 1000000000) (Real.log (1213311574277 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1213311574277 / 500000000000) = -Real.log (500000000000 / 1213311574277) := by
    rw [show ((1213311574277 / 500000000000) : ℝ) = ((500000000000 / 1213311574277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (637751467 / 1000000000) ≤ -Real.log (500000000000 / 946110685311) ∧
    -Real.log (500000000000 / 946110685311) ≤ (159437867 / 250000000) := by
  have h := checkLog_sound (w := (446110685311 / 1446110685311)) (n := 12)
    (lo := (637751467 / 1000000000)) (hi := (159437867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((946110685311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(946110685311 / 500000000000) = 1/(500000000000 / 946110685311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (637751467 / 1000000000) (159437867 / 250000000) (Real.log (946110685311 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (946110685311 / 500000000000) = -Real.log (500000000000 / 946110685311) := by
    rw [show ((946110685311 / 500000000000) : ℝ) = ((500000000000 / 946110685311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (639332253 / 1000000000) ≤ -Real.log (12500000000 / 23690186669) ∧
    -Real.log (12500000000 / 23690186669) ≤ (319666127 / 500000000) := by
  have h := checkLog_sound (w := (11190186669 / 36190186669)) (n := 12)
    (lo := (639332253 / 1000000000)) (hi := (319666127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23690186669 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23690186669 / 12500000000) = 1/(12500000000 / 23690186669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (639332253 / 1000000000) (319666127 / 500000000) (Real.log (23690186669 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23690186669 / 12500000000) = -Real.log (12500000000 / 23690186669) := by
    rw [show ((23690186669 / 12500000000) : ℝ) = ((12500000000 / 23690186669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0225

end


