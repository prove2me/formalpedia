-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0198Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0198Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:15:52.246901+00:00
-- url     : https://prove2.me/theorems/6d8dc915-6f1b-4cd4-a37a-2b50dbdf4e56
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0198Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0199Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0198Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0199Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0200Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0201Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0202Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0203Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0204Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0198Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0199Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0200Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0201Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0202Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0203Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0204Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0198Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0199Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0200Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0201Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0202Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0203Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0204Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0198Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0199Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0200Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0201Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0202Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0203Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0204Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0198Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0198
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

theorem reflection_log_1_neg : (266562171 / 1000000000) ≤ -Real.log (1280 / 1671) ∧
    -Real.log (1280 / 1671) ≤ (66640543 / 250000000) := by
  have h := checkLog_sound (w := (391 / 2951)) (n := 12)
    (lo := (266562171 / 1000000000)) (hi := (66640543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1671 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1671 / 1280) = 1/(1280 / 1671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (266562171 / 1000000000) (66640543 / 250000000) (Real.log (1671 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1671 / 1280) = -Real.log (1280 / 1671) := by
    rw [show ((1671 / 1280) : ℝ) = ((1280 / 1671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (364518121 / 1000000000) ≤ -Real.log (889 / 1280) ∧
    -Real.log (889 / 1280) ≤ (182259061 / 500000000) := by
  have h := checkLog_sound (w := (391 / 2169)) (n := 12)
    (lo := (364518121 / 1000000000)) (hi := (182259061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 889) = 1/(889 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-182259061 / 500000000) (-364518121 / 1000000000) (Real.log (889 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (266113237 / 1000000000) ≤ -Real.log (5120 / 6681) ∧
    -Real.log (5120 / 6681) ≤ (133056619 / 500000000) := by
  have h := checkLog_sound (w := (1561 / 11801)) (n := 12)
    (lo := (266113237 / 1000000000)) (hi := (133056619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6681 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6681 / 5120) = 1/(5120 / 6681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (266113237 / 1000000000) (133056619 / 500000000) (Real.log (6681 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6681 / 5120) = -Real.log (5120 / 6681) := by
    rw [show ((6681 / 5120) : ℝ) = ((5120 / 6681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (22729677 / 62500000) ≤ -Real.log (3559 / 5120) ∧
    -Real.log (3559 / 5120) ≤ (363674833 / 1000000000) := by
  have h := checkLog_sound (w := (1561 / 8679)) (n := 12)
    (lo := (22729677 / 62500000)) (hi := (363674833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3559) = 1/(3559 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-363674833 / 1000000000) (-22729677 / 62500000) (Real.log (3559 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (476816307 / 1000000000) ≤ -Real.log (640 / 1031) ∧
    -Real.log (640 / 1031) ≤ (119204077 / 250000000) := by
  have h := checkLog_sound (w := (391 / 1671)) (n := 12)
    (lo := (476816307 / 1000000000)) (hi := (119204077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1031 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1031 / 640) = 1/(640 / 1031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (476816307 / 1000000000) (119204077 / 250000000) (Real.log (1031 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1031 / 640) = -Real.log (640 / 1031) := by
    rw [show ((1031 / 640) : ℝ) = ((640 / 1031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (944015279 / 1000000000) ≤ -Real.log (249 / 640) ∧
    -Real.log (249 / 640) ≤ (944015281 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 249) = 1/(249 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-944015281 / 1000000000) (-944015279 / 1000000000) (Real.log (249 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (476088593 / 1000000000) ≤ -Real.log (2560 / 4121) ∧
    -Real.log (2560 / 4121) ≤ (238044297 / 500000000) := by
  have h := checkLog_sound (w := (1561 / 6681)) (n := 12)
    (lo := (476088593 / 1000000000)) (hi := (238044297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4121 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4121 / 2560) = 1/(2560 / 4121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (476088593 / 1000000000) (238044297 / 500000000) (Real.log (4121 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4121 / 2560) = -Real.log (2560 / 4121) := by
    rw [show ((4121 / 2560) : ℝ) = ((2560 / 4121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (470503879 / 500000000) ≤ -Real.log (999 / 2560) ∧
    -Real.log (999 / 2560) ≤ (11762597 / 12500000) := by
  have h := checkLog_sound (w := (281 / 2279)) (n := 12)
    (lo := (123930289 / 500000000)) (hi := (247860579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 999) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 999) = 1/(999 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-11762597 / 12500000) (-470503879 / 500000000) (Real.log (999 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (182027373 / 500000000) ≤ -Real.log (1000000 / 1439153) ∧
    -Real.log (1000000 / 1439153) ≤ (364054747 / 1000000000) := by
  have h := checkLog_sound (w := (439153 / 2439153)) (n := 12)
    (lo := (182027373 / 500000000)) (hi := (364054747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439153 / 1000000) = 1/(1000000 / 1439153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (182027373 / 500000000) (364054747 / 1000000000) (Real.log (1439153 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1439153 / 1000000) = -Real.log (1000000 / 1439153) := by
    rw [show ((1439153 / 1000000) : ℝ) = ((1000000 / 1439153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (578307137 / 1000000000) ≤ -Real.log (560847 / 1000000) ∧
    -Real.log (560847 / 1000000) ≤ (289153569 / 500000000) := by
  have h := checkLog_sound (w := (439153 / 1560847)) (n := 12)
    (lo := (578307137 / 1000000000)) (hi := (289153569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 560847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 560847) = 1/(560847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-289153569 / 500000000) (-578307137 / 1000000000) (Real.log (560847 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (182333709 / 500000000) ≤ -Real.log (200000 / 288007) ∧
    -Real.log (200000 / 288007) ≤ (364667419 / 1000000000) := by
  have h := checkLog_sound (w := (88007 / 488007)) (n := 12)
    (lo := (182333709 / 500000000)) (hi := (364667419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288007 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288007 / 200000) = 1/(200000 / 288007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (182333709 / 500000000) (364667419 / 1000000000) (Real.log (288007 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (288007 / 200000) = -Real.log (200000 / 288007) := by
    rw [show ((288007 / 200000) : ℝ) = ((200000 / 288007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (579880997 / 1000000000) ≤ -Real.log (111993 / 200000) ∧
    -Real.log (111993 / 200000) ≤ (289940499 / 500000000) := by
  have h := checkLog_sound (w := (88007 / 311993)) (n := 12)
    (lo := (579880997 / 1000000000)) (hi := (289940499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 111993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 111993) = 1/(111993 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-289940499 / 500000000) (-579880997 / 1000000000) (Real.log (111993 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (70918701 / 250000000) ≤ -Real.log (1000000 / 1328001) ∧
    -Real.log (1000000 / 1328001) ≤ (56734961 / 200000000) := by
  have h := checkLog_sound (w := (328001 / 2328001)) (n := 12)
    (lo := (70918701 / 250000000)) (hi := (56734961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328001 / 1000000) = 1/(1000000 / 1328001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (70918701 / 250000000) (56734961 / 200000000) (Real.log (1328001 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1328001 / 1000000) = -Real.log (1000000 / 1328001) := by
    rw [show ((1328001 / 1000000) : ℝ) = ((1000000 / 1328001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (198749213 / 500000000) ≤ -Real.log (671999 / 1000000) ∧
    -Real.log (671999 / 1000000) ≤ (397498427 / 1000000000) := by
  have h := checkLog_sound (w := (328001 / 1671999)) (n := 12)
    (lo := (198749213 / 500000000)) (hi := (397498427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671999) = 1/(671999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-397498427 / 1000000000) (-198749213 / 500000000) (Real.log (671999 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (284226609 / 1000000000) ≤ -Real.log (500000 / 664367) ∧
    -Real.log (500000 / 664367) ≤ (28422661 / 100000000) := by
  have h := checkLog_sound (w := (164367 / 1164367)) (n := 12)
    (lo := (284226609 / 1000000000)) (hi := (28422661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664367 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664367 / 500000) = 1/(500000 / 664367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (284226609 / 1000000000) (28422661 / 100000000) (Real.log (664367 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (664367 / 500000) = -Real.log (500000 / 664367) := by
    rw [show ((664367 / 500000) : ℝ) = ((500000 / 664367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (398589797 / 1000000000) ≤ -Real.log (335633 / 500000) ∧
    -Real.log (335633 / 500000) ≤ (199294899 / 500000000) := by
  have h := checkLog_sound (w := (164367 / 835633)) (n := 12)
    (lo := (398589797 / 1000000000)) (hi := (199294899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 335633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 335633) = 1/(335633 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-199294899 / 500000000) (-398589797 / 1000000000) (Real.log (335633 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (942361883 / 1000000000) ≤ -Real.log (125000000000 / 320754367947) ∧
    -Real.log (125000000000 / 320754367947) ≤ (188472377 / 200000000) := by
  have h := checkLog_sound (w := (70754367947 / 570754367947)) (n := 12)
    (lo := (249214703 / 1000000000)) (hi := (15575919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320754367947 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320754367947 / 250000000000) = 1/(125000000000 / 320754367947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (942361883 / 1000000000) (188472377 / 200000000) (Real.log (320754367947 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (320754367947 / 125000000000) = -Real.log (125000000000 / 320754367947) := by
    rw [show ((320754367947 / 125000000000) : ℝ) = ((125000000000 / 320754367947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (188909683 / 200000000) ≤ -Real.log (250000000000 / 642912949917) ∧
    -Real.log (250000000000 / 642912949917) ≤ (944548417 / 1000000000) := by
  have h := checkLog_sound (w := (142912949917 / 1142912949917)) (n := 12)
    (lo := (50280247 / 200000000)) (hi := (62850309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642912949917 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(642912949917 / 500000000000) = 1/(250000000000 / 642912949917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (188909683 / 200000000) (944548417 / 1000000000) (Real.log (642912949917 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (642912949917 / 250000000000) = -Real.log (250000000000 / 642912949917) := by
    rw [show ((642912949917 / 250000000000) : ℝ) = ((250000000000 / 642912949917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (68117323 / 100000000) ≤ -Real.log (20000000000 / 39523898101) ∧
    -Real.log (20000000000 / 39523898101) ≤ (681173231 / 1000000000) := by
  have h := checkLog_sound (w := (19523898101 / 59523898101)) (n := 12)
    (lo := (68117323 / 100000000)) (hi := (681173231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39523898101 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39523898101 / 20000000000) = 1/(20000000000 / 39523898101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (68117323 / 100000000) (681173231 / 1000000000) (Real.log (39523898101 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (39523898101 / 20000000000) = -Real.log (20000000000 / 39523898101) := by
    rw [show ((39523898101 / 20000000000) : ℝ) = ((20000000000 / 39523898101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (341408203 / 500000000) ≤ -Real.log (62500000000 / 123715300641) ∧
    -Real.log (62500000000 / 123715300641) ≤ (682816407 / 1000000000) := by
  have h := checkLog_sound (w := (61215300641 / 186215300641)) (n := 12)
    (lo := (341408203 / 500000000)) (hi := (682816407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123715300641 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123715300641 / 62500000000) = 1/(62500000000 / 123715300641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (341408203 / 500000000) (682816407 / 1000000000) (Real.log (123715300641 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (123715300641 / 62500000000) = -Real.log (62500000000 / 123715300641) := by
    rw [show ((123715300641 / 62500000000) : ℝ) = ((62500000000 / 123715300641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0198

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0199Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0199
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

theorem reflection_log_1_neg : (266113237 / 1000000000) ≤ -Real.log (5120 / 6681) ∧
    -Real.log (5120 / 6681) ≤ (133056619 / 500000000) := by
  have h := checkLog_sound (w := (1561 / 11801)) (n := 12)
    (lo := (266113237 / 1000000000)) (hi := (133056619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6681 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6681 / 5120) = 1/(5120 / 6681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (266113237 / 1000000000) (133056619 / 500000000) (Real.log (6681 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6681 / 5120) = -Real.log (5120 / 6681) := by
    rw [show ((6681 / 5120) : ℝ) = ((5120 / 6681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (22729677 / 62500000) ≤ -Real.log (3559 / 5120) ∧
    -Real.log (3559 / 5120) ≤ (363674833 / 1000000000) := by
  have h := checkLog_sound (w := (1561 / 8679)) (n := 12)
    (lo := (22729677 / 62500000)) (hi := (363674833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3559) = 1/(3559 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-363674833 / 1000000000) (-22729677 / 62500000) (Real.log (3559 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132832051 / 500000000) ≤ -Real.log (2560 / 3339) ∧
    -Real.log (2560 / 3339) ≤ (265664103 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 5899)) (n := 12)
    (lo := (132832051 / 500000000)) (hi := (265664103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3339 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3339 / 2560) = 1/(2560 / 3339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132832051 / 500000000) (265664103 / 1000000000) (Real.log (3339 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3339 / 2560) = -Real.log (2560 / 3339) := by
    rw [show ((3339 / 2560) : ℝ) = ((2560 / 3339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (181416127 / 500000000) ≤ -Real.log (1781 / 2560) ∧
    -Real.log (1781 / 2560) ≤ (72566451 / 200000000) := by
  have h := checkLog_sound (w := (779 / 4341)) (n := 12)
    (lo := (181416127 / 500000000)) (hi := (72566451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1781) = 1/(1781 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-72566451 / 200000000) (-181416127 / 500000000) (Real.log (1781 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (476088593 / 1000000000) ≤ -Real.log (2560 / 4121) ∧
    -Real.log (2560 / 4121) ≤ (238044297 / 500000000) := by
  have h := checkLog_sound (w := (1561 / 6681)) (n := 12)
    (lo := (476088593 / 1000000000)) (hi := (238044297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4121 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4121 / 2560) = 1/(2560 / 4121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (476088593 / 1000000000) (238044297 / 500000000) (Real.log (4121 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4121 / 2560) = -Real.log (2560 / 4121) := by
    rw [show ((4121 / 2560) : ℝ) = ((2560 / 4121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (470503879 / 500000000) ≤ -Real.log (999 / 2560) ∧
    -Real.log (999 / 2560) ≤ (11762597 / 12500000) := by
  have h := checkLog_sound (w := (281 / 2279)) (n := 12)
    (lo := (123930289 / 500000000)) (hi := (247860579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 999) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 999) = 1/(999 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11762597 / 12500000) (-470503879 / 500000000) (Real.log (999 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (9507207 / 20000000) ≤ -Real.log (1280 / 2059) ∧
    -Real.log (1280 / 2059) ≤ (475360351 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 3339)) (n := 12)
    (lo := (9507207 / 20000000)) (hi := (475360351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2059 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2059 / 1280) = 1/(1280 / 2059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (9507207 / 20000000) (475360351 / 1000000000) (Real.log (2059 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2059 / 1280) = -Real.log (1280 / 2059) := by
    rw [show ((2059 / 1280) : ℝ) = ((1280 / 2059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (187601851 / 200000000) ≤ -Real.log (501 / 1280) ∧
    -Real.log (501 / 1280) ≤ (938009257 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 1141)) (n := 12)
    (lo := (9794483 / 40000000)) (hi := (61215519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 501) = 1/(501 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-938009257 / 1000000000) (-187601851 / 200000000) (Real.log (501 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (363442393 / 1000000000) ≤ -Real.log (15625 / 22473) ∧
    -Real.log (15625 / 22473) ≤ (181721197 / 500000000) := by
  have h := checkLog_sound (w := (3424 / 19049)) (n := 12)
    (lo := (363442393 / 1000000000)) (hi := (181721197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22473 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22473 / 15625) = 1/(15625 / 22473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (363442393 / 1000000000) (181721197 / 500000000) (Real.log (22473 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (22473 / 15625) = -Real.log (15625 / 22473) := by
    rw [show ((22473 / 15625) : ℝ) = ((15625 / 22473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (144184383 / 250000000) ≤ -Real.log (8777 / 15625) ∧
    -Real.log (8777 / 15625) ≤ (576737533 / 1000000000) := by
  have h := checkLog_sound (w := (3424 / 12201)) (n := 12)
    (lo := (144184383 / 250000000)) (hi := (576737533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 8777) = 1/(8777 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-576737533 / 1000000000) (-144184383 / 250000000) (Real.log (8777 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4550693 / 12500000) ≤ -Real.log (500000 / 719577) ∧
    -Real.log (500000 / 719577) ≤ (364055441 / 1000000000) := by
  have h := checkLog_sound (w := (219577 / 1219577)) (n := 12)
    (lo := (4550693 / 12500000)) (hi := (364055441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719577 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719577 / 500000) = 1/(500000 / 719577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4550693 / 12500000) (364055441 / 1000000000) (Real.log (719577 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (719577 / 500000) = -Real.log (500000 / 719577) := by
    rw [show ((719577 / 500000) : ℝ) = ((500000 / 719577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (14457723 / 25000000) ≤ -Real.log (280423 / 500000) ∧
    -Real.log (280423 / 500000) ≤ (578308921 / 1000000000) := by
  have h := checkLog_sound (w := (219577 / 780423)) (n := 12)
    (lo := (14457723 / 25000000)) (hi := (578308921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 280423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 280423) = 1/(280423 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-578308921 / 1000000000) (-14457723 / 25000000) (Real.log (280423 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (283124201 / 1000000000) ≤ -Real.log (100000 / 132727) ∧
    -Real.log (100000 / 132727) ≤ (141562101 / 500000000) := by
  have h := checkLog_sound (w := (32727 / 232727)) (n := 12)
    (lo := (283124201 / 1000000000)) (hi := (141562101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132727 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132727 / 100000) = 1/(100000 / 132727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (283124201 / 1000000000) (141562101 / 500000000) (Real.log (132727 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (132727 / 100000) = -Real.log (100000 / 132727) := by
    rw [show ((132727 / 100000) : ℝ) = ((100000 / 132727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (198205609 / 500000000) ≤ -Real.log (67273 / 100000) ∧
    -Real.log (67273 / 100000) ≤ (396411219 / 1000000000) := by
  have h := checkLog_sound (w := (32727 / 167273)) (n := 12)
    (lo := (198205609 / 500000000)) (hi := (396411219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 67273) = 1/(67273 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-396411219 / 1000000000) (-198205609 / 500000000) (Real.log (67273 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (283675557 / 1000000000) ≤ -Real.log (500000 / 664001) ∧
    -Real.log (500000 / 664001) ≤ (141837779 / 500000000) := by
  have h := checkLog_sound (w := (164001 / 1164001)) (n := 12)
    (lo := (283675557 / 1000000000)) (hi := (141837779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664001 / 500000) = 1/(500000 / 664001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (283675557 / 1000000000) (141837779 / 500000000) (Real.log (664001 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (664001 / 500000) = -Real.log (500000 / 664001) := by
    rw [show ((664001 / 500000) : ℝ) = ((500000 / 664001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (198749957 / 500000000) ≤ -Real.log (335999 / 500000) ∧
    -Real.log (335999 / 500000) ≤ (79499983 / 200000000) := by
  have h := checkLog_sound (w := (164001 / 835999)) (n := 12)
    (lo := (198749957 / 500000000)) (hi := (79499983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 335999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 335999) = 1/(335999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-79499983 / 200000000) (-198749957 / 500000000) (Real.log (335999 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (235044981 / 250000000) ≤ -Real.log (500000000000 / 1280221032243) ∧
    -Real.log (500000000000 / 1280221032243) ≤ (470089963 / 500000000) := by
  have h := checkLog_sound (w := (280221032243 / 2280221032243)) (n := 12)
    (lo := (30879093 / 125000000)) (hi := (49406549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280221032243 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280221032243 / 1000000000000) = 1/(500000000000 / 1280221032243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (235044981 / 250000000) (470089963 / 500000000) (Real.log (1280221032243 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1280221032243 / 500000000000) = -Real.log (500000000000 / 1280221032243) := by
    rw [show ((1280221032243 / 500000000000) : ℝ) = ((500000000000 / 1280221032243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (942364361 / 1000000000) ≤ -Real.log (250000000000 / 641510325473) ∧
    -Real.log (250000000000 / 641510325473) ≤ (942364363 / 1000000000) := by
  have h := checkLog_sound (w := (141510325473 / 1141510325473)) (n := 12)
    (lo := (249217181 / 1000000000)) (hi := (124608591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641510325473 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(641510325473 / 500000000000) = 1/(250000000000 / 641510325473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (942364361 / 1000000000) (942364363 / 1000000000) (Real.log (641510325473 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (641510325473 / 250000000000) = -Real.log (250000000000 / 641510325473) := by
    rw [show ((641510325473 / 250000000000) : ℝ) = ((250000000000 / 641510325473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (679535419 / 1000000000) ≤ -Real.log (250000000000 / 493240230107) ∧
    -Real.log (250000000000 / 493240230107) ≤ (33976771 / 50000000) := by
  have h := checkLog_sound (w := (243240230107 / 743240230107)) (n := 12)
    (lo := (679535419 / 1000000000)) (hi := (33976771 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493240230107 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493240230107 / 250000000000) = 1/(250000000000 / 493240230107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (679535419 / 1000000000) (33976771 / 50000000) (Real.log (493240230107 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (493240230107 / 250000000000) = -Real.log (250000000000 / 493240230107) := by
    rw [show ((493240230107 / 250000000000) : ℝ) = ((250000000000 / 493240230107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (681175471 / 1000000000) ≤ -Real.log (125000000000 / 247024916741) ∧
    -Real.log (125000000000 / 247024916741) ≤ (42573467 / 62500000) := by
  have h := checkLog_sound (w := (122024916741 / 372024916741)) (n := 12)
    (lo := (681175471 / 1000000000)) (hi := (42573467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247024916741 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247024916741 / 125000000000) = 1/(125000000000 / 247024916741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (681175471 / 1000000000) (42573467 / 62500000) (Real.log (247024916741 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (247024916741 / 125000000000) = -Real.log (125000000000 / 247024916741) := by
    rw [show ((247024916741 / 125000000000) : ℝ) = ((125000000000 / 247024916741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0199

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0200Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0200
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

theorem reflection_log_1_neg : (132832051 / 500000000) ≤ -Real.log (2560 / 3339) ∧
    -Real.log (2560 / 3339) ≤ (265664103 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 5899)) (n := 12)
    (lo := (132832051 / 500000000)) (hi := (265664103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3339 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3339 / 2560) = 1/(2560 / 3339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132832051 / 500000000) (265664103 / 1000000000) (Real.log (3339 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3339 / 2560) = -Real.log (2560 / 3339) := by
    rw [show ((3339 / 2560) : ℝ) = ((2560 / 3339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (181416127 / 500000000) ≤ -Real.log (1781 / 2560) ∧
    -Real.log (1781 / 2560) ≤ (72566451 / 200000000) := by
  have h := checkLog_sound (w := (779 / 4341)) (n := 12)
    (lo := (181416127 / 500000000)) (hi := (72566451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1781) = 1/(1781 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-72566451 / 200000000) (-181416127 / 500000000) (Real.log (1781 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (53042953 / 200000000) ≤ -Real.log (1024 / 1335) ∧
    -Real.log (1024 / 1335) ≤ (132607383 / 500000000) := by
  have h := checkLog_sound (w := (311 / 2359)) (n := 12)
    (lo := (53042953 / 200000000)) (hi := (132607383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1335 / 1024) = 1/(1024 / 1335) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (53042953 / 200000000) (132607383 / 500000000) (Real.log (1335 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1335 / 1024) = -Real.log (1024 / 1335) := by
    rw [show ((1335 / 1024) : ℝ) = ((1024 / 1335) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (72398077 / 200000000) ≤ -Real.log (713 / 1024) ∧
    -Real.log (713 / 1024) ≤ (180995193 / 500000000) := by
  have h := checkLog_sound (w := (311 / 1737)) (n := 12)
    (lo := (72398077 / 200000000)) (hi := (180995193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 713) = 1/(713 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-180995193 / 500000000) (-72398077 / 200000000) (Real.log (713 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (9507207 / 20000000) ≤ -Real.log (1280 / 2059) ∧
    -Real.log (1280 / 2059) ≤ (475360351 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 3339)) (n := 12)
    (lo := (9507207 / 20000000)) (hi := (475360351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2059 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2059 / 1280) = 1/(1280 / 2059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (9507207 / 20000000) (475360351 / 1000000000) (Real.log (2059 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2059 / 1280) = -Real.log (1280 / 2059) := by
    rw [show ((2059 / 1280) : ℝ) = ((1280 / 2059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (187601851 / 200000000) ≤ -Real.log (501 / 1280) ∧
    -Real.log (501 / 1280) ≤ (938009257 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 1141)) (n := 12)
    (lo := (9794483 / 40000000)) (hi := (61215519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 501) = 1/(501 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-938009257 / 1000000000) (-187601851 / 200000000) (Real.log (501 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18985263 / 40000000) ≤ -Real.log (512 / 823) ∧
    -Real.log (512 / 823) ≤ (59328947 / 125000000) := by
  have h := checkLog_sound (w := (311 / 1335)) (n := 12)
    (lo := (18985263 / 40000000)) (hi := (59328947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823 / 512) = 1/(512 / 823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18985263 / 40000000) (59328947 / 125000000) (Real.log (823 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (823 / 512) = -Real.log (512 / 823) := by
    rw [show ((823 / 512) : ℝ) = ((512 / 823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (233754929 / 250000000) ≤ -Real.log (201 / 512) ∧
    -Real.log (201 / 512) ≤ (467509859 / 500000000) := by
  have h := checkLog_sound (w := (55 / 457)) (n := 12)
    (lo := (30234067 / 125000000)) (hi := (241872537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 201) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 201) = 1/(201 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-467509859 / 500000000) (-233754929 / 250000000) (Real.log (201 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (11338427 / 31250000) ≤ -Real.log (1000000 / 1437391) ∧
    -Real.log (1000000 / 1437391) ≤ (72565933 / 200000000) := by
  have h := checkLog_sound (w := (437391 / 2437391)) (n := 12)
    (lo := (11338427 / 31250000)) (hi := (72565933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1437391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1437391 / 1000000) = 1/(1000000 / 1437391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (11338427 / 31250000) (72565933 / 200000000) (Real.log (1437391 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1437391 / 1000000) = -Real.log (1000000 / 1437391) := by
    rw [show ((1437391 / 1000000) : ℝ) = ((1000000 / 1437391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (115034077 / 200000000) ≤ -Real.log (562609 / 1000000) ∧
    -Real.log (562609 / 1000000) ≤ (287585193 / 500000000) := by
  have h := checkLog_sound (w := (437391 / 1562609)) (n := 12)
    (lo := (115034077 / 200000000)) (hi := (287585193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 562609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 562609) = 1/(562609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-287585193 / 500000000) (-115034077 / 200000000) (Real.log (562609 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (22715193 / 62500000) ≤ -Real.log (1000000 / 1438273) ∧
    -Real.log (1000000 / 1438273) ≤ (363443089 / 1000000000) := by
  have h := checkLog_sound (w := (438273 / 2438273)) (n := 12)
    (lo := (22715193 / 62500000)) (hi := (363443089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1438273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1438273 / 1000000) = 1/(1000000 / 1438273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (22715193 / 62500000) (363443089 / 1000000000) (Real.log (1438273 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1438273 / 1000000) = -Real.log (1000000 / 1438273) := by
    rw [show ((1438273 / 1000000) : ℝ) = ((1000000 / 1438273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36046207 / 62500000) ≤ -Real.log (561727 / 1000000) ∧
    -Real.log (561727 / 1000000) ≤ (576739313 / 1000000000) := by
  have h := checkLog_sound (w := (438273 / 1561727)) (n := 12)
    (lo := (36046207 / 62500000)) (hi := (576739313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 561727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 561727) = 1/(561727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-576739313 / 1000000000) (-36046207 / 62500000) (Real.log (561727 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (141286647 / 500000000) ≤ -Real.log (1000000 / 1326539) ∧
    -Real.log (1000000 / 1326539) ≤ (56514659 / 200000000) := by
  have h := checkLog_sound (w := (326539 / 2326539)) (n := 12)
    (lo := (141286647 / 500000000)) (hi := (56514659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326539 / 1000000) = 1/(1000000 / 1326539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (141286647 / 500000000) (56514659 / 200000000) (Real.log (1326539 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1326539 / 1000000) = -Real.log (1000000 / 1326539) := by
    rw [show ((1326539 / 1000000) : ℝ) = ((1000000 / 1326539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (395325191 / 1000000000) ≤ -Real.log (673461 / 1000000) ∧
    -Real.log (673461 / 1000000) ≤ (49415649 / 125000000) := by
  have h := checkLog_sound (w := (326539 / 1673461)) (n := 12)
    (lo := (395325191 / 1000000000)) (hi := (49415649 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673461) = 1/(673461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-49415649 / 125000000) (-395325191 / 1000000000) (Real.log (673461 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (141562477 / 500000000) ≤ -Real.log (1000000 / 1327271) ∧
    -Real.log (1000000 / 1327271) ≤ (56624991 / 200000000) := by
  have h := checkLog_sound (w := (327271 / 2327271)) (n := 12)
    (lo := (141562477 / 500000000)) (hi := (56624991 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327271 / 1000000) = 1/(1000000 / 1327271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (141562477 / 500000000) (56624991 / 200000000) (Real.log (1327271 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1327271 / 1000000) = -Real.log (1000000 / 1327271) := by
    rw [show ((1327271 / 1000000) : ℝ) = ((1000000 / 1327271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (79282541 / 200000000) ≤ -Real.log (672729 / 1000000) ∧
    -Real.log (672729 / 1000000) ≤ (198206353 / 500000000) := by
  have h := checkLog_sound (w := (327271 / 1672729)) (n := 12)
    (lo := (79282541 / 200000000)) (hi := (198206353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 672729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 672729) = 1/(672729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-198206353 / 500000000) (-79282541 / 200000000) (Real.log (672729 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (18760001 / 20000000) ≤ -Real.log (125000000000 / 319358337673) ∧
    -Real.log (125000000000 / 319358337673) ≤ (234500013 / 250000000) := by
  have h := checkLog_sound (w := (69358337673 / 569358337673)) (n := 12)
    (lo := (24485287 / 100000000)) (hi := (244852871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319358337673 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(319358337673 / 250000000000) = 1/(125000000000 / 319358337673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (18760001 / 20000000) (234500013 / 250000000) (Real.log (319358337673 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (319358337673 / 125000000000) = -Real.log (125000000000 / 319358337673) := by
    rw [show ((319358337673 / 125000000000) : ℝ) = ((125000000000 / 319358337673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (940182399 / 1000000000) ≤ -Real.log (125000000000 / 320056050359) ∧
    -Real.log (125000000000 / 320056050359) ≤ (940182401 / 1000000000) := by
  have h := checkLog_sound (w := (70056050359 / 570056050359)) (n := 12)
    (lo := (247035219 / 1000000000)) (hi := (12351761 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320056050359 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320056050359 / 250000000000) = 1/(125000000000 / 320056050359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (940182399 / 1000000000) (940182401 / 1000000000) (Real.log (320056050359 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (320056050359 / 125000000000) = -Real.log (125000000000 / 320056050359) := by
    rw [show ((320056050359 / 125000000000) : ℝ) = ((125000000000 / 320056050359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (338949243 / 500000000) ≤ -Real.log (500000000000 / 984866978191) ∧
    -Real.log (500000000000 / 984866978191) ≤ (677898487 / 1000000000) := by
  have h := checkLog_sound (w := (484866978191 / 1484866978191)) (n := 12)
    (lo := (338949243 / 500000000)) (hi := (677898487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((984866978191 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(984866978191 / 500000000000) = 1/(500000000000 / 984866978191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (338949243 / 500000000) (677898487 / 1000000000) (Real.log (984866978191 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (984866978191 / 500000000000) = -Real.log (500000000000 / 984866978191) := by
    rw [show ((984866978191 / 500000000000) : ℝ) = ((500000000000 / 984866978191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (679537659 / 1000000000) ≤ -Real.log (250000000000 / 493241334921) ∧
    -Real.log (250000000000 / 493241334921) ≤ (33976883 / 50000000) := by
  have h := checkLog_sound (w := (243241334921 / 743241334921)) (n := 12)
    (lo := (679537659 / 1000000000)) (hi := (33976883 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493241334921 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493241334921 / 250000000000) = 1/(250000000000 / 493241334921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (679537659 / 1000000000) (33976883 / 50000000) (Real.log (493241334921 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (493241334921 / 250000000000) = -Real.log (250000000000 / 493241334921) := by
    rw [show ((493241334921 / 250000000000) : ℝ) = ((250000000000 / 493241334921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0200

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0201Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0201
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

theorem reflection_log_1_neg : (53042953 / 200000000) ≤ -Real.log (1024 / 1335) ∧
    -Real.log (1024 / 1335) ≤ (132607383 / 500000000) := by
  have h := checkLog_sound (w := (311 / 2359)) (n := 12)
    (lo := (53042953 / 200000000)) (hi := (132607383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1335 / 1024) = 1/(1024 / 1335) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (53042953 / 200000000) (132607383 / 500000000) (Real.log (1335 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1335 / 1024) = -Real.log (1024 / 1335) := by
    rw [show ((1335 / 1024) : ℝ) = ((1024 / 1335) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (72398077 / 200000000) ≤ -Real.log (713 / 1024) ∧
    -Real.log (713 / 1024) ≤ (180995193 / 500000000) := by
  have h := checkLog_sound (w := (311 / 1737)) (n := 12)
    (lo := (72398077 / 200000000)) (hi := (180995193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 713) = 1/(713 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-180995193 / 500000000) (-72398077 / 200000000) (Real.log (713 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132382613 / 500000000) ≤ -Real.log (320 / 417) ∧
    -Real.log (320 / 417) ≤ (264765227 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 737)) (n := 12)
    (lo := (132382613 / 500000000)) (hi := (264765227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417 / 320) = 1/(320 / 417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132382613 / 500000000) (264765227 / 1000000000) (Real.log (417 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (417 / 320) = -Real.log (320 / 417) := by
    rw [show ((417 / 320) : ℝ) = ((320 / 417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (45143653 / 125000000) ≤ -Real.log (223 / 320) ∧
    -Real.log (223 / 320) ≤ (14445969 / 40000000) := by
  have h := checkLog_sound (w := (97 / 543)) (n := 12)
    (lo := (45143653 / 125000000)) (hi := (14445969 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 223) = 1/(223 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14445969 / 40000000) (-45143653 / 125000000) (Real.log (223 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18985263 / 40000000) ≤ -Real.log (512 / 823) ∧
    -Real.log (512 / 823) ≤ (59328947 / 125000000) := by
  have h := checkLog_sound (w := (311 / 1335)) (n := 12)
    (lo := (18985263 / 40000000)) (hi := (59328947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823 / 512) = 1/(512 / 823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18985263 / 40000000) (59328947 / 125000000) (Real.log (823 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (823 / 512) = -Real.log (512 / 823) := by
    rw [show ((823 / 512) : ℝ) = ((512 / 823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (233754929 / 250000000) ≤ -Real.log (201 / 512) ∧
    -Real.log (201 / 512) ≤ (467509859 / 500000000) := by
  have h := checkLog_sound (w := (55 / 457)) (n := 12)
    (lo := (30234067 / 125000000)) (hi := (241872537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 201) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 201) = 1/(201 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-467509859 / 500000000) (-233754929 / 250000000) (Real.log (201 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (473902269 / 1000000000) ≤ -Real.log (160 / 257) ∧
    -Real.log (160 / 257) ≤ (47390227 / 100000000) := by
  have h := checkLog_sound (w := (97 / 417)) (n := 12)
    (lo := (473902269 / 1000000000)) (hi := (47390227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257 / 160) = 1/(160 / 257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (473902269 / 1000000000) (47390227 / 100000000) (Real.log (257 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (257 / 160) = -Real.log (160 / 257) := by
    rw [show ((257 / 160) : ℝ) = ((160 / 257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58252443 / 62500000) ≤ -Real.log (63 / 160) ∧
    -Real.log (63 / 160) ≤ (93203909 / 100000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 63) = 1/(63 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-93203909 / 100000000) (-58252443 / 62500000) (Real.log (63 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4527707 / 12500000) ≤ -Real.log (100000 / 143651) ∧
    -Real.log (100000 / 143651) ≤ (362216561 / 1000000000) := by
  have h := checkLog_sound (w := (43651 / 243651)) (n := 12)
    (lo := (4527707 / 12500000)) (hi := (362216561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143651 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143651 / 100000) = 1/(100000 / 143651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4527707 / 12500000) (362216561 / 1000000000) (Real.log (143651 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (143651 / 100000) = -Real.log (100000 / 143651) := by
    rw [show ((143651 / 100000) : ℝ) = ((100000 / 143651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (573605691 / 1000000000) ≤ -Real.log (56349 / 100000) ∧
    -Real.log (56349 / 100000) ≤ (143401423 / 250000000) := by
  have h := checkLog_sound (w := (43651 / 156349)) (n := 12)
    (lo := (573605691 / 1000000000)) (hi := (143401423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 56349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 56349) = 1/(56349 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-143401423 / 250000000) (-573605691 / 1000000000) (Real.log (56349 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9070759 / 25000000) ≤ -Real.log (62500 / 89837) ∧
    -Real.log (62500 / 89837) ≤ (362830361 / 1000000000) := by
  have h := checkLog_sound (w := (27337 / 152337)) (n := 12)
    (lo := (9070759 / 25000000)) (hi := (362830361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89837 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89837 / 62500) = 1/(62500 / 89837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9070759 / 25000000) (362830361 / 1000000000) (Real.log (89837 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (89837 / 62500) = -Real.log (62500 / 89837) := by
    rw [show ((89837 / 62500) : ℝ) = ((62500 / 89837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (575172163 / 1000000000) ≤ -Real.log (35163 / 62500) ∧
    -Real.log (35163 / 62500) ≤ (143793041 / 250000000) := by
  have h := checkLog_sound (w := (27337 / 97663)) (n := 12)
    (lo := (575172163 / 1000000000)) (hi := (143793041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 35163) = 1/(35163 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-143793041 / 250000000) (-575172163 / 1000000000) (Real.log (35163 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (282022839 / 1000000000) ≤ -Real.log (1000000 / 1325809) ∧
    -Real.log (1000000 / 1325809) ≤ (7050571 / 25000000) := by
  have h := checkLog_sound (w := (325809 / 2325809)) (n := 12)
    (lo := (282022839 / 1000000000)) (hi := (7050571 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325809 / 1000000) = 1/(1000000 / 1325809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (282022839 / 1000000000) (7050571 / 25000000) (Real.log (1325809 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1325809 / 1000000) = -Real.log (1000000 / 1325809) := by
    rw [show ((1325809 / 1000000) : ℝ) = ((1000000 / 1325809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15769673 / 40000000) ≤ -Real.log (674191 / 1000000) ∧
    -Real.log (674191 / 1000000) ≤ (197120913 / 500000000) := by
  have h := checkLog_sound (w := (325809 / 1674191)) (n := 12)
    (lo := (15769673 / 40000000)) (hi := (197120913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674191) = 1/(674191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-197120913 / 500000000) (-15769673 / 40000000) (Real.log (674191 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (8830439 / 31250000) ≤ -Real.log (50000 / 66327) ∧
    -Real.log (50000 / 66327) ≤ (282574049 / 1000000000) := by
  have h := checkLog_sound (w := (16327 / 116327)) (n := 12)
    (lo := (8830439 / 31250000)) (hi := (282574049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66327 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66327 / 50000) = 1/(50000 / 66327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (8830439 / 31250000) (282574049 / 1000000000) (Real.log (66327 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (66327 / 50000) = -Real.log (50000 / 66327) := by
    rw [show ((66327 / 50000) : ℝ) = ((50000 / 66327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (98831669 / 250000000) ≤ -Real.log (33673 / 50000) ∧
    -Real.log (33673 / 50000) ≤ (395326677 / 1000000000) := by
  have h := checkLog_sound (w := (16327 / 83673)) (n := 12)
    (lo := (98831669 / 250000000)) (hi := (395326677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33673) = 1/(33673 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-395326677 / 1000000000) (-98831669 / 250000000) (Real.log (33673 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (233955563 / 250000000) ≤ -Real.log (250000000000 / 637327193029) ∧
    -Real.log (250000000000 / 637327193029) ≤ (467911127 / 500000000) := by
  have h := checkLog_sound (w := (137327193029 / 1137327193029)) (n := 12)
    (lo := (1895899 / 7812500)) (hi := (242675073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637327193029 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(637327193029 / 500000000000) = 1/(250000000000 / 637327193029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (233955563 / 250000000) (467911127 / 500000000) (Real.log (637327193029 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (637327193029 / 250000000000) = -Real.log (250000000000 / 637327193029) := by
    rw [show ((637327193029 / 250000000000) : ℝ) = ((250000000000 / 637327193029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (938002523 / 1000000000) ≤ -Real.log (31250000000 / 79839781873) ∧
    -Real.log (31250000000 / 79839781873) ≤ (37520101 / 40000000) := by
  have h := checkLog_sound (w := (17339781873 / 142339781873)) (n := 12)
    (lo := (244855343 / 1000000000)) (hi := (15303459 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79839781873 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(79839781873 / 62500000000) = 1/(31250000000 / 79839781873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (938002523 / 1000000000) (37520101 / 40000000) (Real.log (79839781873 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (79839781873 / 31250000000) = -Real.log (31250000000 / 79839781873) := by
    rw [show ((79839781873 / 31250000000) : ℝ) = ((31250000000 / 79839781873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (84533083 / 125000000) ≤ -Real.log (250000000000 / 491629597547) ∧
    -Real.log (250000000000 / 491629597547) ≤ (135252933 / 200000000) := by
  have h := checkLog_sound (w := (241629597547 / 741629597547)) (n := 12)
    (lo := (84533083 / 125000000)) (hi := (135252933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491629597547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491629597547 / 250000000000) = 1/(250000000000 / 491629597547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (84533083 / 125000000) (135252933 / 200000000) (Real.log (491629597547 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (491629597547 / 250000000000) = -Real.log (250000000000 / 491629597547) := by
    rw [show ((491629597547 / 250000000000) : ℝ) = ((250000000000 / 491629597547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (169475181 / 250000000) ≤ -Real.log (20000000000 / 39394767321) ∧
    -Real.log (20000000000 / 39394767321) ≤ (27116029 / 40000000) := by
  have h := checkLog_sound (w := (19394767321 / 59394767321)) (n := 12)
    (lo := (169475181 / 250000000)) (hi := (27116029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39394767321 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39394767321 / 20000000000) = 1/(20000000000 / 39394767321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (169475181 / 250000000) (27116029 / 40000000) (Real.log (39394767321 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (39394767321 / 20000000000) = -Real.log (20000000000 / 39394767321) := by
    rw [show ((39394767321 / 20000000000) : ℝ) = ((20000000000 / 39394767321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0201

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0202Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0202
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

theorem reflection_log_1_neg : (132382613 / 500000000) ≤ -Real.log (320 / 417) ∧
    -Real.log (320 / 417) ≤ (264765227 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 737)) (n := 12)
    (lo := (132382613 / 500000000)) (hi := (264765227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417 / 320) = 1/(320 / 417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132382613 / 500000000) (264765227 / 1000000000) (Real.log (417 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (417 / 320) = -Real.log (320 / 417) := by
    rw [show ((417 / 320) : ℝ) = ((320 / 417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (45143653 / 125000000) ≤ -Real.log (223 / 320) ∧
    -Real.log (223 / 320) ≤ (14445969 / 40000000) := by
  have h := checkLog_sound (w := (97 / 543)) (n := 12)
    (lo := (45143653 / 125000000)) (hi := (14445969 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 223) = 1/(223 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14445969 / 40000000) (-45143653 / 125000000) (Real.log (223 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66078871 / 250000000) ≤ -Real.log (5120 / 6669) ∧
    -Real.log (5120 / 6669) ≤ (52863097 / 200000000) := by
  have h := checkLog_sound (w := (1549 / 11789)) (n := 12)
    (lo := (66078871 / 250000000)) (hi := (52863097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6669 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6669 / 5120) = 1/(5120 / 6669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66078871 / 250000000) (52863097 / 200000000) (Real.log (6669 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6669 / 5120) = -Real.log (5120 / 6669) := by
    rw [show ((6669 / 5120) : ℝ) = ((5120 / 6669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36030877 / 100000000) ≤ -Real.log (3571 / 5120) ∧
    -Real.log (3571 / 5120) ≤ (360308771 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 8691)) (n := 12)
    (lo := (36030877 / 100000000)) (hi := (360308771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3571) = 1/(3571 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-360308771 / 1000000000) (-36030877 / 100000000) (Real.log (3571 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (473902269 / 1000000000) ≤ -Real.log (160 / 257) ∧
    -Real.log (160 / 257) ≤ (47390227 / 100000000) := by
  have h := checkLog_sound (w := (97 / 417)) (n := 12)
    (lo := (473902269 / 1000000000)) (hi := (47390227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257 / 160) = 1/(160 / 257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (473902269 / 1000000000) (47390227 / 100000000) (Real.log (257 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (257 / 160) = -Real.log (160 / 257) := by
    rw [show ((257 / 160) : ℝ) = ((160 / 257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58252443 / 62500000) ≤ -Real.log (63 / 160) ∧
    -Real.log (63 / 160) ≤ (93203909 / 100000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 63) = 1/(63 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-93203909 / 100000000) (-58252443 / 62500000) (Real.log (63 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (473172431 / 1000000000) ≤ -Real.log (2560 / 4109) ∧
    -Real.log (2560 / 4109) ≤ (29573277 / 62500000) := by
  have h := checkLog_sound (w := (1549 / 6669)) (n := 12)
    (lo := (473172431 / 1000000000)) (hi := (29573277 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4109 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4109 / 2560) = 1/(2560 / 4109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (473172431 / 1000000000) (29573277 / 62500000) (Real.log (4109 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4109 / 2560) = -Real.log (2560 / 4109) := by
    rw [show ((4109 / 2560) : ℝ) = ((2560 / 4109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (929067317 / 1000000000) ≤ -Real.log (1011 / 2560) ∧
    -Real.log (1011 / 2560) ≤ (929067319 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 2291)) (n := 12)
    (lo := (235920137 / 1000000000)) (hi := (117960069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1011) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1011) = 1/(1011 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-929067319 / 1000000000) (-929067317 / 1000000000) (Real.log (1011 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (361603777 / 1000000000) ≤ -Real.log (100000 / 143563) ∧
    -Real.log (100000 / 143563) ≤ (180801889 / 500000000) := by
  have h := checkLog_sound (w := (43563 / 243563)) (n := 12)
    (lo := (361603777 / 1000000000)) (hi := (180801889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143563 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143563 / 100000) = 1/(100000 / 143563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (361603777 / 1000000000) (180801889 / 500000000) (Real.log (143563 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (143563 / 100000) = -Real.log (100000 / 143563) := by
    rw [show ((143563 / 100000) : ℝ) = ((100000 / 143563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (286022607 / 500000000) ≤ -Real.log (56437 / 100000) ∧
    -Real.log (56437 / 100000) ≤ (114409043 / 200000000) := by
  have h := checkLog_sound (w := (43563 / 156437)) (n := 12)
    (lo := (286022607 / 500000000)) (hi := (114409043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 56437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 56437) = 1/(56437 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-114409043 / 200000000) (-286022607 / 500000000) (Real.log (56437 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (45277157 / 125000000) ≤ -Real.log (1000000 / 1436511) ∧
    -Real.log (1000000 / 1436511) ≤ (362217257 / 1000000000) := by
  have h := checkLog_sound (w := (436511 / 2436511)) (n := 12)
    (lo := (45277157 / 125000000)) (hi := (362217257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1436511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1436511 / 1000000) = 1/(1000000 / 1436511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (45277157 / 125000000) (362217257 / 1000000000) (Real.log (1436511 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1436511 / 1000000) = -Real.log (1000000 / 1436511) := by
    rw [show ((1436511 / 1000000) : ℝ) = ((1000000 / 1436511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (286803733 / 500000000) ≤ -Real.log (563489 / 1000000) ∧
    -Real.log (563489 / 1000000) ≤ (573607467 / 1000000000) := by
  have h := checkLog_sound (w := (436511 / 1563489)) (n := 12)
    (lo := (286803733 / 500000000)) (hi := (573607467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 563489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 563489) = 1/(563489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-573607467 / 1000000000) (-286803733 / 500000000) (Real.log (563489 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (140736417 / 500000000) ≤ -Real.log (25000 / 33127) ∧
    -Real.log (25000 / 33127) ≤ (56294567 / 200000000) := by
  have h := checkLog_sound (w := (8127 / 58127)) (n := 12)
    (lo := (140736417 / 500000000)) (hi := (56294567 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33127 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33127 / 25000) = 1/(25000 / 33127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (140736417 / 500000000) (56294567 / 200000000) (Real.log (33127 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (33127 / 25000) = -Real.log (25000 / 33127) := by
    rw [show ((33127 / 25000) : ℝ) = ((25000 / 33127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (393161113 / 1000000000) ≤ -Real.log (16873 / 25000) ∧
    -Real.log (16873 / 25000) ≤ (196580557 / 500000000) := by
  have h := checkLog_sound (w := (8127 / 41873)) (n := 12)
    (lo := (393161113 / 1000000000)) (hi := (196580557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 16873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 16873) = 1/(16873 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-196580557 / 500000000) (-393161113 / 1000000000) (Real.log (16873 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (282023593 / 1000000000) ≤ -Real.log (100000 / 132581) ∧
    -Real.log (100000 / 132581) ≤ (141011797 / 500000000) := by
  have h := checkLog_sound (w := (32581 / 232581)) (n := 12)
    (lo := (282023593 / 1000000000)) (hi := (141011797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132581 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132581 / 100000) = 1/(100000 / 132581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (282023593 / 1000000000) (141011797 / 500000000) (Real.log (132581 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (132581 / 100000) = -Real.log (100000 / 132581) := by
    rw [show ((132581 / 100000) : ℝ) = ((100000 / 132581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (98560827 / 250000000) ≤ -Real.log (67419 / 100000) ∧
    -Real.log (67419 / 100000) ≤ (394243309 / 1000000000) := by
  have h := checkLog_sound (w := (32581 / 167419)) (n := 12)
    (lo := (98560827 / 250000000)) (hi := (394243309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 67419) = 1/(67419 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-394243309 / 1000000000) (-98560827 / 250000000) (Real.log (67419 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (93364899 / 100000000) ≤ -Real.log (62500000000 / 158985904637) ∧
    -Real.log (62500000000 / 158985904637) ≤ (29176531 / 31250000) := by
  have h := checkLog_sound (w := (33985904637 / 283985904637)) (n := 12)
    (lo := (24050181 / 100000000)) (hi := (240501811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158985904637 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(158985904637 / 125000000000) = 1/(62500000000 / 158985904637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (93364899 / 100000000) (29176531 / 31250000) (Real.log (158985904637 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (158985904637 / 62500000000) = -Real.log (62500000000 / 158985904637) := by
    rw [show ((158985904637 / 62500000000) : ℝ) = ((62500000000 / 158985904637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (467912361 / 500000000) ≤ -Real.log (500000000000 / 1274657535463) ∧
    -Real.log (500000000000 / 1274657535463) ≤ (233956181 / 250000000) := by
  have h := checkLog_sound (w := (274657535463 / 2274657535463)) (n := 12)
    (lo := (121338771 / 500000000)) (hi := (242677543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274657535463 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1274657535463 / 1000000000000) = 1/(500000000000 / 1274657535463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (467912361 / 500000000) (233956181 / 250000000) (Real.log (1274657535463 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1274657535463 / 500000000000) = -Real.log (500000000000 / 1274657535463) := by
    rw [show ((1274657535463 / 500000000000) : ℝ) = ((500000000000 / 1274657535463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (168658487 / 250000000) ≤ -Real.log (125000000000 / 245414271321) ∧
    -Real.log (125000000000 / 245414271321) ≤ (674633949 / 1000000000) := by
  have h := checkLog_sound (w := (120414271321 / 370414271321)) (n := 12)
    (lo := (168658487 / 250000000)) (hi := (674633949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245414271321 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245414271321 / 125000000000) = 1/(125000000000 / 245414271321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (168658487 / 250000000) (674633949 / 1000000000) (Real.log (245414271321 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (245414271321 / 125000000000) = -Real.log (125000000000 / 245414271321) := by
    rw [show ((245414271321 / 125000000000) : ℝ) = ((125000000000 / 245414271321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (338133451 / 500000000) ≤ -Real.log (125000000000 / 245815348789) ∧
    -Real.log (125000000000 / 245815348789) ≤ (676266903 / 1000000000) := by
  have h := checkLog_sound (w := (120815348789 / 370815348789)) (n := 12)
    (lo := (338133451 / 500000000)) (hi := (676266903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245815348789 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245815348789 / 125000000000) = 1/(125000000000 / 245815348789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (338133451 / 500000000) (676266903 / 1000000000) (Real.log (245815348789 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (245815348789 / 125000000000) = -Real.log (125000000000 / 245815348789) := by
    rw [show ((245815348789 / 125000000000) : ℝ) = ((125000000000 / 245815348789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0202

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0203Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0203
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

theorem reflection_log_1_neg : (66078871 / 250000000) ≤ -Real.log (5120 / 6669) ∧
    -Real.log (5120 / 6669) ≤ (52863097 / 200000000) := by
  have h := checkLog_sound (w := (1549 / 11789)) (n := 12)
    (lo := (66078871 / 250000000)) (hi := (52863097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6669 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6669 / 5120) = 1/(5120 / 6669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66078871 / 250000000) (52863097 / 200000000) (Real.log (6669 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6669 / 5120) = -Real.log (5120 / 6669) := by
    rw [show ((6669 / 5120) : ℝ) = ((5120 / 6669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36030877 / 100000000) ≤ -Real.log (3571 / 5120) ∧
    -Real.log (3571 / 5120) ≤ (360308771 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 8691)) (n := 12)
    (lo := (36030877 / 100000000)) (hi := (360308771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3571) = 1/(3571 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-360308771 / 1000000000) (-36030877 / 100000000) (Real.log (3571 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13193277 / 50000000) ≤ -Real.log (2560 / 3333) ∧
    -Real.log (2560 / 3333) ≤ (263865541 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 5893)) (n := 12)
    (lo := (13193277 / 50000000)) (hi := (263865541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3333 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3333 / 2560) = 1/(2560 / 3333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13193277 / 50000000) (263865541 / 1000000000) (Real.log (3333 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3333 / 2560) = -Real.log (2560 / 3333) := by
    rw [show ((3333 / 2560) : ℝ) = ((2560 / 3333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (179734511 / 500000000) ≤ -Real.log (1787 / 2560) ∧
    -Real.log (1787 / 2560) ≤ (359469023 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 4347)) (n := 12)
    (lo := (179734511 / 500000000)) (hi := (359469023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1787) = 1/(1787 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-359469023 / 1000000000) (-179734511 / 500000000) (Real.log (1787 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (473172431 / 1000000000) ≤ -Real.log (2560 / 4109) ∧
    -Real.log (2560 / 4109) ≤ (29573277 / 62500000) := by
  have h := checkLog_sound (w := (1549 / 6669)) (n := 12)
    (lo := (473172431 / 1000000000)) (hi := (29573277 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4109 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4109 / 2560) = 1/(2560 / 4109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (473172431 / 1000000000) (29573277 / 62500000) (Real.log (4109 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4109 / 2560) = -Real.log (2560 / 4109) := by
    rw [show ((4109 / 2560) : ℝ) = ((2560 / 4109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (929067317 / 1000000000) ≤ -Real.log (1011 / 2560) ∧
    -Real.log (1011 / 2560) ≤ (929067319 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 2291)) (n := 12)
    (lo := (235920137 / 1000000000)) (hi := (117960069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1011) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1011) = 1/(1011 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-929067319 / 1000000000) (-929067317 / 1000000000) (Real.log (1011 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23622103 / 50000000) ≤ -Real.log (1280 / 2053) ∧
    -Real.log (1280 / 2053) ≤ (472442061 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 3333)) (n := 12)
    (lo := (23622103 / 50000000)) (hi := (472442061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2053 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2053 / 1280) = 1/(1280 / 2053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23622103 / 50000000) (472442061 / 1000000000) (Real.log (2053 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2053 / 1280) = -Real.log (1280 / 2053) := by
    rw [show ((2053 / 1280) : ℝ) = ((1280 / 2053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (28940761 / 31250000) ≤ -Real.log (507 / 1280) ∧
    -Real.log (507 / 1280) ≤ (463052177 / 500000000) := by
  have h := checkLog_sound (w := (133 / 1147)) (n := 12)
    (lo := (58239293 / 250000000)) (hi := (232957173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 507) = 1/(507 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-463052177 / 500000000) (-28940761 / 31250000) (Real.log (507 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (180495309 / 500000000) ≤ -Real.log (4000 / 5739) ∧
    -Real.log (4000 / 5739) ≤ (360990619 / 1000000000) := by
  have h := checkLog_sound (w := (1739 / 9739)) (n := 12)
    (lo := (180495309 / 500000000)) (hi := (360990619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5739 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5739 / 4000) = 1/(4000 / 5739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (180495309 / 500000000) (360990619 / 1000000000) (Real.log (5739 / 4000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (5739 / 4000) = -Real.log (4000 / 5739) := by
    rw [show ((5739 / 4000) : ℝ) = ((4000 / 5739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (570487167 / 1000000000) ≤ -Real.log (2261 / 4000) ∧
    -Real.log (2261 / 4000) ≤ (4456931 / 7812500) := by
  have h := checkLog_sound (w := (1739 / 6261)) (n := 12)
    (lo := (570487167 / 1000000000)) (hi := (4456931 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 2261) = 1/(2261 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4456931 / 7812500) (-570487167 / 1000000000) (Real.log (2261 / 4000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (361604473 / 1000000000) ≤ -Real.log (1000000 / 1435631) ∧
    -Real.log (1000000 / 1435631) ≤ (180802237 / 500000000) := by
  have h := checkLog_sound (w := (435631 / 2435631)) (n := 12)
    (lo := (361604473 / 1000000000)) (hi := (180802237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1435631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1435631 / 1000000) = 1/(1000000 / 1435631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (361604473 / 1000000000) (180802237 / 500000000) (Real.log (1435631 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1435631 / 1000000) = -Real.log (1000000 / 1435631) := by
    rw [show ((1435631 / 1000000) : ℝ) = ((1000000 / 1435631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (286023493 / 500000000) ≤ -Real.log (564369 / 1000000) ∧
    -Real.log (564369 / 1000000) ≤ (572046987 / 1000000000) := by
  have h := checkLog_sound (w := (435631 / 1564369)) (n := 12)
    (lo := (286023493 / 500000000)) (hi := (572046987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 564369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 564369) = 1/(564369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-572046987 / 1000000000) (-286023493 / 500000000) (Real.log (564369 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8778829 / 31250000) ≤ -Real.log (1000000 / 1324351) ∧
    -Real.log (1000000 / 1324351) ≤ (280922529 / 1000000000) := by
  have h := checkLog_sound (w := (324351 / 2324351)) (n := 12)
    (lo := (8778829 / 31250000)) (hi := (280922529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1324351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1324351 / 1000000) = 1/(1000000 / 1324351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8778829 / 31250000) (280922529 / 1000000000) (Real.log (1324351 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1324351 / 1000000) = -Real.log (1000000 / 1324351) := by
    rw [show ((1324351 / 1000000) : ℝ) = ((1000000 / 1324351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (12252549 / 31250000) ≤ -Real.log (675649 / 1000000) ∧
    -Real.log (675649 / 1000000) ≤ (392081569 / 1000000000) := by
  have h := checkLog_sound (w := (324351 / 1675649)) (n := 12)
    (lo := (12252549 / 31250000)) (hi := (392081569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 675649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 675649) = 1/(675649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-392081569 / 1000000000) (-12252549 / 31250000) (Real.log (675649 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (281473589 / 1000000000) ≤ -Real.log (1000000 / 1325081) ∧
    -Real.log (1000000 / 1325081) ≤ (28147359 / 100000000) := by
  have h := checkLog_sound (w := (325081 / 2325081)) (n := 12)
    (lo := (281473589 / 1000000000)) (hi := (28147359 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325081 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325081 / 1000000) = 1/(1000000 / 1325081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (281473589 / 1000000000) (28147359 / 100000000) (Real.log (1325081 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1325081 / 1000000) = -Real.log (1000000 / 1325081) := by
    rw [show ((1325081 / 1000000) : ℝ) = ((1000000 / 1325081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (78632519 / 200000000) ≤ -Real.log (674919 / 1000000) ∧
    -Real.log (674919 / 1000000) ≤ (98290649 / 250000000) := by
  have h := checkLog_sound (w := (325081 / 1674919)) (n := 12)
    (lo := (78632519 / 200000000)) (hi := (98290649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674919) = 1/(674919 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-98290649 / 250000000) (-78632519 / 200000000) (Real.log (674919 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (186295557 / 200000000) ≤ -Real.log (500000000000 / 1269128704113) ∧
    -Real.log (500000000000 / 1269128704113) ≤ (931477787 / 1000000000) := by
  have h := checkLog_sound (w := (269128704113 / 2269128704113)) (n := 12)
    (lo := (47666121 / 200000000)) (hi := (119165303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269128704113 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1269128704113 / 1000000000000) = 1/(500000000000 / 1269128704113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (186295557 / 200000000) (931477787 / 1000000000) (Real.log (1269128704113 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1269128704113 / 500000000000) = -Real.log (500000000000 / 1269128704113) := by
    rw [show ((1269128704113 / 500000000000) : ℝ) = ((500000000000 / 1269128704113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (933651459 / 1000000000) ≤ -Real.log (500000000000 / 1271890376687) ∧
    -Real.log (500000000000 / 1271890376687) ≤ (933651461 / 1000000000) := by
  have h := checkLog_sound (w := (271890376687 / 2271890376687)) (n := 12)
    (lo := (240504279 / 1000000000)) (hi := (6012607 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271890376687 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1271890376687 / 1000000000000) = 1/(500000000000 / 1271890376687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (933651459 / 1000000000) (933651461 / 1000000000) (Real.log (1271890376687 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1271890376687 / 500000000000) = -Real.log (500000000000 / 1271890376687) := by
    rw [show ((1271890376687 / 500000000000) : ℝ) = ((500000000000 / 1271890376687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10515689 / 15625000) ≤ -Real.log (250000000000 / 490029216353) ∧
    -Real.log (250000000000 / 490029216353) ≤ (673004097 / 1000000000) := by
  have h := checkLog_sound (w := (240029216353 / 740029216353)) (n := 12)
    (lo := (10515689 / 15625000)) (hi := (673004097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490029216353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490029216353 / 250000000000) = 1/(250000000000 / 490029216353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (10515689 / 15625000) (673004097 / 1000000000) (Real.log (490029216353 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (490029216353 / 250000000000) = -Real.log (250000000000 / 490029216353) := by
    rw [show ((490029216353 / 250000000000) : ℝ) = ((250000000000 / 490029216353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (84329523 / 125000000) ≤ -Real.log (125000000000 / 245414820149) ∧
    -Real.log (125000000000 / 245414820149) ≤ (134927237 / 200000000) := by
  have h := checkLog_sound (w := (120414820149 / 370414820149)) (n := 12)
    (lo := (84329523 / 125000000)) (hi := (134927237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245414820149 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245414820149 / 125000000000) = 1/(125000000000 / 245414820149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (84329523 / 125000000) (134927237 / 200000000) (Real.log (245414820149 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (245414820149 / 125000000000) = -Real.log (125000000000 / 245414820149) := by
    rw [show ((245414820149 / 125000000000) : ℝ) = ((125000000000 / 245414820149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0203

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0204Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0204
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

theorem reflection_log_1_neg : (13193277 / 50000000) ≤ -Real.log (2560 / 3333) ∧
    -Real.log (2560 / 3333) ≤ (263865541 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 5893)) (n := 12)
    (lo := (13193277 / 50000000)) (hi := (263865541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3333 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3333 / 2560) = 1/(2560 / 3333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13193277 / 50000000) (263865541 / 1000000000) (Real.log (3333 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3333 / 2560) = -Real.log (2560 / 3333) := by
    rw [show ((3333 / 2560) : ℝ) = ((2560 / 3333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (179734511 / 500000000) ≤ -Real.log (1787 / 2560) ∧
    -Real.log (1787 / 2560) ≤ (359469023 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 4347)) (n := 12)
    (lo := (179734511 / 500000000)) (hi := (359469023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1787) = 1/(1787 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-359469023 / 1000000000) (-179734511 / 500000000) (Real.log (1787 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (131707697 / 500000000) ≤ -Real.log (5120 / 6663) ∧
    -Real.log (5120 / 6663) ≤ (52683079 / 200000000) := by
  have h := checkLog_sound (w := (1543 / 11783)) (n := 12)
    (lo := (131707697 / 500000000)) (hi := (52683079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6663 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6663 / 5120) = 1/(5120 / 6663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (131707697 / 500000000) (52683079 / 200000000) (Real.log (6663 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6663 / 5120) = -Real.log (5120 / 6663) := by
    rw [show ((6663 / 5120) : ℝ) = ((5120 / 6663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (179314989 / 500000000) ≤ -Real.log (3577 / 5120) ∧
    -Real.log (3577 / 5120) ≤ (358629979 / 1000000000) := by
  have h := checkLog_sound (w := (1543 / 8697)) (n := 12)
    (lo := (179314989 / 500000000)) (hi := (358629979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3577) = 1/(3577 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-358629979 / 1000000000) (-179314989 / 500000000) (Real.log (3577 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23622103 / 50000000) ≤ -Real.log (1280 / 2053) ∧
    -Real.log (1280 / 2053) ≤ (472442061 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 3333)) (n := 12)
    (lo := (23622103 / 50000000)) (hi := (472442061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2053 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2053 / 1280) = 1/(1280 / 2053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23622103 / 50000000) (472442061 / 1000000000) (Real.log (2053 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2053 / 1280) = -Real.log (1280 / 2053) := by
    rw [show ((2053 / 1280) : ℝ) = ((1280 / 2053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28940761 / 31250000) ≤ -Real.log (507 / 1280) ∧
    -Real.log (507 / 1280) ≤ (463052177 / 500000000) := by
  have h := checkLog_sound (w := (133 / 1147)) (n := 12)
    (lo := (58239293 / 250000000)) (hi := (232957173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 507) = 1/(507 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-463052177 / 500000000) (-28940761 / 31250000) (Real.log (507 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (235855577 / 500000000) ≤ -Real.log (2560 / 4103) ∧
    -Real.log (2560 / 4103) ≤ (94342231 / 200000000) := by
  have h := checkLog_sound (w := (1543 / 6663)) (n := 12)
    (lo := (235855577 / 500000000)) (hi := (94342231 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4103 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4103 / 2560) = 1/(2560 / 4103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (235855577 / 500000000) (94342231 / 200000000) (Real.log (4103 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4103 / 2560) = -Real.log (2560 / 4103) := by
    rw [show ((4103 / 2560) : ℝ) = ((2560 / 4103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (46157507 / 50000000) ≤ -Real.log (1017 / 2560) ∧
    -Real.log (1017 / 2560) ≤ (461575071 / 500000000) := by
  have h := checkLog_sound (w := (263 / 2297)) (n := 12)
    (lo := (2875037 / 12500000)) (hi := (230002961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1017) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1017) = 1/(1017 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-461575071 / 500000000) (-46157507 / 50000000) (Real.log (1017 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (360377779 / 1000000000) ≤ -Real.log (1000000 / 1433871) ∧
    -Real.log (1000000 / 1433871) ≤ (18018889 / 50000000) := by
  have h := checkLog_sound (w := (433871 / 2433871)) (n := 12)
    (lo := (360377779 / 1000000000)) (hi := (18018889 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433871 / 1000000) = 1/(1000000 / 1433871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (360377779 / 1000000000) (18018889 / 50000000) (Real.log (1433871 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1433871 / 1000000) = -Real.log (1000000 / 1433871) := by
    rw [show ((1433871 / 1000000) : ℝ) = ((1000000 / 1433871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (568933311 / 1000000000) ≤ -Real.log (566129 / 1000000) ∧
    -Real.log (566129 / 1000000) ≤ (8889583 / 15625000) := by
  have h := checkLog_sound (w := (433871 / 1566129)) (n := 12)
    (lo := (568933311 / 1000000000)) (hi := (8889583 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 566129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 566129) = 1/(566129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-8889583 / 15625000) (-568933311 / 1000000000) (Real.log (566129 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180495657 / 500000000) ≤ -Real.log (1000000 / 1434751) ∧
    -Real.log (1000000 / 1434751) ≤ (72198263 / 200000000) := by
  have h := checkLog_sound (w := (434751 / 2434751)) (n := 12)
    (lo := (180495657 / 500000000)) (hi := (72198263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1434751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1434751 / 1000000) = 1/(1000000 / 1434751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180495657 / 500000000) (72198263 / 200000000) (Real.log (1434751 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1434751 / 1000000) = -Real.log (1000000 / 1434751) := by
    rw [show ((1434751 / 1000000) : ℝ) = ((1000000 / 1434751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (71311117 / 125000000) ≤ -Real.log (565249 / 1000000) ∧
    -Real.log (565249 / 1000000) ≤ (570488937 / 1000000000) := by
  have h := checkLog_sound (w := (434751 / 1565249)) (n := 12)
    (lo := (71311117 / 125000000)) (hi := (570488937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 565249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 565249) = 1/(565249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-570488937 / 1000000000) (-71311117 / 125000000) (Real.log (565249 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (280372673 / 1000000000) ≤ -Real.log (1000000 / 1323623) ∧
    -Real.log (1000000 / 1323623) ≤ (140186337 / 500000000) := by
  have h := checkLog_sound (w := (323623 / 2323623)) (n := 12)
    (lo := (280372673 / 1000000000)) (hi := (140186337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323623 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323623 / 1000000) = 1/(1000000 / 1323623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (280372673 / 1000000000) (140186337 / 500000000) (Real.log (1323623 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1323623 / 1000000) = -Real.log (1000000 / 1323623) := by
    rw [show ((1323623 / 1000000) : ℝ) = ((1000000 / 1323623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (195502333 / 500000000) ≤ -Real.log (676377 / 1000000) ∧
    -Real.log (676377 / 1000000) ≤ (391004667 / 1000000000) := by
  have h := checkLog_sound (w := (323623 / 1676377)) (n := 12)
    (lo := (195502333 / 500000000)) (hi := (391004667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 676377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 676377) = 1/(676377 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-391004667 / 1000000000) (-195502333 / 500000000) (Real.log (676377 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (280923283 / 1000000000) ≤ -Real.log (15625 / 20693) ∧
    -Real.log (15625 / 20693) ≤ (70230821 / 250000000) := by
  have h := checkLog_sound (w := (2534 / 18159)) (n := 12)
    (lo := (280923283 / 1000000000)) (hi := (70230821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20693 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20693 / 15625) = 1/(15625 / 20693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (280923283 / 1000000000) (70230821 / 250000000) (Real.log (20693 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (20693 / 15625) = -Real.log (15625 / 20693) := by
    rw [show ((20693 / 15625) : ℝ) = ((15625 / 20693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (49010381 / 125000000) ≤ -Real.log (10557 / 15625) ∧
    -Real.log (10557 / 15625) ≤ (392083049 / 1000000000) := by
  have h := checkLog_sound (w := (2534 / 13091)) (n := 12)
    (lo := (49010381 / 125000000)) (hi := (392083049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10557) = 1/(10557 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-392083049 / 1000000000) (-49010381 / 125000000) (Real.log (10557 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (92931109 / 100000000) ≤ -Real.log (50000000000 / 126638186703) ∧
    -Real.log (50000000000 / 126638186703) ≤ (232327773 / 250000000) := by
  have h := checkLog_sound (w := (26638186703 / 226638186703)) (n := 12)
    (lo := (23616391 / 100000000)) (hi := (236163911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126638186703 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126638186703 / 100000000000) = 1/(50000000000 / 126638186703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (92931109 / 100000000) (232327773 / 250000000) (Real.log (126638186703 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (126638186703 / 50000000000) = -Real.log (50000000000 / 126638186703) := by
    rw [show ((126638186703 / 50000000000) : ℝ) = ((50000000000 / 126638186703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (931480251 / 1000000000) ≤ -Real.log (31250000000 / 79320739621) ∧
    -Real.log (31250000000 / 79320739621) ≤ (931480253 / 1000000000) := by
  have h := checkLog_sound (w := (16820739621 / 141820739621)) (n := 12)
    (lo := (238333071 / 1000000000)) (hi := (14895817 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79320739621 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(79320739621 / 62500000000) = 1/(31250000000 / 79320739621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (931480251 / 1000000000) (931480253 / 1000000000) (Real.log (79320739621 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (79320739621 / 31250000000) = -Real.log (31250000000 / 79320739621) := by
    rw [show ((79320739621 / 31250000000) : ℝ) = ((31250000000 / 79320739621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (671377339 / 1000000000) ≤ -Real.log (12500000000 / 24461635301) ∧
    -Real.log (12500000000 / 24461635301) ≤ (33568867 / 50000000) := by
  have h := checkLog_sound (w := (11961635301 / 36961635301)) (n := 12)
    (lo := (671377339 / 1000000000)) (hi := (33568867 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24461635301 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24461635301 / 12500000000) = 1/(12500000000 / 24461635301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (671377339 / 1000000000) (33568867 / 50000000) (Real.log (24461635301 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (24461635301 / 12500000000) = -Real.log (12500000000 / 24461635301) := by
    rw [show ((24461635301 / 12500000000) : ℝ) = ((12500000000 / 24461635301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (673006331 / 1000000000) ≤ -Real.log (125000000000 / 245015155821) ∧
    -Real.log (125000000000 / 245015155821) ≤ (168251583 / 250000000) := by
  have h := checkLog_sound (w := (120015155821 / 370015155821)) (n := 12)
    (lo := (673006331 / 1000000000)) (hi := (168251583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245015155821 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245015155821 / 125000000000) = 1/(125000000000 / 245015155821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (673006331 / 1000000000) (168251583 / 250000000) (Real.log (245015155821 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (245015155821 / 125000000000) = -Real.log (125000000000 / 245015155821) := by
    rw [show ((245015155821 / 125000000000) : ℝ) = ((125000000000 / 245015155821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0204

end


