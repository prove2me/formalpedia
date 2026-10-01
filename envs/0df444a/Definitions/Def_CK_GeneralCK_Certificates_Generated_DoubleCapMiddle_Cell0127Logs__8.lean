-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0127Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0127Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:12:12.753674+00:00
-- url     : https://prove2.me/theorems/4c056280-35ed-4d4b-ac7e-a621b17ef598
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0127Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0128Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0127Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0128Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0129Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0130Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0131Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0132Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0133Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0134Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0127Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0128Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0129Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0130Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0131Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0132Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0133Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0134Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0127Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0128Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0129Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0130Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0131Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0132Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0133Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0134Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0127Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0128Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0129Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0130Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0131Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0132Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0133Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0134Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0127Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0127
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

theorem reflection_log_1_neg : (310467379 / 1000000000) ≤ -Real.log (640 / 873) ∧
    -Real.log (640 / 873) ≤ (15523369 / 50000000) := by
  have h := checkLog_sound (w := (233 / 1513)) (n := 12)
    (lo := (310467379 / 1000000000)) (hi := (15523369 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873 / 640) = 1/(640 / 873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (310467379 / 1000000000) (15523369 / 50000000) (Real.log (873 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (873 / 640) = -Real.log (640 / 873) := by
    rw [show ((873 / 640) : ℝ) = ((640 / 873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (45265499 / 100000000) ≤ -Real.log (407 / 640) ∧
    -Real.log (407 / 640) ≤ (452654991 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 1047)) (n := 12)
    (lo := (45265499 / 100000000)) (hi := (452654991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 407) = 1/(407 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-452654991 / 1000000000) (-45265499 / 100000000) (Real.log (407 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (309607903 / 1000000000) ≤ -Real.log (2560 / 3489) ∧
    -Real.log (2560 / 3489) ≤ (9675247 / 31250000) := by
  have h := checkLog_sound (w := (929 / 6049)) (n := 12)
    (lo := (309607903 / 1000000000)) (hi := (9675247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3489 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3489 / 2560) = 1/(2560 / 3489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (309607903 / 1000000000) (9675247 / 31250000) (Real.log (3489 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3489 / 2560) = -Real.log (2560 / 3489) := by
    rw [show ((3489 / 2560) : ℝ) = ((2560 / 3489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (225406967 / 500000000) ≤ -Real.log (1631 / 2560) ∧
    -Real.log (1631 / 2560) ≤ (90162787 / 200000000) := by
  have h := checkLog_sound (w := (929 / 4191)) (n := 12)
    (lo := (225406967 / 500000000)) (hi := (90162787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1631) = 1/(1631 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-90162787 / 200000000) (-225406967 / 500000000) (Real.log (1631 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (109407401 / 200000000) ≤ -Real.log (320 / 553) ∧
    -Real.log (320 / 553) ≤ (273518503 / 500000000) := by
  have h := checkLog_sound (w := (233 / 873)) (n := 12)
    (lo := (109407401 / 200000000)) (hi := (273518503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((553 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(553 / 320) = 1/(320 / 553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (109407401 / 200000000) (273518503 / 500000000) (Real.log (553 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (553 / 320) = -Real.log (320 / 553) := by
    rw [show ((553 / 320) : ℝ) = ((320 / 553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (325603219 / 250000000) ≤ -Real.log (87 / 320) ∧
    -Real.log (87 / 320) ≤ (651206439 / 500000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 87) = 1/(87 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-651206439 / 500000000) (-325603219 / 250000000) (Real.log (87 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (272839923 / 500000000) ≤ -Real.log (1280 / 2209) ∧
    -Real.log (1280 / 2209) ≤ (545679847 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 3489)) (n := 12)
    (lo := (272839923 / 500000000)) (hi := (545679847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2209 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2209 / 1280) = 1/(1280 / 2209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (272839923 / 500000000) (545679847 / 1000000000) (Real.log (2209 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2209 / 1280) = -Real.log (1280 / 2209) := by
    rw [show ((2209 / 1280) : ℝ) = ((1280 / 2209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (323457283 / 250000000) ≤ -Real.log (351 / 1280) ∧
    -Real.log (351 / 1280) ≤ (646914567 / 500000000) := by
  have h := checkLog_sound (w := (289 / 991)) (n := 12)
    (lo := (18771311 / 31250000)) (hi := (600681953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 351) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 351) = 1/(351 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-646914567 / 500000000) (-323457283 / 250000000) (Real.log (351 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42397147 / 100000000) ≤ -Real.log (500000 / 764009) ∧
    -Real.log (500000 / 764009) ≤ (423971471 / 1000000000) := by
  have h := checkLog_sound (w := (264009 / 1264009)) (n := 12)
    (lo := (42397147 / 100000000)) (hi := (423971471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764009 / 500000) = 1/(500000 / 764009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42397147 / 100000000) (423971471 / 1000000000) (Real.log (764009 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (764009 / 500000) = -Real.log (500000 / 764009) := by
    rw [show ((764009 / 500000) : ℝ) = ((500000 / 764009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (750814429 / 1000000000) ≤ -Real.log (235991 / 500000) ∧
    -Real.log (235991 / 500000) ≤ (750814431 / 1000000000) := by
  have h := checkLog_sound (w := (14009 / 485991)) (n := 12)
    (lo := (57667249 / 1000000000)) (hi := (230669 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 235991) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 235991) = 1/(235991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-750814431 / 1000000000) (-750814429 / 1000000000) (Real.log (235991 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (425172959 / 1000000000) ≤ -Real.log (200000 / 305971) ∧
    -Real.log (200000 / 305971) ≤ (2657331 / 6250000) := by
  have h := checkLog_sound (w := (105971 / 505971)) (n := 12)
    (lo := (425172959 / 1000000000)) (hi := (2657331 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305971 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305971 / 200000) = 1/(200000 / 305971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (425172959 / 1000000000) (2657331 / 6250000) (Real.log (305971 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (305971 / 200000) = -Real.log (200000 / 305971) := by
    rw [show ((305971 / 200000) : ℝ) = ((200000 / 305971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18867853 / 25000000) ≤ -Real.log (94029 / 200000) ∧
    -Real.log (94029 / 200000) ≤ (377357061 / 500000000) := by
  have h := checkLog_sound (w := (5971 / 194029)) (n := 12)
    (lo := (3078347 / 50000000)) (hi := (61566941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 94029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 94029) = 1/(94029 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-377357061 / 500000000) (-18867853 / 25000000) (Real.log (94029 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (33963651 / 100000000) ≤ -Real.log (1000000 / 1404437) ∧
    -Real.log (1000000 / 1404437) ≤ (339636511 / 1000000000) := by
  have h := checkLog_sound (w := (404437 / 2404437)) (n := 12)
    (lo := (33963651 / 100000000)) (hi := (339636511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1404437 / 1000000) = 1/(1000000 / 1404437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (33963651 / 100000000) (339636511 / 1000000000) (Real.log (1404437 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1404437 / 1000000) = -Real.log (1000000 / 1404437) := by
    rw [show ((1404437 / 1000000) : ℝ) = ((1000000 / 1404437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (259124051 / 500000000) ≤ -Real.log (595563 / 1000000) ∧
    -Real.log (595563 / 1000000) ≤ (518248103 / 1000000000) := by
  have h := checkLog_sound (w := (404437 / 1595563)) (n := 12)
    (lo := (259124051 / 500000000)) (hi := (518248103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 595563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 595563) = 1/(595563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-518248103 / 1000000000) (-259124051 / 500000000) (Real.log (595563 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85201067 / 250000000) ≤ -Real.log (500000 / 703039) ∧
    -Real.log (500000 / 703039) ≤ (340804269 / 1000000000) := by
  have h := checkLog_sound (w := (203039 / 1203039)) (n := 12)
    (lo := (85201067 / 250000000)) (hi := (340804269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703039 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703039 / 500000) = 1/(500000 / 703039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85201067 / 250000000) (340804269 / 1000000000) (Real.log (703039 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (703039 / 500000) = -Real.log (500000 / 703039) := by
    rw [show ((703039 / 500000) : ℝ) = ((500000 / 703039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (521007281 / 1000000000) ≤ -Real.log (296961 / 500000) ∧
    -Real.log (296961 / 500000) ≤ (260503641 / 500000000) := by
  have h := checkLog_sound (w := (203039 / 796961)) (n := 12)
    (lo := (521007281 / 1000000000)) (hi := (260503641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 296961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 296961) = 1/(296961 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-260503641 / 500000000) (-521007281 / 1000000000) (Real.log (296961 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1174785899 / 1000000000) ≤ -Real.log (250000000000 / 809362433313) ∧
    -Real.log (250000000000 / 809362433313) ≤ (1174785901 / 1000000000) := by
  have h := checkLog_sound (w := (309362433313 / 1309362433313)) (n := 12)
    (lo := (481638719 / 1000000000)) (hi := (1505121 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809362433313 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(809362433313 / 500000000000) = 1/(250000000000 / 809362433313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1174785899 / 1000000000) (1174785901 / 1000000000) (Real.log (809362433313 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (809362433313 / 250000000000) = -Real.log (250000000000 / 809362433313) := by
    rw [show ((809362433313 / 250000000000) : ℝ) = ((250000000000 / 809362433313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (29497177 / 25000000) ≤ -Real.log (500000000000 / 1627003371301) ∧
    -Real.log (500000000000 / 1627003371301) ≤ (589943541 / 500000000) := by
  have h := checkLog_sound (w := (627003371301 / 2627003371301)) (n := 12)
    (lo := (4867399 / 10000000)) (hi := (486739901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1627003371301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1627003371301 / 1000000000000) = 1/(500000000000 / 1627003371301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (29497177 / 25000000) (589943541 / 500000000) (Real.log (1627003371301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1627003371301 / 500000000000) = -Real.log (500000000000 / 1627003371301) := by
    rw [show ((1627003371301 / 500000000000) : ℝ) = ((500000000000 / 1627003371301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (214471153 / 250000000) ≤ -Real.log (125000000000 / 294770872267) ∧
    -Real.log (125000000000 / 294770872267) ≤ (428942307 / 500000000) := by
  have h := checkLog_sound (w := (44770872267 / 544770872267)) (n := 12)
    (lo := (20592179 / 125000000)) (hi := (164737433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294770872267 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(294770872267 / 250000000000) = 1/(125000000000 / 294770872267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (214471153 / 250000000) (428942307 / 500000000) (Real.log (294770872267 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (294770872267 / 125000000000) = -Real.log (125000000000 / 294770872267) := by
    rw [show ((294770872267 / 125000000000) : ℝ) = ((125000000000 / 294770872267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (861811549 / 1000000000) ≤ -Real.log (125000000000 / 295930694603) ∧
    -Real.log (125000000000 / 295930694603) ≤ (861811551 / 1000000000) := by
  have h := checkLog_sound (w := (45930694603 / 545930694603)) (n := 12)
    (lo := (168664369 / 1000000000)) (hi := (16866437 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295930694603 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(295930694603 / 250000000000) = 1/(125000000000 / 295930694603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (861811549 / 1000000000) (861811551 / 1000000000) (Real.log (295930694603 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (295930694603 / 125000000000) = -Real.log (125000000000 / 295930694603) := by
    rw [show ((295930694603 / 125000000000) : ℝ) = ((125000000000 / 295930694603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0127

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0128Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0128
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

theorem reflection_log_1_neg : (309607903 / 1000000000) ≤ -Real.log (2560 / 3489) ∧
    -Real.log (2560 / 3489) ≤ (9675247 / 31250000) := by
  have h := checkLog_sound (w := (929 / 6049)) (n := 12)
    (lo := (309607903 / 1000000000)) (hi := (9675247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3489 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3489 / 2560) = 1/(2560 / 3489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (309607903 / 1000000000) (9675247 / 31250000) (Real.log (3489 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3489 / 2560) = -Real.log (2560 / 3489) := by
    rw [show ((3489 / 2560) : ℝ) = ((2560 / 3489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (225406967 / 500000000) ≤ -Real.log (1631 / 2560) ∧
    -Real.log (1631 / 2560) ≤ (90162787 / 200000000) := by
  have h := checkLog_sound (w := (929 / 4191)) (n := 12)
    (lo := (225406967 / 500000000)) (hi := (90162787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1631) = 1/(1631 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-90162787 / 200000000) (-225406967 / 500000000) (Real.log (1631 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (38593461 / 125000000) ≤ -Real.log (1280 / 1743) ∧
    -Real.log (1280 / 1743) ≤ (308747689 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 3023)) (n := 12)
    (lo := (38593461 / 125000000)) (hi := (308747689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1743 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1743 / 1280) = 1/(1280 / 1743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (38593461 / 125000000) (308747689 / 1000000000) (Real.log (1743 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1743 / 1280) = -Real.log (1280 / 1743) := by
    rw [show ((1743 / 1280) : ℝ) = ((1280 / 1743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224488131 / 500000000) ≤ -Real.log (817 / 1280) ∧
    -Real.log (817 / 1280) ≤ (448976263 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2097)) (n := 12)
    (lo := (224488131 / 500000000)) (hi := (448976263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 817) = 1/(817 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-448976263 / 1000000000) (-224488131 / 500000000) (Real.log (817 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (272839923 / 500000000) ≤ -Real.log (1280 / 2209) ∧
    -Real.log (1280 / 2209) ≤ (545679847 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 3489)) (n := 12)
    (lo := (272839923 / 500000000)) (hi := (545679847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2209 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2209 / 1280) = 1/(1280 / 2209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (272839923 / 500000000) (545679847 / 1000000000) (Real.log (2209 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2209 / 1280) = -Real.log (1280 / 2209) := by
    rw [show ((2209 / 1280) : ℝ) = ((1280 / 2209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (323457283 / 250000000) ≤ -Real.log (351 / 1280) ∧
    -Real.log (351 / 1280) ≤ (646914567 / 500000000) := by
  have h := checkLog_sound (w := (289 / 991)) (n := 12)
    (lo := (18771311 / 31250000)) (hi := (600681953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 351) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 351) = 1/(351 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-646914567 / 500000000) (-323457283 / 250000000) (Real.log (351 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (272160421 / 500000000) ≤ -Real.log (640 / 1103) ∧
    -Real.log (640 / 1103) ≤ (544320843 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 1743)) (n := 12)
    (lo := (272160421 / 500000000)) (hi := (544320843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103 / 640) = 1/(640 / 1103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (272160421 / 500000000) (544320843 / 1000000000) (Real.log (1103 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1103 / 640) = -Real.log (640 / 1103) := by
    rw [show ((1103 / 640) : ℝ) = ((640 / 1103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1285318443 / 1000000000) ≤ -Real.log (177 / 640) ∧
    -Real.log (177 / 640) ≤ (257063689 / 200000000) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 177) = 1/(177 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-257063689 / 200000000) (-1285318443 / 1000000000) (Real.log (177 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (211385251 / 500000000) ≤ -Real.log (125000 / 190773) ∧
    -Real.log (125000 / 190773) ≤ (422770503 / 1000000000) := by
  have h := checkLog_sound (w := (65773 / 315773)) (n := 12)
    (lo := (211385251 / 500000000)) (hi := (422770503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190773 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190773 / 125000) = 1/(125000 / 190773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (211385251 / 500000000) (422770503 / 1000000000) (Real.log (190773 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (190773 / 125000) = -Real.log (125000 / 190773) := by
    rw [show ((190773 / 125000) : ℝ) = ((125000 / 190773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (746936217 / 1000000000) ≤ -Real.log (59227 / 125000) ∧
    -Real.log (59227 / 125000) ≤ (746936219 / 1000000000) := by
  have h := checkLog_sound (w := (3273 / 121727)) (n := 12)
    (lo := (53789037 / 1000000000)) (hi := (26894519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 59227) = 1/(59227 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-746936219 / 1000000000) (-746936217 / 1000000000) (Real.log (59227 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3391777 / 8000000) ≤ -Real.log (1000000 / 1528019) ∧
    -Real.log (1000000 / 1528019) ≤ (211986063 / 500000000) := by
  have h := checkLog_sound (w := (528019 / 2528019)) (n := 12)
    (lo := (3391777 / 8000000)) (hi := (211986063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1528019 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1528019 / 1000000) = 1/(1000000 / 1528019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3391777 / 8000000) (211986063 / 500000000) (Real.log (1528019 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1528019 / 1000000) = -Real.log (1000000 / 1528019) := by
    rw [show ((1528019 / 1000000) : ℝ) = ((1000000 / 1528019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (750816547 / 1000000000) ≤ -Real.log (471981 / 1000000) ∧
    -Real.log (471981 / 1000000) ≤ (750816549 / 1000000000) := by
  have h := checkLog_sound (w := (28019 / 971981)) (n := 12)
    (lo := (57669367 / 1000000000)) (hi := (7208671 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 471981) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 471981) = 1/(471981 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-750816549 / 1000000000) (-750816547 / 1000000000) (Real.log (471981 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67694333 / 200000000) ≤ -Real.log (500000 / 701401) ∧
    -Real.log (500000 / 701401) ≤ (169235833 / 500000000) := by
  have h := checkLog_sound (w := (201401 / 1201401)) (n := 12)
    (lo := (67694333 / 200000000)) (hi := (169235833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701401 / 500000) = 1/(500000 / 701401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67694333 / 200000000) (169235833 / 500000000) (Real.log (701401 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (701401 / 500000) = -Real.log (500000 / 701401) := by
    rw [show ((701401 / 500000) : ℝ) = ((500000 / 701401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (257753281 / 500000000) ≤ -Real.log (298599 / 500000) ∧
    -Real.log (298599 / 500000) ≤ (515506563 / 1000000000) := by
  have h := checkLog_sound (w := (201401 / 798599)) (n := 12)
    (lo := (257753281 / 500000000)) (hi := (515506563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 298599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 298599) = 1/(298599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-515506563 / 1000000000) (-257753281 / 500000000) (Real.log (298599 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (169818611 / 500000000) ≤ -Real.log (500000 / 702219) ∧
    -Real.log (500000 / 702219) ≤ (339637223 / 1000000000) := by
  have h := checkLog_sound (w := (202219 / 1202219)) (n := 12)
    (lo := (169818611 / 500000000)) (hi := (339637223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702219 / 500000) = 1/(500000 / 702219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (169818611 / 500000000) (339637223 / 1000000000) (Real.log (702219 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (702219 / 500000) = -Real.log (500000 / 702219) := by
    rw [show ((702219 / 500000) : ℝ) = ((500000 / 702219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (518249781 / 1000000000) ≤ -Real.log (297781 / 500000) ∧
    -Real.log (297781 / 500000) ≤ (259124891 / 500000000) := by
  have h := checkLog_sound (w := (202219 / 797781)) (n := 12)
    (lo := (518249781 / 1000000000)) (hi := (259124891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 297781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 297781) = 1/(297781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-259124891 / 500000000) (-518249781 / 1000000000) (Real.log (297781 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (7310667 / 6250000) ≤ -Real.log (500000000000 / 1610523916457) ∧
    -Real.log (500000000000 / 1610523916457) ≤ (584853361 / 500000000) := by
  have h := checkLog_sound (w := (610523916457 / 2610523916457)) (n := 12)
    (lo := (23827977 / 50000000)) (hi := (476559541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1610523916457 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1610523916457 / 1000000000000) = 1/(500000000000 / 1610523916457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (7310667 / 6250000) (584853361 / 500000000) (Real.log (1610523916457 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1610523916457 / 500000000000) = -Real.log (500000000000 / 1610523916457) := by
    rw [show ((1610523916457 / 500000000000) : ℝ) = ((500000000000 / 1610523916457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1174788673 / 1000000000) ≤ -Real.log (500000000000 / 1618729355631) ∧
    -Real.log (500000000000 / 1618729355631) ≤ (46991547 / 40000000) := by
  have h := checkLog_sound (w := (618729355631 / 2618729355631)) (n := 12)
    (lo := (481641493 / 1000000000)) (hi := (240820747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1618729355631 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1618729355631 / 1000000000000) = 1/(500000000000 / 1618729355631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1174788673 / 1000000000) (46991547 / 40000000) (Real.log (1618729355631 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1618729355631 / 500000000000) = -Real.log (500000000000 / 1618729355631) := by
    rw [show ((1618729355631 / 500000000000) : ℝ) = ((500000000000 / 1618729355631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (426989113 / 500000000) ≤ -Real.log (500000000000 / 1174486518709) ∧
    -Real.log (500000000000 / 1174486518709) ≤ (213494557 / 250000000) := by
  have h := checkLog_sound (w := (174486518709 / 2174486518709)) (n := 12)
    (lo := (80415523 / 500000000)) (hi := (160831047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174486518709 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1174486518709 / 1000000000000) = 1/(500000000000 / 1174486518709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (426989113 / 500000000) (213494557 / 250000000) (Real.log (1174486518709 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1174486518709 / 500000000000) = -Real.log (500000000000 / 1174486518709) := by
    rw [show ((1174486518709 / 500000000000) : ℝ) = ((500000000000 / 1174486518709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (857887003 / 1000000000) ≤ -Real.log (100000000000 / 235817261679) ∧
    -Real.log (100000000000 / 235817261679) ≤ (171577401 / 200000000) := by
  have h := checkLog_sound (w := (35817261679 / 435817261679)) (n := 12)
    (lo := (164739823 / 1000000000)) (hi := (10296239 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235817261679 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(235817261679 / 200000000000) = 1/(100000000000 / 235817261679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (857887003 / 1000000000) (171577401 / 200000000) (Real.log (235817261679 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (235817261679 / 100000000000) = -Real.log (100000000000 / 235817261679) := by
    rw [show ((235817261679 / 100000000000) : ℝ) = ((100000000000 / 235817261679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0128

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0129Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0129
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

theorem reflection_log_1_neg : (38593461 / 125000000) ≤ -Real.log (1280 / 1743) ∧
    -Real.log (1280 / 1743) ≤ (308747689 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 3023)) (n := 12)
    (lo := (38593461 / 125000000)) (hi := (308747689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1743 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1743 / 1280) = 1/(1280 / 1743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (38593461 / 125000000) (308747689 / 1000000000) (Real.log (1743 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1743 / 1280) = -Real.log (1280 / 1743) := by
    rw [show ((1743 / 1280) : ℝ) = ((1280 / 1743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224488131 / 500000000) ≤ -Real.log (817 / 1280) ∧
    -Real.log (817 / 1280) ≤ (448976263 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2097)) (n := 12)
    (lo := (224488131 / 500000000)) (hi := (448976263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 817) = 1/(817 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-448976263 / 1000000000) (-224488131 / 500000000) (Real.log (817 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (76971683 / 250000000) ≤ -Real.log (2560 / 3483) ∧
    -Real.log (2560 / 3483) ≤ (307886733 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 6043)) (n := 12)
    (lo := (76971683 / 250000000)) (hi := (307886733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3483 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3483 / 2560) = 1/(2560 / 3483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (76971683 / 250000000) (307886733 / 1000000000) (Real.log (3483 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3483 / 2560) = -Real.log (2560 / 3483) := by
    rw [show ((3483 / 2560) : ℝ) = ((2560 / 3483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (11178549 / 25000000) ≤ -Real.log (1637 / 2560) ∧
    -Real.log (1637 / 2560) ≤ (447141961 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 4197)) (n := 12)
    (lo := (11178549 / 25000000)) (hi := (447141961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1637) = 1/(1637 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-447141961 / 1000000000) (-11178549 / 25000000) (Real.log (1637 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (272160421 / 500000000) ≤ -Real.log (640 / 1103) ∧
    -Real.log (640 / 1103) ≤ (544320843 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 1743)) (n := 12)
    (lo := (272160421 / 500000000)) (hi := (544320843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103 / 640) = 1/(640 / 1103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (272160421 / 500000000) (544320843 / 1000000000) (Real.log (1103 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1103 / 640) = -Real.log (640 / 1103) := by
    rw [show ((1103 / 640) : ℝ) = ((640 / 1103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1285318443 / 1000000000) ≤ -Real.log (177 / 640) ∧
    -Real.log (177 / 640) ≤ (257063689 / 200000000) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 177) = 1/(177 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-257063689 / 200000000) (-1285318443 / 1000000000) (Real.log (177 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (542959989 / 1000000000) ≤ -Real.log (1280 / 2203) ∧
    -Real.log (1280 / 2203) ≤ (54295999 / 100000000) := by
  have h := checkLog_sound (w := (923 / 3483)) (n := 12)
    (lo := (542959989 / 1000000000)) (hi := (54295999 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2203 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2203 / 1280) = 1/(1280 / 2203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (542959989 / 1000000000) (54295999 / 100000000) (Real.log (2203 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2203 / 1280) = -Real.log (1280 / 2203) := by
    rw [show ((2203 / 1280) : ℝ) = ((1280 / 2203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (638439787 / 500000000) ≤ -Real.log (357 / 1280) ∧
    -Real.log (357 / 1280) ≤ (159609947 / 125000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 357) = 1/(357 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159609947 / 125000000) (-638439787 / 500000000) (Real.log (357 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (421569401 / 1000000000) ≤ -Real.log (15625 / 23818) ∧
    -Real.log (15625 / 23818) ≤ (210784701 / 500000000) := by
  have h := checkLog_sound (w := (8193 / 39443)) (n := 12)
    (lo := (421569401 / 1000000000)) (hi := (210784701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23818 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23818 / 15625) = 1/(15625 / 23818) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (421569401 / 1000000000) (210784701 / 500000000) (Real.log (23818 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (23818 / 15625) = -Real.log (15625 / 23818) := by
    rw [show ((23818 / 15625) : ℝ) = ((15625 / 23818) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (743077193 / 1000000000) ≤ -Real.log (7432 / 15625) ∧
    -Real.log (7432 / 15625) ≤ (148615439 / 200000000) := by
  have h := checkLog_sound (w := (761 / 30489)) (n := 12)
    (lo := (49930013 / 1000000000)) (hi := (24965007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14864) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 14864) = 1/(7432 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-148615439 / 200000000) (-743077193 / 1000000000) (Real.log (7432 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (422771157 / 1000000000) ≤ -Real.log (200000 / 305237) ∧
    -Real.log (200000 / 305237) ≤ (211385579 / 500000000) := by
  have h := checkLog_sound (w := (105237 / 505237)) (n := 12)
    (lo := (422771157 / 1000000000)) (hi := (211385579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305237 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305237 / 200000) = 1/(200000 / 305237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (422771157 / 1000000000) (211385579 / 500000000) (Real.log (305237 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (305237 / 200000) = -Real.log (200000 / 305237) := by
    rw [show ((305237 / 200000) : ℝ) = ((200000 / 305237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93367291 / 125000000) ≤ -Real.log (94763 / 200000) ∧
    -Real.log (94763 / 200000) ≤ (74693833 / 100000000) := by
  have h := checkLog_sound (w := (5237 / 194763)) (n := 12)
    (lo := (13447787 / 250000000)) (hi := (53791149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 94763) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 94763) = 1/(94763 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-74693833 / 100000000) (-93367291 / 125000000) (Real.log (94763 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67461663 / 200000000) ≤ -Real.log (1000000 / 1401171) ∧
    -Real.log (1000000 / 1401171) ≤ (84327079 / 250000000) := by
  have h := checkLog_sound (w := (401171 / 2401171)) (n := 12)
    (lo := (67461663 / 200000000)) (hi := (84327079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1401171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1401171 / 1000000) = 1/(1000000 / 1401171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67461663 / 200000000) (84327079 / 250000000) (Real.log (1401171 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1401171 / 1000000) = -Real.log (1000000 / 1401171) := by
    rw [show ((1401171 / 1000000) : ℝ) = ((1000000 / 1401171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (512779197 / 1000000000) ≤ -Real.log (598829 / 1000000) ∧
    -Real.log (598829 / 1000000) ≤ (256389599 / 500000000) := by
  have h := checkLog_sound (w := (401171 / 1598829)) (n := 12)
    (lo := (512779197 / 1000000000)) (hi := (256389599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 598829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 598829) = 1/(598829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-256389599 / 500000000) (-512779197 / 1000000000) (Real.log (598829 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338472377 / 1000000000) ≤ -Real.log (1000000 / 1402803) ∧
    -Real.log (1000000 / 1402803) ≤ (169236189 / 500000000) := by
  have h := checkLog_sound (w := (402803 / 2402803)) (n := 12)
    (lo := (338472377 / 1000000000)) (hi := (169236189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1402803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1402803 / 1000000) = 1/(1000000 / 1402803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338472377 / 1000000000) (169236189 / 500000000) (Real.log (1402803 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1402803 / 1000000) = -Real.log (1000000 / 1402803) := by
    rw [show ((1402803 / 1000000) : ℝ) = ((1000000 / 1402803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (128877059 / 250000000) ≤ -Real.log (597197 / 1000000) ∧
    -Real.log (597197 / 1000000) ≤ (515508237 / 1000000000) := by
  have h := checkLog_sound (w := (402803 / 1597197)) (n := 12)
    (lo := (128877059 / 250000000)) (hi := (515508237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 597197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 597197) = 1/(597197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-515508237 / 1000000000) (-128877059 / 250000000) (Real.log (597197 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (232929319 / 200000000) ≤ -Real.log (500000000000 / 1602395048439) ∧
    -Real.log (500000000000 / 1602395048439) ≤ (1164646597 / 1000000000) := by
  have h := checkLog_sound (w := (602395048439 / 2602395048439)) (n := 12)
    (lo := (94299883 / 200000000)) (hi := (58937427 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1602395048439 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1602395048439 / 1000000000000) = 1/(500000000000 / 1602395048439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (232929319 / 200000000) (1164646597 / 1000000000) (Real.log (1602395048439 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1602395048439 / 500000000000) = -Real.log (500000000000 / 1602395048439) := by
    rw [show ((1602395048439 / 500000000000) : ℝ) = ((500000000000 / 1602395048439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (233941897 / 200000000) ≤ -Real.log (250000000000 / 805264185389) ∧
    -Real.log (250000000000 / 805264185389) ≤ (1169709487 / 1000000000) := by
  have h := checkLog_sound (w := (305264185389 / 1305264185389)) (n := 12)
    (lo := (95312461 / 200000000)) (hi := (238281153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805264185389 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(805264185389 / 500000000000) = 1/(250000000000 / 805264185389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (233941897 / 200000000) (1169709487 / 1000000000) (Real.log (805264185389 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (805264185389 / 250000000000) = -Real.log (250000000000 / 805264185389) := by
    rw [show ((805264185389 / 250000000000) : ℝ) = ((250000000000 / 805264185389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (106260939 / 125000000) ≤ -Real.log (125000000000 / 292481451299) ∧
    -Real.log (125000000000 / 292481451299) ≤ (425043757 / 500000000) := by
  have h := checkLog_sound (w := (42481451299 / 542481451299)) (n := 12)
    (lo := (39235083 / 250000000)) (hi := (156940333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292481451299 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(292481451299 / 250000000000) = 1/(125000000000 / 292481451299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (106260939 / 125000000) (425043757 / 500000000) (Real.log (292481451299 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (292481451299 / 125000000000) = -Real.log (125000000000 / 292481451299) := by
    rw [show ((292481451299 / 125000000000) : ℝ) = ((125000000000 / 292481451299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (426990307 / 500000000) ≤ -Real.log (500000000000 / 1174489322619) ∧
    -Real.log (500000000000 / 1174489322619) ≤ (106747577 / 125000000) := by
  have h := checkLog_sound (w := (174489322619 / 2174489322619)) (n := 12)
    (lo := (80416717 / 500000000)) (hi := (32166687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174489322619 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1174489322619 / 1000000000000) = 1/(500000000000 / 1174489322619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (426990307 / 500000000) (106747577 / 125000000) (Real.log (1174489322619 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1174489322619 / 500000000000) = -Real.log (500000000000 / 1174489322619) := by
    rw [show ((1174489322619 / 500000000000) : ℝ) = ((500000000000 / 1174489322619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0129

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0130Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0130
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

theorem reflection_log_1_neg : (76971683 / 250000000) ≤ -Real.log (2560 / 3483) ∧
    -Real.log (2560 / 3483) ≤ (307886733 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 6043)) (n := 12)
    (lo := (76971683 / 250000000)) (hi := (307886733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3483 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3483 / 2560) = 1/(2560 / 3483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (76971683 / 250000000) (307886733 / 1000000000) (Real.log (3483 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3483 / 2560) = -Real.log (2560 / 3483) := by
    rw [show ((3483 / 2560) : ℝ) = ((2560 / 3483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (11178549 / 25000000) ≤ -Real.log (1637 / 2560) ∧
    -Real.log (1637 / 2560) ≤ (447141961 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 4197)) (n := 12)
    (lo := (11178549 / 25000000)) (hi := (447141961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1637) = 1/(1637 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-447141961 / 1000000000) (-11178549 / 25000000) (Real.log (1637 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (61405007 / 200000000) ≤ -Real.log (64 / 87) ∧
    -Real.log (64 / 87) ≤ (76756259 / 250000000) := by
  have h := checkLog_sound (w := (23 / 151)) (n := 12)
    (lo := (61405007 / 200000000)) (hi := (76756259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87 / 64) = 1/(64 / 87) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (61405007 / 200000000) (76756259 / 250000000) (Real.log (87 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (87 / 64) = -Real.log (64 / 87) := by
    rw [show ((87 / 64) : ℝ) = ((64 / 87) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (55663877 / 125000000) ≤ -Real.log (41 / 64) ∧
    -Real.log (41 / 64) ≤ (445311017 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 41) = 1/(41 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-445311017 / 1000000000) (-55663877 / 125000000) (Real.log (41 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (542959989 / 1000000000) ≤ -Real.log (1280 / 2203) ∧
    -Real.log (1280 / 2203) ≤ (54295999 / 100000000) := by
  have h := checkLog_sound (w := (923 / 3483)) (n := 12)
    (lo := (542959989 / 1000000000)) (hi := (54295999 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2203 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2203 / 1280) = 1/(1280 / 2203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (542959989 / 1000000000) (54295999 / 100000000) (Real.log (2203 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2203 / 1280) = -Real.log (1280 / 2203) := by
    rw [show ((2203 / 1280) : ℝ) = ((1280 / 2203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (638439787 / 500000000) ≤ -Real.log (357 / 1280) ∧
    -Real.log (357 / 1280) ≤ (159609947 / 125000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 357) = 1/(357 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159609947 / 125000000) (-638439787 / 500000000) (Real.log (357 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (270798641 / 500000000) ≤ -Real.log (32 / 55) ∧
    -Real.log (32 / 55) ≤ (541597283 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 87)) (n := 12)
    (lo := (270798641 / 500000000)) (hi := (541597283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55 / 32) = 1/(32 / 55) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (270798641 / 500000000) (541597283 / 1000000000) (Real.log (55 / 32)) := by
  have h := reflection_log_7_neg
  have he : Real.log (55 / 32) = -Real.log (32 / 55) := by
    rw [show ((55 / 32) : ℝ) = ((32 / 55) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (317127831 / 250000000) ≤ -Real.log (9 / 32) ∧
    -Real.log (9 / 32) ≤ (634255663 / 500000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 9) = 1/(9 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-634255663 / 500000000) (-317127831 / 250000000) (Real.log (9 / 32)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42036817 / 100000000) ≤ -Real.log (500000 / 761261) ∧
    -Real.log (500000 / 761261) ≤ (420368171 / 1000000000) := by
  have h := checkLog_sound (w := (261261 / 1261261)) (n := 12)
    (lo := (42036817 / 100000000)) (hi := (420368171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761261 / 500000) = 1/(500000 / 761261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42036817 / 100000000) (420368171 / 1000000000) (Real.log (761261 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (761261 / 500000) = -Real.log (500000 / 761261) := by
    rw [show ((761261 / 500000) : ℝ) = ((500000 / 761261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (92404649 / 125000000) ≤ -Real.log (238739 / 500000) ∧
    -Real.log (238739 / 500000) ≤ (369618597 / 500000000) := by
  have h := checkLog_sound (w := (11261 / 488739)) (n := 12)
    (lo := (11522503 / 250000000)) (hi := (46090013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 238739) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 238739) = 1/(238739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-369618597 / 500000000) (-92404649 / 125000000) (Real.log (238739 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (421570057 / 1000000000) ≤ -Real.log (1000000 / 1524353) ∧
    -Real.log (1000000 / 1524353) ≤ (210785029 / 500000000) := by
  have h := checkLog_sound (w := (524353 / 2524353)) (n := 12)
    (lo := (421570057 / 1000000000)) (hi := (210785029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1524353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1524353 / 1000000) = 1/(1000000 / 1524353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (421570057 / 1000000000) (210785029 / 500000000) (Real.log (1524353 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1524353 / 1000000) = -Real.log (1000000 / 1524353) := by
    rw [show ((1524353 / 1000000) : ℝ) = ((1000000 / 1524353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (148615859 / 200000000) ≤ -Real.log (475647 / 1000000) ∧
    -Real.log (475647 / 1000000) ≤ (743079297 / 1000000000) := by
  have h := checkLog_sound (w := (24353 / 975647)) (n := 12)
    (lo := (9986423 / 200000000)) (hi := (12483029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 475647) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 475647) = 1/(475647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-743079297 / 1000000000) (-148615859 / 200000000) (Real.log (475647 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (336146469 / 1000000000) ≤ -Real.log (125000 / 174943) ∧
    -Real.log (125000 / 174943) ≤ (33614647 / 100000000) := by
  have h := checkLog_sound (w := (49943 / 299943)) (n := 12)
    (lo := (336146469 / 1000000000)) (hi := (33614647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174943 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174943 / 125000) = 1/(125000 / 174943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (336146469 / 1000000000) (33614647 / 100000000) (Real.log (174943 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (174943 / 125000) = -Real.log (125000 / 174943) := by
    rw [show ((174943 / 125000) : ℝ) = ((125000 / 174943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (63758239 / 125000000) ≤ -Real.log (75057 / 125000) ∧
    -Real.log (75057 / 125000) ≤ (510065913 / 1000000000) := by
  have h := checkLog_sound (w := (49943 / 200057)) (n := 12)
    (lo := (63758239 / 125000000)) (hi := (510065913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 75057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 75057) = 1/(75057 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-510065913 / 1000000000) (-63758239 / 125000000) (Real.log (75057 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (337309029 / 1000000000) ≤ -Real.log (250000 / 350293) ∧
    -Real.log (250000 / 350293) ≤ (33730903 / 100000000) := by
  have h := checkLog_sound (w := (100293 / 600293)) (n := 12)
    (lo := (337309029 / 1000000000)) (hi := (33730903 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350293 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350293 / 250000) = 1/(250000 / 350293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (337309029 / 1000000000) (33730903 / 100000000) (Real.log (350293 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (350293 / 250000) = -Real.log (250000 / 350293) := by
    rw [show ((350293 / 250000) : ℝ) = ((250000 / 350293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (512780867 / 1000000000) ≤ -Real.log (149707 / 250000) ∧
    -Real.log (149707 / 250000) ≤ (128195217 / 250000000) := by
  have h := checkLog_sound (w := (100293 / 399707)) (n := 12)
    (lo := (512780867 / 1000000000)) (hi := (128195217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 149707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 149707) = 1/(149707 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-128195217 / 250000000) (-512780867 / 1000000000) (Real.log (149707 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1159605363 / 1000000000) ≤ -Real.log (20000000000 / 63773493229) ∧
    -Real.log (20000000000 / 63773493229) ≤ (231921073 / 200000000) := by
  have h := checkLog_sound (w := (23773493229 / 103773493229)) (n := 12)
    (lo := (466458183 / 1000000000)) (hi := (58307273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63773493229 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63773493229 / 40000000000) = 1/(20000000000 / 63773493229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1159605363 / 1000000000) (231921073 / 200000000) (Real.log (63773493229 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (63773493229 / 20000000000) = -Real.log (20000000000 / 63773493229) := by
    rw [show ((63773493229 / 20000000000) : ℝ) = ((20000000000 / 63773493229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1164649353 / 1000000000) ≤ -Real.log (250000000000 / 801199734257) ∧
    -Real.log (250000000000 / 801199734257) ≤ (232929871 / 200000000) := by
  have h := checkLog_sound (w := (301199734257 / 1301199734257)) (n := 12)
    (lo := (471502173 / 1000000000)) (hi := (235751087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801199734257 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(801199734257 / 500000000000) = 1/(250000000000 / 801199734257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1164649353 / 1000000000) (232929871 / 200000000) (Real.log (801199734257 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (801199734257 / 250000000000) = -Real.log (250000000000 / 801199734257) := by
    rw [show ((801199734257 / 250000000000) : ℝ) = ((250000000000 / 801199734257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (846212381 / 1000000000) ≤ -Real.log (100000000000 / 233080192387) ∧
    -Real.log (100000000000 / 233080192387) ≤ (846212383 / 1000000000) := by
  have h := checkLog_sound (w := (33080192387 / 433080192387)) (n := 12)
    (lo := (153065201 / 1000000000)) (hi := (76532601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233080192387 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(233080192387 / 200000000000) = 1/(100000000000 / 233080192387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (846212381 / 1000000000) (846212383 / 1000000000) (Real.log (233080192387 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (233080192387 / 100000000000) = -Real.log (100000000000 / 233080192387) := by
    rw [show ((233080192387 / 100000000000) : ℝ) = ((100000000000 / 233080192387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (106261237 / 125000000) ≤ -Real.log (250000000000 / 584964296927) ∧
    -Real.log (250000000000 / 584964296927) ≤ (425044949 / 500000000) := by
  have h := checkLog_sound (w := (84964296927 / 1084964296927)) (n := 12)
    (lo := (39235679 / 250000000)) (hi := (156942717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584964296927 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(584964296927 / 500000000000) = 1/(250000000000 / 584964296927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (106261237 / 125000000) (425044949 / 500000000) (Real.log (584964296927 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (584964296927 / 250000000000) = -Real.log (250000000000 / 584964296927) := by
    rw [show ((584964296927 / 250000000000) : ℝ) = ((250000000000 / 584964296927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0130

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0131Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0131
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

theorem reflection_log_1_neg : (61405007 / 200000000) ≤ -Real.log (64 / 87) ∧
    -Real.log (64 / 87) ≤ (76756259 / 250000000) := by
  have h := checkLog_sound (w := (23 / 151)) (n := 12)
    (lo := (61405007 / 200000000)) (hi := (76756259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87 / 64) = 1/(64 / 87) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (61405007 / 200000000) (76756259 / 250000000) (Real.log (87 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (87 / 64) = -Real.log (64 / 87) := by
    rw [show ((87 / 64) : ℝ) = ((64 / 87) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (55663877 / 125000000) ≤ -Real.log (41 / 64) ∧
    -Real.log (41 / 64) ≤ (445311017 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 41) = 1/(41 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-445311017 / 1000000000) (-55663877 / 125000000) (Real.log (41 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (153081297 / 500000000) ≤ -Real.log (2560 / 3477) ∧
    -Real.log (2560 / 3477) ≤ (61232519 / 200000000) := by
  have h := checkLog_sound (w := (917 / 6037)) (n := 12)
    (lo := (153081297 / 500000000)) (hi := (61232519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3477 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3477 / 2560) = 1/(2560 / 3477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (153081297 / 500000000) (61232519 / 200000000) (Real.log (3477 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3477 / 2560) = -Real.log (2560 / 3477) := by
    rw [show ((3477 / 2560) : ℝ) = ((2560 / 3477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (443483419 / 1000000000) ≤ -Real.log (1643 / 2560) ∧
    -Real.log (1643 / 2560) ≤ (22174171 / 50000000) := by
  have h := checkLog_sound (w := (917 / 4203)) (n := 12)
    (lo := (443483419 / 1000000000)) (hi := (22174171 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1643) = 1/(1643 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22174171 / 50000000) (-443483419 / 1000000000) (Real.log (1643 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (270798641 / 500000000) ≤ -Real.log (32 / 55) ∧
    -Real.log (32 / 55) ≤ (541597283 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 87)) (n := 12)
    (lo := (270798641 / 500000000)) (hi := (541597283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55 / 32) = 1/(32 / 55) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (270798641 / 500000000) (541597283 / 1000000000) (Real.log (55 / 32)) := by
  have h := reflection_log_5_neg
  have he : Real.log (55 / 32) = -Real.log (32 / 55) := by
    rw [show ((55 / 32) : ℝ) = ((32 / 55) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (317127831 / 250000000) ≤ -Real.log (9 / 32) ∧
    -Real.log (9 / 32) ≤ (634255663 / 500000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 9) = 1/(9 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-634255663 / 500000000) (-317127831 / 250000000) (Real.log (9 / 32)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (108046543 / 200000000) ≤ -Real.log (1280 / 2197) ∧
    -Real.log (1280 / 2197) ≤ (135058179 / 250000000) := by
  have h := checkLog_sound (w := (917 / 3477)) (n := 12)
    (lo := (108046543 / 200000000)) (hi := (135058179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2197 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2197 / 1280) = 1/(1280 / 2197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (108046543 / 200000000) (135058179 / 250000000) (Real.log (2197 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2197 / 1280) = -Real.log (1280 / 2197) := by
    rw [show ((2197 / 1280) : ℝ) = ((1280 / 2197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (630106261 / 500000000) ≤ -Real.log (363 / 1280) ∧
    -Real.log (363 / 1280) ≤ (315053131 / 250000000) := by
  have h := checkLog_sound (w := (277 / 1003)) (n := 12)
    (lo := (283532671 / 500000000)) (hi := (567065343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 363) = 1/(363 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-315053131 / 250000000) (-630106261 / 500000000) (Real.log (363 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (419166809 / 1000000000) ≤ -Real.log (500000 / 760347) ∧
    -Real.log (500000 / 760347) ≤ (41916681 / 100000000) := by
  have h := checkLog_sound (w := (260347 / 1260347)) (n := 12)
    (lo := (419166809 / 1000000000)) (hi := (41916681 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760347 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760347 / 500000) = 1/(500000 / 760347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (419166809 / 1000000000) (41916681 / 100000000) (Real.log (760347 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (760347 / 500000) = -Real.log (500000 / 760347) := by
    rw [show ((760347 / 500000) : ℝ) = ((500000 / 760347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (367708027 / 500000000) ≤ -Real.log (239653 / 500000) ∧
    -Real.log (239653 / 500000) ≤ (91927007 / 125000000) := by
  have h := checkLog_sound (w := (10347 / 489653)) (n := 12)
    (lo := (21134437 / 500000000)) (hi := (338151 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 239653) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 239653) = 1/(239653 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91927007 / 125000000) (-367708027 / 500000000) (Real.log (239653 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (420368827 / 1000000000) ≤ -Real.log (1000000 / 1522523) ∧
    -Real.log (1000000 / 1522523) ≤ (105092207 / 250000000) := by
  have h := checkLog_sound (w := (522523 / 2522523)) (n := 12)
    (lo := (420368827 / 1000000000)) (hi := (105092207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1522523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1522523 / 1000000) = 1/(1000000 / 1522523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (420368827 / 1000000000) (105092207 / 250000000) (Real.log (1522523 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1522523 / 1000000) = -Real.log (1000000 / 1522523) := by
    rw [show ((1522523 / 1000000) : ℝ) = ((1000000 / 1522523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (739239287 / 1000000000) ≤ -Real.log (477477 / 1000000) ∧
    -Real.log (477477 / 1000000) ≤ (739239289 / 1000000000) := by
  have h := checkLog_sound (w := (22523 / 977477)) (n := 12)
    (lo := (46092107 / 1000000000)) (hi := (11523027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 477477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 477477) = 1/(477477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-739239289 / 1000000000) (-739239287 / 1000000000) (Real.log (477477 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10468339 / 31250000) ≤ -Real.log (500000 / 698961) ∧
    -Real.log (500000 / 698961) ≤ (334986849 / 1000000000) := by
  have h := checkLog_sound (w := (198961 / 1198961)) (n := 12)
    (lo := (10468339 / 31250000)) (hi := (334986849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698961 / 500000) = 1/(500000 / 698961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10468339 / 31250000) (334986849 / 1000000000) (Real.log (698961 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (698961 / 500000) = -Real.log (500000 / 698961) := by
    rw [show ((698961 / 500000) : ℝ) = ((500000 / 698961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (507368273 / 1000000000) ≤ -Real.log (301039 / 500000) ∧
    -Real.log (301039 / 500000) ≤ (253684137 / 500000000) := by
  have h := checkLog_sound (w := (198961 / 801039)) (n := 12)
    (lo := (507368273 / 1000000000)) (hi := (253684137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 301039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 301039) = 1/(301039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-253684137 / 500000000) (-507368273 / 1000000000) (Real.log (301039 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (336147183 / 1000000000) ≤ -Real.log (200000 / 279909) ∧
    -Real.log (200000 / 279909) ≤ (21009199 / 62500000) := by
  have h := checkLog_sound (w := (79909 / 479909)) (n := 12)
    (lo := (336147183 / 1000000000)) (hi := (21009199 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279909 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279909 / 200000) = 1/(200000 / 279909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (336147183 / 1000000000) (21009199 / 62500000) (Real.log (279909 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (279909 / 200000) = -Real.log (200000 / 279909) := by
    rw [show ((279909 / 200000) : ℝ) = ((200000 / 279909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (510067577 / 1000000000) ≤ -Real.log (120091 / 200000) ∧
    -Real.log (120091 / 200000) ≤ (255033789 / 500000000) := by
  have h := checkLog_sound (w := (79909 / 320091)) (n := 12)
    (lo := (510067577 / 1000000000)) (hi := (255033789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120091) = 1/(120091 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-255033789 / 500000000) (-510067577 / 1000000000) (Real.log (120091 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1154582863 / 1000000000) ≤ -Real.log (500000000000 / 1586349847487) ∧
    -Real.log (500000000000 / 1586349847487) ≤ (230916573 / 200000000) := by
  have h := checkLog_sound (w := (586349847487 / 2586349847487)) (n := 12)
    (lo := (461435683 / 1000000000)) (hi := (115358921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1586349847487 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1586349847487 / 1000000000000) = 1/(500000000000 / 1586349847487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1154582863 / 1000000000) (230916573 / 200000000) (Real.log (1586349847487 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1586349847487 / 500000000000) = -Real.log (500000000000 / 1586349847487) := by
    rw [show ((1586349847487 / 500000000000) : ℝ) = ((500000000000 / 1586349847487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (579804057 / 500000000) ≤ -Real.log (62500000000 / 199292714623) ∧
    -Real.log (62500000000 / 199292714623) ≤ (289902029 / 250000000) := by
  have h := checkLog_sound (w := (74292714623 / 324292714623)) (n := 12)
    (lo := (233230467 / 500000000)) (hi := (93292187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199292714623 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(199292714623 / 125000000000) = 1/(62500000000 / 199292714623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (579804057 / 500000000) (289902029 / 250000000) (Real.log (199292714623 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (199292714623 / 62500000000) = -Real.log (62500000000 / 199292714623) := by
    rw [show ((199292714623 / 62500000000) : ℝ) = ((62500000000 / 199292714623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (842355121 / 1000000000) ≤ -Real.log (500000000000 / 1160914366577) ∧
    -Real.log (500000000000 / 1160914366577) ≤ (842355123 / 1000000000) := by
  have h := checkLog_sound (w := (160914366577 / 2160914366577)) (n := 12)
    (lo := (149207941 / 1000000000)) (hi := (74603971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160914366577 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1160914366577 / 1000000000000) = 1/(500000000000 / 1160914366577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (842355121 / 1000000000) (842355123 / 1000000000) (Real.log (1160914366577 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1160914366577 / 500000000000) = -Real.log (500000000000 / 1160914366577) := by
    rw [show ((1160914366577 / 500000000000) : ℝ) = ((500000000000 / 1160914366577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (846214761 / 1000000000) ≤ -Real.log (500000000000 / 1165403735501) ∧
    -Real.log (500000000000 / 1165403735501) ≤ (846214763 / 1000000000) := by
  have h := checkLog_sound (w := (165403735501 / 2165403735501)) (n := 12)
    (lo := (153067581 / 1000000000)) (hi := (76533791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1165403735501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1165403735501 / 1000000000000) = 1/(500000000000 / 1165403735501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (846214761 / 1000000000) (846214763 / 1000000000) (Real.log (1165403735501 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1165403735501 / 500000000000) = -Real.log (500000000000 / 1165403735501) := by
    rw [show ((1165403735501 / 500000000000) : ℝ) = ((500000000000 / 1165403735501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0131

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0132Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0132
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

theorem reflection_log_1_neg : (153081297 / 500000000) ≤ -Real.log (2560 / 3477) ∧
    -Real.log (2560 / 3477) ≤ (61232519 / 200000000) := by
  have h := checkLog_sound (w := (917 / 6037)) (n := 12)
    (lo := (153081297 / 500000000)) (hi := (61232519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3477 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3477 / 2560) = 1/(2560 / 3477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (153081297 / 500000000) (61232519 / 200000000) (Real.log (3477 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3477 / 2560) = -Real.log (2560 / 3477) := by
    rw [show ((3477 / 2560) : ℝ) = ((2560 / 3477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (443483419 / 1000000000) ≤ -Real.log (1643 / 2560) ∧
    -Real.log (1643 / 2560) ≤ (22174171 / 50000000) := by
  have h := checkLog_sound (w := (917 / 4203)) (n := 12)
    (lo := (443483419 / 1000000000)) (hi := (22174171 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1643) = 1/(1643 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22174171 / 50000000) (-443483419 / 1000000000) (Real.log (1643 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (305299409 / 1000000000) ≤ -Real.log (1280 / 1737) ∧
    -Real.log (1280 / 1737) ≤ (30529941 / 100000000) := by
  have h := checkLog_sound (w := (457 / 3017)) (n := 12)
    (lo := (305299409 / 1000000000)) (hi := (30529941 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1737 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1737 / 1280) = 1/(1280 / 1737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (305299409 / 1000000000) (30529941 / 100000000) (Real.log (1737 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1737 / 1280) = -Real.log (1280 / 1737) := by
    rw [show ((1737 / 1280) : ℝ) = ((1280 / 1737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (110414789 / 250000000) ≤ -Real.log (823 / 1280) ∧
    -Real.log (823 / 1280) ≤ (441659157 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2103)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 823) = 1/(823 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-441659157 / 1000000000) (-110414789 / 250000000) (Real.log (823 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (108046543 / 200000000) ≤ -Real.log (1280 / 2197) ∧
    -Real.log (1280 / 2197) ≤ (135058179 / 250000000) := by
  have h := checkLog_sound (w := (917 / 3477)) (n := 12)
    (lo := (108046543 / 200000000)) (hi := (135058179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2197 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2197 / 1280) = 1/(1280 / 2197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (108046543 / 200000000) (135058179 / 250000000) (Real.log (2197 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2197 / 1280) = -Real.log (1280 / 2197) := by
    rw [show ((2197 / 1280) : ℝ) = ((1280 / 2197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (630106261 / 500000000) ≤ -Real.log (363 / 1280) ∧
    -Real.log (363 / 1280) ≤ (315053131 / 250000000) := by
  have h := checkLog_sound (w := (277 / 1003)) (n := 12)
    (lo := (283532671 / 500000000)) (hi := (567065343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 363) = 1/(363 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-315053131 / 250000000) (-630106261 / 500000000) (Real.log (363 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (538866283 / 1000000000) ≤ -Real.log (640 / 1097) ∧
    -Real.log (640 / 1097) ≤ (134716571 / 250000000) := by
  have h := checkLog_sound (w := (457 / 1737)) (n := 12)
    (lo := (538866283 / 1000000000)) (hi := (134716571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097 / 640) = 1/(640 / 1097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (538866283 / 1000000000) (134716571 / 250000000) (Real.log (1097 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1097 / 640) = -Real.log (640 / 1097) := by
    rw [show ((1097 / 640) : ℝ) = ((640 / 1097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (625991011 / 500000000) ≤ -Real.log (183 / 640) ∧
    -Real.log (183 / 640) ≤ (156497753 / 125000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 183) = 1/(183 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-156497753 / 125000000) (-625991011 / 500000000) (Real.log (183 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (208982331 / 500000000) ≤ -Real.log (1000000 / 1518867) ∧
    -Real.log (1000000 / 1518867) ≤ (417964663 / 1000000000) := by
  have h := checkLog_sound (w := (518867 / 2518867)) (n := 12)
    (lo := (208982331 / 500000000)) (hi := (417964663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1518867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1518867 / 1000000) = 1/(1000000 / 1518867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (208982331 / 500000000) (417964663 / 1000000000) (Real.log (1518867 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1518867 / 1000000) = -Real.log (1000000 / 1518867) := by
    rw [show ((1518867 / 1000000) : ℝ) = ((1000000 / 1518867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (731611539 / 1000000000) ≤ -Real.log (481133 / 1000000) ∧
    -Real.log (481133 / 1000000) ≤ (731611541 / 1000000000) := by
  have h := checkLog_sound (w := (18867 / 981133)) (n := 12)
    (lo := (38464359 / 1000000000)) (hi := (961609 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 481133) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 481133) = 1/(481133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-731611541 / 1000000000) (-731611539 / 1000000000) (Real.log (481133 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (419167467 / 1000000000) ≤ -Real.log (200000 / 304139) ∧
    -Real.log (200000 / 304139) ≤ (104791867 / 250000000) := by
  have h := checkLog_sound (w := (104139 / 504139)) (n := 12)
    (lo := (419167467 / 1000000000)) (hi := (104791867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304139 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304139 / 200000) = 1/(200000 / 304139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (419167467 / 1000000000) (104791867 / 250000000) (Real.log (304139 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (304139 / 200000) = -Real.log (200000 / 304139) := by
    rw [show ((304139 / 200000) : ℝ) = ((200000 / 304139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36770907 / 50000000) ≤ -Real.log (95861 / 200000) ∧
    -Real.log (95861 / 200000) ≤ (367709071 / 500000000) := by
  have h := checkLog_sound (w := (4139 / 195861)) (n := 12)
    (lo := (528387 / 12500000)) (hi := (42270961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 95861) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 95861) = 1/(95861 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-367709071 / 500000000) (-36770907 / 50000000) (Real.log (95861 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (66765749 / 200000000) ≤ -Real.log (62500 / 87269) ∧
    -Real.log (62500 / 87269) ≤ (166914373 / 500000000) := by
  have h := checkLog_sound (w := (24769 / 149769)) (n := 12)
    (lo := (66765749 / 200000000)) (hi := (166914373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87269 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87269 / 62500) = 1/(62500 / 87269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (66765749 / 200000000) (166914373 / 500000000) (Real.log (87269 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (87269 / 62500) = -Real.log (62500 / 87269) := by
    rw [show ((87269 / 62500) : ℝ) = ((62500 / 87269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (504684519 / 1000000000) ≤ -Real.log (37731 / 62500) ∧
    -Real.log (37731 / 62500) ≤ (12617113 / 25000000) := by
  have h := checkLog_sound (w := (24769 / 100231)) (n := 12)
    (lo := (504684519 / 1000000000)) (hi := (12617113 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 37731) = 1/(37731 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-12617113 / 25000000) (-504684519 / 1000000000) (Real.log (37731 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (334987563 / 1000000000) ≤ -Real.log (1000000 / 1397923) ∧
    -Real.log (1000000 / 1397923) ≤ (83746891 / 250000000) := by
  have h := checkLog_sound (w := (397923 / 2397923)) (n := 12)
    (lo := (334987563 / 1000000000)) (hi := (83746891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397923 / 1000000) = 1/(1000000 / 1397923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (334987563 / 1000000000) (83746891 / 250000000) (Real.log (1397923 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1397923 / 1000000) = -Real.log (1000000 / 1397923) := by
    rw [show ((1397923 / 1000000) : ℝ) = ((1000000 / 1397923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (253684967 / 500000000) ≤ -Real.log (602077 / 1000000) ∧
    -Real.log (602077 / 1000000) ≤ (101473987 / 200000000) := by
  have h := checkLog_sound (w := (397923 / 1602077)) (n := 12)
    (lo := (253684967 / 500000000)) (hi := (101473987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 602077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 602077) = 1/(602077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-101473987 / 200000000) (-253684967 / 500000000) (Real.log (602077 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1149576201 / 1000000000) ≤ -Real.log (125000000000 / 394606844677) ∧
    -Real.log (125000000000 / 394606844677) ≤ (1149576203 / 1000000000) := by
  have h := checkLog_sound (w := (144606844677 / 644606844677)) (n := 12)
    (lo := (456429021 / 1000000000)) (hi := (228214511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394606844677 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(394606844677 / 250000000000) = 1/(125000000000 / 394606844677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1149576201 / 1000000000) (1149576203 / 1000000000) (Real.log (394606844677 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (394606844677 / 125000000000) = -Real.log (125000000000 / 394606844677) := by
    rw [show ((394606844677 / 125000000000) : ℝ) = ((125000000000 / 394606844677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1154585607 / 1000000000) ≤ -Real.log (500000000000 / 1586354200353) ∧
    -Real.log (500000000000 / 1586354200353) ≤ (1154585609 / 1000000000) := by
  have h := checkLog_sound (w := (586354200353 / 2586354200353)) (n := 12)
    (lo := (461438427 / 1000000000)) (hi := (115359607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1586354200353 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1586354200353 / 1000000000000) = 1/(500000000000 / 1586354200353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1154585607 / 1000000000) (1154585609 / 1000000000) (Real.log (1586354200353 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1586354200353 / 500000000000) = -Real.log (500000000000 / 1586354200353) := by
    rw [show ((1586354200353 / 500000000000) : ℝ) = ((500000000000 / 1586354200353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (52407079 / 62500000) ≤ -Real.log (125000000000 / 289115713869) ∧
    -Real.log (125000000000 / 289115713869) ≤ (419256633 / 500000000) := by
  have h := checkLog_sound (w := (39115713869 / 539115713869)) (n := 12)
    (lo := (36341521 / 250000000)) (hi := (29073217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289115713869 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(289115713869 / 250000000000) = 1/(125000000000 / 289115713869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (52407079 / 62500000) (419256633 / 500000000) (Real.log (289115713869 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (289115713869 / 125000000000) = -Real.log (125000000000 / 289115713869) := by
    rw [show ((289115713869 / 125000000000) : ℝ) = ((125000000000 / 289115713869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (842357497 / 1000000000) ≤ -Real.log (500000000000 / 1160917125219) ∧
    -Real.log (500000000000 / 1160917125219) ≤ (842357499 / 1000000000) := by
  have h := checkLog_sound (w := (160917125219 / 2160917125219)) (n := 12)
    (lo := (149210317 / 1000000000)) (hi := (74605159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160917125219 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1160917125219 / 1000000000000) = 1/(500000000000 / 1160917125219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (842357497 / 1000000000) (842357499 / 1000000000) (Real.log (1160917125219 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1160917125219 / 500000000000) = -Real.log (500000000000 / 1160917125219) := by
    rw [show ((1160917125219 / 500000000000) : ℝ) = ((500000000000 / 1160917125219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0132

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0133Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0133
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

theorem reflection_log_1_neg : (305299409 / 1000000000) ≤ -Real.log (1280 / 1737) ∧
    -Real.log (1280 / 1737) ≤ (30529941 / 100000000) := by
  have h := checkLog_sound (w := (457 / 3017)) (n := 12)
    (lo := (305299409 / 1000000000)) (hi := (30529941 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1737 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1737 / 1280) = 1/(1280 / 1737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (305299409 / 1000000000) (30529941 / 100000000) (Real.log (1737 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1737 / 1280) = -Real.log (1280 / 1737) := by
    rw [show ((1737 / 1280) : ℝ) = ((1280 / 1737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (110414789 / 250000000) ≤ -Real.log (823 / 1280) ∧
    -Real.log (823 / 1280) ≤ (441659157 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2103)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 823) = 1/(823 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-441659157 / 1000000000) (-110414789 / 250000000) (Real.log (823 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (152217739 / 500000000) ≤ -Real.log (2560 / 3471) ∧
    -Real.log (2560 / 3471) ≤ (304435479 / 1000000000) := by
  have h := checkLog_sound (w := (911 / 6031)) (n := 12)
    (lo := (152217739 / 500000000)) (hi := (304435479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3471 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3471 / 2560) = 1/(2560 / 3471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (152217739 / 500000000) (304435479 / 1000000000) (Real.log (3471 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3471 / 2560) = -Real.log (2560 / 3471) := by
    rw [show ((3471 / 2560) : ℝ) = ((2560 / 3471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (219919107 / 500000000) ≤ -Real.log (1649 / 2560) ∧
    -Real.log (1649 / 2560) ≤ (87967643 / 200000000) := by
  have h := checkLog_sound (w := (911 / 4209)) (n := 12)
    (lo := (219919107 / 500000000)) (hi := (87967643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1649) = 1/(1649 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-87967643 / 200000000) (-219919107 / 500000000) (Real.log (1649 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (538866283 / 1000000000) ≤ -Real.log (640 / 1097) ∧
    -Real.log (640 / 1097) ≤ (134716571 / 250000000) := by
  have h := checkLog_sound (w := (457 / 1737)) (n := 12)
    (lo := (538866283 / 1000000000)) (hi := (134716571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097 / 640) = 1/(640 / 1097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (538866283 / 1000000000) (134716571 / 250000000) (Real.log (1097 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1097 / 640) = -Real.log (640 / 1097) := by
    rw [show ((1097 / 640) : ℝ) = ((640 / 1097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (625991011 / 500000000) ≤ -Real.log (183 / 640) ∧
    -Real.log (183 / 640) ≤ (156497753 / 125000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 183) = 1/(183 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-156497753 / 125000000) (-625991011 / 500000000) (Real.log (183 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (268748991 / 500000000) ≤ -Real.log (1280 / 2191) ∧
    -Real.log (1280 / 2191) ≤ (537497983 / 1000000000) := by
  have h := checkLog_sound (w := (911 / 3471)) (n := 12)
    (lo := (268748991 / 500000000)) (hi := (537497983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2191 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2191 / 1280) = 1/(1280 / 2191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (268748991 / 500000000) (537497983 / 1000000000) (Real.log (2191 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2191 / 1280) = -Real.log (1280 / 2191) := by
    rw [show ((2191 / 1280) : ℝ) = ((1280 / 2191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (155477339 / 125000000) ≤ -Real.log (369 / 1280) ∧
    -Real.log (369 / 1280) ≤ (621909357 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1009)) (n := 12)
    (lo := (137667883 / 250000000)) (hi := (550671533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 369) = 1/(369 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-621909357 / 500000000) (-155477339 / 125000000) (Real.log (369 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (208381193 / 500000000) ≤ -Real.log (500000 / 758521) ∧
    -Real.log (500000 / 758521) ≤ (416762387 / 1000000000) := by
  have h := checkLog_sound (w := (258521 / 1258521)) (n := 12)
    (lo := (208381193 / 500000000)) (hi := (416762387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758521 / 500000) = 1/(500000 / 758521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (208381193 / 500000000) (416762387 / 1000000000) (Real.log (758521 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (758521 / 500000) = -Real.log (500000 / 758521) := by
    rw [show ((758521 / 500000) : ℝ) = ((500000 / 758521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (145565117 / 200000000) ≤ -Real.log (241479 / 500000) ∧
    -Real.log (241479 / 500000) ≤ (727825587 / 1000000000) := by
  have h := checkLog_sound (w := (8521 / 491479)) (n := 12)
    (lo := (6935681 / 200000000)) (hi := (17339203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 241479) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 241479) = 1/(241479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-727825587 / 1000000000) (-145565117 / 200000000) (Real.log (241479 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10449133 / 25000000) ≤ -Real.log (250000 / 379717) ∧
    -Real.log (250000 / 379717) ≤ (417965321 / 1000000000) := by
  have h := checkLog_sound (w := (129717 / 629717)) (n := 12)
    (lo := (10449133 / 25000000)) (hi := (417965321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379717 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379717 / 250000) = 1/(250000 / 379717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10449133 / 25000000) (417965321 / 1000000000) (Real.log (379717 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (379717 / 250000) = -Real.log (250000 / 379717) := by
    rw [show ((379717 / 250000) : ℝ) = ((250000 / 379717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (731613617 / 1000000000) ≤ -Real.log (120283 / 250000) ∧
    -Real.log (120283 / 250000) ≤ (731613619 / 1000000000) := by
  have h := checkLog_sound (w := (4717 / 245283)) (n := 12)
    (lo := (38466437 / 1000000000)) (hi := (19233219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 120283) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 120283) = 1/(120283 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-731613619 / 1000000000) (-731613617 / 1000000000) (Real.log (120283 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (41584021 / 125000000) ≤ -Real.log (100000 / 139469) ∧
    -Real.log (100000 / 139469) ≤ (332672169 / 1000000000) := by
  have h := checkLog_sound (w := (39469 / 239469)) (n := 12)
    (lo := (41584021 / 125000000)) (hi := (332672169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139469 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139469 / 100000) = 1/(100000 / 139469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (41584021 / 125000000) (332672169 / 1000000000) (Real.log (139469 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (139469 / 100000) = -Real.log (100000 / 139469) := by
    rw [show ((139469 / 100000) : ℝ) = ((100000 / 139469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (100402911 / 200000000) ≤ -Real.log (60531 / 100000) ∧
    -Real.log (60531 / 100000) ≤ (125503639 / 250000000) := by
  have h := checkLog_sound (w := (39469 / 160531)) (n := 12)
    (lo := (100402911 / 200000000)) (hi := (125503639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 60531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 60531) = 1/(60531 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-125503639 / 250000000) (-100402911 / 200000000) (Real.log (60531 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (333829461 / 1000000000) ≤ -Real.log (200000 / 279261) ∧
    -Real.log (200000 / 279261) ≤ (166914731 / 500000000) := by
  have h := checkLog_sound (w := (79261 / 479261)) (n := 12)
    (lo := (333829461 / 1000000000)) (hi := (166914731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279261 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279261 / 200000) = 1/(200000 / 279261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (333829461 / 1000000000) (166914731 / 500000000) (Real.log (279261 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (279261 / 200000) = -Real.log (200000 / 279261) := by
    rw [show ((279261 / 200000) : ℝ) = ((200000 / 279261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20187447 / 40000000) ≤ -Real.log (120739 / 200000) ∧
    -Real.log (120739 / 200000) ≤ (15771443 / 31250000) := by
  have h := checkLog_sound (w := (79261 / 320739)) (n := 12)
    (lo := (20187447 / 40000000)) (hi := (15771443 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120739) = 1/(120739 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-15771443 / 31250000) (-20187447 / 40000000) (Real.log (120739 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1144587971 / 1000000000) ≤ -Real.log (125000000000 / 392643356151) ∧
    -Real.log (125000000000 / 392643356151) ≤ (1144587973 / 1000000000) := by
  have h := checkLog_sound (w := (142643356151 / 642643356151)) (n := 12)
    (lo := (451440791 / 1000000000)) (hi := (56430099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392643356151 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(392643356151 / 250000000000) = 1/(125000000000 / 392643356151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1144587971 / 1000000000) (1144587973 / 1000000000) (Real.log (392643356151 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (392643356151 / 125000000000) = -Real.log (125000000000 / 392643356151) := by
    rw [show ((392643356151 / 125000000000) : ℝ) = ((125000000000 / 392643356151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (574789469 / 500000000) ≤ -Real.log (250000000000 / 789215849289) ∧
    -Real.log (250000000000 / 789215849289) ≤ (57478947 / 50000000) := by
  have h := checkLog_sound (w := (289215849289 / 1289215849289)) (n := 12)
    (lo := (228215879 / 500000000)) (hi := (456431759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789215849289 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(789215849289 / 500000000000) = 1/(250000000000 / 789215849289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (574789469 / 500000000) (57478947 / 50000000) (Real.log (789215849289 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (789215849289 / 250000000000) = -Real.log (250000000000 / 789215849289) := by
    rw [show ((789215849289 / 250000000000) : ℝ) = ((250000000000 / 789215849289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (834686723 / 1000000000) ≤ -Real.log (125000000000 / 288011514761) ∧
    -Real.log (125000000000 / 288011514761) ≤ (33387469 / 40000000) := by
  have h := checkLog_sound (w := (38011514761 / 538011514761)) (n := 12)
    (lo := (141539543 / 1000000000)) (hi := (17692443 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288011514761 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(288011514761 / 250000000000) = 1/(125000000000 / 288011514761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (834686723 / 1000000000) (33387469 / 40000000) (Real.log (288011514761 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (288011514761 / 125000000000) = -Real.log (125000000000 / 288011514761) := by
    rw [show ((288011514761 / 125000000000) : ℝ) = ((125000000000 / 288011514761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (209628909 / 250000000) ≤ -Real.log (500000000000 / 1156465599351) ∧
    -Real.log (500000000000 / 1156465599351) ≤ (419257819 / 500000000) := by
  have h := checkLog_sound (w := (156465599351 / 2156465599351)) (n := 12)
    (lo := (18171057 / 125000000)) (hi := (145368457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156465599351 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1156465599351 / 1000000000000) = 1/(500000000000 / 1156465599351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (209628909 / 250000000) (419257819 / 500000000) (Real.log (1156465599351 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1156465599351 / 500000000000) = -Real.log (500000000000 / 1156465599351) := by
    rw [show ((1156465599351 / 500000000000) : ℝ) = ((500000000000 / 1156465599351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0133

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0134Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0134
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

theorem reflection_log_1_neg : (152217739 / 500000000) ≤ -Real.log (2560 / 3471) ∧
    -Real.log (2560 / 3471) ≤ (304435479 / 1000000000) := by
  have h := checkLog_sound (w := (911 / 6031)) (n := 12)
    (lo := (152217739 / 500000000)) (hi := (304435479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3471 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3471 / 2560) = 1/(2560 / 3471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (152217739 / 500000000) (304435479 / 1000000000) (Real.log (3471 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3471 / 2560) = -Real.log (2560 / 3471) := by
    rw [show ((3471 / 2560) : ℝ) = ((2560 / 3471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (219919107 / 500000000) ≤ -Real.log (1649 / 2560) ∧
    -Real.log (1649 / 2560) ≤ (87967643 / 200000000) := by
  have h := checkLog_sound (w := (911 / 4209)) (n := 12)
    (lo := (219919107 / 500000000)) (hi := (87967643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1649) = 1/(1649 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-87967643 / 200000000) (-219919107 / 500000000) (Real.log (1649 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (758927 / 2500000) ≤ -Real.log (640 / 867) ∧
    -Real.log (640 / 867) ≤ (303570801 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1507)) (n := 12)
    (lo := (758927 / 2500000)) (hi := (303570801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867 / 640) = 1/(640 / 867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (758927 / 2500000) (303570801 / 1000000000) (Real.log (867 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (867 / 640) = -Real.log (640 / 867) := by
    rw [show ((867 / 640) : ℝ) = ((640 / 867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (438020583 / 1000000000) ≤ -Real.log (413 / 640) ∧
    -Real.log (413 / 640) ≤ (54752573 / 125000000) := by
  have h := checkLog_sound (w := (227 / 1053)) (n := 12)
    (lo := (438020583 / 1000000000)) (hi := (54752573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 413) = 1/(413 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-54752573 / 125000000) (-438020583 / 1000000000) (Real.log (413 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (268748991 / 500000000) ≤ -Real.log (1280 / 2191) ∧
    -Real.log (1280 / 2191) ≤ (537497983 / 1000000000) := by
  have h := checkLog_sound (w := (911 / 3471)) (n := 12)
    (lo := (268748991 / 500000000)) (hi := (537497983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2191 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2191 / 1280) = 1/(1280 / 2191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (268748991 / 500000000) (537497983 / 1000000000) (Real.log (2191 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2191 / 1280) = -Real.log (1280 / 2191) := by
    rw [show ((2191 / 1280) : ℝ) = ((1280 / 2191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (155477339 / 125000000) ≤ -Real.log (369 / 1280) ∧
    -Real.log (369 / 1280) ≤ (621909357 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1009)) (n := 12)
    (lo := (137667883 / 250000000)) (hi := (550671533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 369) = 1/(369 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-621909357 / 500000000) (-155477339 / 125000000) (Real.log (369 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (268063903 / 500000000) ≤ -Real.log (320 / 547) ∧
    -Real.log (320 / 547) ≤ (536127807 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 867)) (n := 12)
    (lo := (268063903 / 500000000)) (hi := (536127807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547 / 320) = 1/(320 / 547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (268063903 / 500000000) (536127807 / 1000000000) (Real.log (547 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (547 / 320) = -Real.log (320 / 547) := by
    rw [show ((547 / 320) : ℝ) = ((320 / 547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (617860751 / 500000000) ≤ -Real.log (93 / 320) ∧
    -Real.log (93 / 320) ≤ (38616297 / 31250000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 93) = 1/(93 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38616297 / 31250000) (-617860751 / 500000000) (Real.log (93 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (207780321 / 500000000) ≤ -Real.log (50000 / 75761) ∧
    -Real.log (50000 / 75761) ≤ (415560643 / 1000000000) := by
  have h := checkLog_sound (w := (25761 / 125761)) (n := 12)
    (lo := (207780321 / 500000000)) (hi := (415560643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75761 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75761 / 50000) = 1/(50000 / 75761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (207780321 / 500000000) (415560643 / 1000000000) (Real.log (75761 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (75761 / 50000) = -Real.log (50000 / 75761) := by
    rw [show ((75761 / 50000) : ℝ) = ((50000 / 75761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (362030049 / 500000000) ≤ -Real.log (24239 / 50000) ∧
    -Real.log (24239 / 50000) ≤ (7240601 / 10000000) := by
  have h := checkLog_sound (w := (761 / 49239)) (n := 12)
    (lo := (15456459 / 500000000)) (hi := (30912919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 24239) = 1/(24239 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7240601 / 10000000) (-362030049 / 500000000) (Real.log (24239 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83352609 / 200000000) ≤ -Real.log (1000000 / 1517043) ∧
    -Real.log (1000000 / 1517043) ≤ (208381523 / 500000000) := by
  have h := checkLog_sound (w := (517043 / 2517043)) (n := 12)
    (lo := (83352609 / 200000000)) (hi := (208381523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1517043 / 1000000) = 1/(1000000 / 1517043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83352609 / 200000000) (208381523 / 500000000) (Real.log (1517043 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1517043 / 1000000) = -Real.log (1000000 / 1517043) := by
    rw [show ((1517043 / 1000000) : ℝ) = ((1000000 / 1517043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (145565531 / 200000000) ≤ -Real.log (482957 / 1000000) ∧
    -Real.log (482957 / 1000000) ≤ (727827657 / 1000000000) := by
  have h := checkLog_sound (w := (17043 / 982957)) (n := 12)
    (lo := (1387219 / 40000000)) (hi := (8670119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 482957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 482957) = 1/(482957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-727827657 / 1000000000) (-145565531 / 200000000) (Real.log (482957 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (331517123 / 1000000000) ≤ -Real.log (25000 / 34827) ∧
    -Real.log (25000 / 34827) ≤ (82879281 / 250000000) := by
  have h := checkLog_sound (w := (9827 / 59827)) (n := 12)
    (lo := (331517123 / 1000000000)) (hi := (82879281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34827 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34827 / 25000) = 1/(25000 / 34827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (331517123 / 1000000000) (82879281 / 250000000) (Real.log (34827 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (34827 / 25000) = -Real.log (25000 / 34827) := by
    rw [show ((34827 / 25000) : ℝ) = ((25000 / 34827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (124839573 / 250000000) ≤ -Real.log (15173 / 25000) ∧
    -Real.log (15173 / 25000) ≤ (499358293 / 1000000000) := by
  have h := checkLog_sound (w := (9827 / 40173)) (n := 12)
    (lo := (124839573 / 250000000)) (hi := (499358293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 15173) = 1/(15173 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-499358293 / 1000000000) (-124839573 / 250000000) (Real.log (15173 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (66534577 / 200000000) ≤ -Real.log (1000000 / 1394691) ∧
    -Real.log (1000000 / 1394691) ≤ (166336443 / 500000000) := by
  have h := checkLog_sound (w := (394691 / 2394691)) (n := 12)
    (lo := (66534577 / 200000000)) (hi := (166336443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1394691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1394691 / 1000000) = 1/(1000000 / 1394691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (66534577 / 200000000) (166336443 / 500000000) (Real.log (1394691 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1394691 / 1000000) = -Real.log (1000000 / 1394691) := by
    rw [show ((1394691 / 1000000) : ℝ) = ((1000000 / 1394691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (502016207 / 1000000000) ≤ -Real.log (605309 / 1000000) ∧
    -Real.log (605309 / 1000000) ≤ (31376013 / 62500000) := by
  have h := checkLog_sound (w := (394691 / 1605309)) (n := 12)
    (lo := (502016207 / 1000000000)) (hi := (31376013 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 605309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 605309) = 1/(605309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-31376013 / 62500000) (-502016207 / 1000000000) (Real.log (605309 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1139620741 / 1000000000) ≤ -Real.log (1562500000 / 4883723029) ∧
    -Real.log (1562500000 / 4883723029) ≤ (1139620743 / 1000000000) := by
  have h := checkLog_sound (w := (1758723029 / 8008723029)) (n := 12)
    (lo := (446473561 / 1000000000)) (hi := (223236781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4883723029 / 3125000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4883723029 / 3125000000) = 1/(1562500000 / 4883723029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1139620741 / 1000000000) (1139620743 / 1000000000) (Real.log (4883723029 / 1562500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4883723029 / 1562500000) = -Real.log (1562500000 / 4883723029) := by
    rw [show ((4883723029 / 1562500000) : ℝ) = ((1562500000 / 4883723029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1144590701 / 1000000000) ≤ -Real.log (31250000000 / 98161106993) ∧
    -Real.log (31250000000 / 98161106993) ≤ (1144590703 / 1000000000) := by
  have h := checkLog_sound (w := (35661106993 / 160661106993)) (n := 12)
    (lo := (451443521 / 1000000000)) (hi := (225721761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98161106993 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(98161106993 / 62500000000) = 1/(31250000000 / 98161106993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1144590701 / 1000000000) (1144590703 / 1000000000) (Real.log (98161106993 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (98161106993 / 31250000000) = -Real.log (31250000000 / 98161106993) := by
    rw [show ((98161106993 / 31250000000) : ℝ) = ((31250000000 / 98161106993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (415437707 / 500000000) ≤ -Real.log (125000000000 / 286915903249) ∧
    -Real.log (125000000000 / 286915903249) ≤ (103859427 / 125000000) := by
  have h := checkLog_sound (w := (36915903249 / 536915903249)) (n := 12)
    (lo := (68864117 / 500000000)) (hi := (27545647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286915903249 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(286915903249 / 250000000000) = 1/(125000000000 / 286915903249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (415437707 / 500000000) (103859427 / 125000000) (Real.log (286915903249 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (286915903249 / 125000000000) = -Real.log (125000000000 / 286915903249) := by
    rw [show ((286915903249 / 125000000000) : ℝ) = ((125000000000 / 286915903249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (208672273 / 250000000) ≤ -Real.log (100000000000 / 230409757661) ∧
    -Real.log (100000000000 / 230409757661) ≤ (417344547 / 500000000) := by
  have h := checkLog_sound (w := (30409757661 / 430409757661)) (n := 12)
    (lo := (17692739 / 125000000)) (hi := (141541913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230409757661 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(230409757661 / 200000000000) = 1/(100000000000 / 230409757661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (208672273 / 250000000) (417344547 / 500000000) (Real.log (230409757661 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (230409757661 / 100000000000) = -Real.log (100000000000 / 230409757661) := by
    rw [show ((230409757661 / 100000000000) : ℝ) = ((100000000000 / 230409757661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0134

end


