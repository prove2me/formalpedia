-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0233Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0233Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:28:31.220989+00:00
-- url     : https://prove2.me/theorems/9f0d6c2d-ba83-46a9-873e-1dcedd9ed7e3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0233Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0234Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0233Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0234Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0235Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0236Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0237Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0238Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0239Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0240Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0233Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0234Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0235Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0236Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0237Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0238Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0239Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0240Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0233Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0234Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0235Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0236Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0237Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0238Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0239Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0240Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0233Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0234Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0235Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0236Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0237Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0238Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0239Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0240Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0233Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0233
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

theorem reflection_log_1_neg : (250728319 / 1000000000) ≤ -Real.log (5120 / 6579) ∧
    -Real.log (5120 / 6579) ≤ (391763 / 1562500) := by
  have h := checkLog_sound (w := (1459 / 11699)) (n := 12)
    (lo := (250728319 / 1000000000)) (hi := (391763 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6579 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6579 / 5120) = 1/(5120 / 6579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (250728319 / 1000000000) (391763 / 1562500) (Real.log (6579 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6579 / 5120) = -Real.log (5120 / 6579) := by
    rw [show ((6579 / 5120) : ℝ) = ((5120 / 6579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (41927263 / 125000000) ≤ -Real.log (3661 / 5120) ∧
    -Real.log (3661 / 5120) ≤ (67083621 / 200000000) := by
  have h := checkLog_sound (w := (1459 / 8781)) (n := 12)
    (lo := (41927263 / 125000000)) (hi := (67083621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3661) = 1/(3661 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-67083621 / 200000000) (-41927263 / 125000000) (Real.log (3661 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (125136109 / 500000000) ≤ -Real.log (320 / 411) ∧
    -Real.log (320 / 411) ≤ (250272219 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 731)) (n := 12)
    (lo := (125136109 / 500000000)) (hi := (250272219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411 / 320) = 1/(320 / 411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (125136109 / 500000000) (250272219 / 1000000000) (Real.log (411 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (411 / 320) = -Real.log (320 / 411) := by
    rw [show ((411 / 320) : ℝ) = ((320 / 411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20912437 / 62500000) ≤ -Real.log (229 / 320) ∧
    -Real.log (229 / 320) ≤ (334598993 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 549)) (n := 12)
    (lo := (20912437 / 62500000)) (hi := (334598993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 229) = 1/(229 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-334598993 / 1000000000) (-20912437 / 62500000) (Real.log (229 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7047279 / 15625000) ≤ -Real.log (2560 / 4019) ∧
    -Real.log (2560 / 4019) ≤ (451025857 / 1000000000) := by
  have h := checkLog_sound (w := (1459 / 6579)) (n := 12)
    (lo := (7047279 / 15625000)) (hi := (451025857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4019 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4019 / 2560) = 1/(2560 / 4019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7047279 / 15625000) (451025857 / 1000000000) (Real.log (4019 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4019 / 2560) = -Real.log (2560 / 4019) := by
    rw [show ((4019 / 2560) : ℝ) = ((2560 / 4019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2109471 / 2500000) ≤ -Real.log (1101 / 2560) ∧
    -Real.log (1101 / 2560) ≤ (421894201 / 500000000) := by
  have h := checkLog_sound (w := (179 / 2381)) (n := 12)
    (lo := (7532061 / 50000000)) (hi := (150641221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1101) = 1/(1101 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-421894201 / 500000000) (-2109471 / 2500000) (Real.log (1101 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (450279123 / 1000000000) ≤ -Real.log (160 / 251) ∧
    -Real.log (160 / 251) ≤ (112569781 / 250000000) := by
  have h := checkLog_sound (w := (91 / 411)) (n := 12)
    (lo := (450279123 / 1000000000)) (hi := (112569781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251 / 160) = 1/(160 / 251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (450279123 / 1000000000) (112569781 / 250000000) (Real.log (251 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (251 / 160) = -Real.log (160 / 251) := by
    rw [show ((251 / 160) : ℝ) = ((160 / 251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (84106731 / 100000000) ≤ -Real.log (69 / 160) ∧
    -Real.log (69 / 160) ≤ (52566707 / 62500000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 69) = 1/(69 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-52566707 / 62500000) (-84106731 / 100000000) (Real.log (69 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (171253779 / 500000000) ≤ -Real.log (40000 / 56339) ∧
    -Real.log (40000 / 56339) ≤ (342507559 / 1000000000) := by
  have h := checkLog_sound (w := (16339 / 96339)) (n := 12)
    (lo := (171253779 / 500000000)) (hi := (342507559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56339 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56339 / 40000) = 1/(40000 / 56339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (171253779 / 500000000) (342507559 / 1000000000) (Real.log (56339 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (56339 / 40000) = -Real.log (40000 / 56339) := by
    rw [show ((56339 / 40000) : ℝ) = ((40000 / 56339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (525051331 / 1000000000) ≤ -Real.log (23661 / 40000) ∧
    -Real.log (23661 / 40000) ≤ (131262833 / 250000000) := by
  have h := checkLog_sound (w := (16339 / 63661)) (n := 12)
    (lo := (525051331 / 1000000000)) (hi := (131262833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 23661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 23661) = 1/(23661 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-131262833 / 250000000) (-525051331 / 1000000000) (Real.log (23661 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171563593 / 500000000) ≤ -Real.log (250000 / 352337) ∧
    -Real.log (250000 / 352337) ≤ (343127187 / 1000000000) := by
  have h := checkLog_sound (w := (102337 / 602337)) (n := 12)
    (lo := (171563593 / 500000000)) (hi := (343127187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352337 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352337 / 250000) = 1/(250000 / 352337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171563593 / 500000000) (343127187 / 1000000000) (Real.log (352337 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (352337 / 250000) = -Real.log (250000 / 352337) := by
    rw [show ((352337 / 250000) : ℝ) = ((250000 / 352337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (526528267 / 1000000000) ≤ -Real.log (147663 / 250000) ∧
    -Real.log (147663 / 250000) ≤ (131632067 / 250000000) := by
  have h := checkLog_sound (w := (102337 / 397663)) (n := 12)
    (lo := (526528267 / 1000000000)) (hi := (131632067 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 147663) = 1/(147663 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-131632067 / 250000000) (-526528267 / 1000000000) (Real.log (147663 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (132257897 / 500000000) ≤ -Real.log (2500 / 3257) ∧
    -Real.log (2500 / 3257) ≤ (52903159 / 200000000) := by
  have h := checkLog_sound (w := (757 / 5757)) (n := 12)
    (lo := (132257897 / 500000000)) (hi := (52903159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3257 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3257 / 2500) = 1/(2500 / 3257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (132257897 / 500000000) (52903159 / 200000000) (Real.log (3257 / 2500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (3257 / 2500) = -Real.log (2500 / 3257) := by
    rw [show ((3257 / 2500) : ℝ) = ((2500 / 3257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (72136593 / 200000000) ≤ -Real.log (1743 / 2500) ∧
    -Real.log (1743 / 2500) ≤ (180341483 / 500000000) := by
  have h := checkLog_sound (w := (757 / 4243)) (n := 12)
    (lo := (72136593 / 200000000)) (hi := (180341483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1743) = 1/(1743 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-180341483 / 500000000) (-72136593 / 200000000) (Real.log (1743 / 2500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (132530313 / 500000000) ≤ -Real.log (100000 / 130351) ∧
    -Real.log (100000 / 130351) ≤ (265060627 / 1000000000) := by
  have h := checkLog_sound (w := (30351 / 230351)) (n := 12)
    (lo := (132530313 / 500000000)) (hi := (265060627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130351 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130351 / 100000) = 1/(100000 / 130351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (132530313 / 500000000) (265060627 / 1000000000) (Real.log (130351 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (130351 / 100000) = -Real.log (100000 / 130351) := by
    rw [show ((130351 / 100000) : ℝ) = ((100000 / 130351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (361701843 / 1000000000) ≤ -Real.log (69649 / 100000) ∧
    -Real.log (69649 / 100000) ≤ (90425461 / 250000000) := by
  have h := checkLog_sound (w := (30351 / 169649)) (n := 12)
    (lo := (361701843 / 1000000000)) (hi := (90425461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 69649) = 1/(69649 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-90425461 / 250000000) (-361701843 / 1000000000) (Real.log (69649 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (867558889 / 1000000000) ≤ -Real.log (1250000000 / 2976364059) ∧
    -Real.log (1250000000 / 2976364059) ≤ (867558891 / 1000000000) := by
  have h := checkLog_sound (w := (476364059 / 5476364059)) (n := 12)
    (lo := (174411709 / 1000000000)) (hi := (17441171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2976364059 / 2500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2976364059 / 2500000000) = 1/(1250000000 / 2976364059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (867558889 / 1000000000) (867558891 / 1000000000) (Real.log (2976364059 / 1250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2976364059 / 1250000000) = -Real.log (1250000000 / 2976364059) := by
    rw [show ((2976364059 / 1250000000) : ℝ) = ((1250000000 / 2976364059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (869655453 / 1000000000) ≤ -Real.log (500000000000 / 1193044296811) ∧
    -Real.log (500000000000 / 1193044296811) ≤ (173931091 / 200000000) := by
  have h := checkLog_sound (w := (193044296811 / 2193044296811)) (n := 12)
    (lo := (176508273 / 1000000000)) (hi := (88254137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193044296811 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1193044296811 / 1000000000000) = 1/(500000000000 / 1193044296811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (869655453 / 1000000000) (173931091 / 200000000) (Real.log (1193044296811 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1193044296811 / 500000000000) = -Real.log (500000000000 / 1193044296811) := by
    rw [show ((1193044296811 / 500000000000) : ℝ) = ((500000000000 / 1193044296811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (625198759 / 1000000000) ≤ -Real.log (62500000000 / 116788582903) ∧
    -Real.log (62500000000 / 116788582903) ≤ (15629969 / 25000000) := by
  have h := checkLog_sound (w := (54288582903 / 179288582903)) (n := 12)
    (lo := (625198759 / 1000000000)) (hi := (15629969 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116788582903 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116788582903 / 62500000000) = 1/(62500000000 / 116788582903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (625198759 / 1000000000) (15629969 / 25000000) (Real.log (116788582903 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (116788582903 / 62500000000) = -Real.log (62500000000 / 116788582903) := by
    rw [show ((116788582903 / 62500000000) : ℝ) = ((62500000000 / 116788582903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (626762469 / 1000000000) ≤ -Real.log (500000000000 / 935770793551) ∧
    -Real.log (500000000000 / 935770793551) ≤ (62676247 / 100000000) := by
  have h := checkLog_sound (w := (435770793551 / 1435770793551)) (n := 12)
    (lo := (626762469 / 1000000000)) (hi := (62676247 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935770793551 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935770793551 / 500000000000) = 1/(500000000000 / 935770793551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (626762469 / 1000000000) (62676247 / 100000000) (Real.log (935770793551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (935770793551 / 500000000000) = -Real.log (500000000000 / 935770793551) := by
    rw [show ((935770793551 / 500000000000) : ℝ) = ((500000000000 / 935770793551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0233

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0234Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0234
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

theorem reflection_log_1_neg : (125136109 / 500000000) ≤ -Real.log (320 / 411) ∧
    -Real.log (320 / 411) ≤ (250272219 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 731)) (n := 12)
    (lo := (125136109 / 500000000)) (hi := (250272219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411 / 320) = 1/(320 / 411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (125136109 / 500000000) (250272219 / 1000000000) (Real.log (411 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (411 / 320) = -Real.log (320 / 411) := by
    rw [show ((411 / 320) : ℝ) = ((320 / 411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20912437 / 62500000) ≤ -Real.log (229 / 320) ∧
    -Real.log (229 / 320) ≤ (334598993 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 549)) (n := 12)
    (lo := (20912437 / 62500000)) (hi := (334598993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 229) = 1/(229 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-334598993 / 1000000000) (-20912437 / 62500000) (Real.log (229 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24981591 / 100000000) ≤ -Real.log (5120 / 6573) ∧
    -Real.log (5120 / 6573) ≤ (249815911 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 11693)) (n := 12)
    (lo := (24981591 / 100000000)) (hi := (249815911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6573 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6573 / 5120) = 1/(5120 / 6573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24981591 / 100000000) (249815911 / 1000000000) (Real.log (6573 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6573 / 5120) = -Real.log (5120 / 6573) := by
    rw [show ((6573 / 5120) : ℝ) = ((5120 / 6573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (333780549 / 1000000000) ≤ -Real.log (3667 / 5120) ∧
    -Real.log (3667 / 5120) ≤ (6675611 / 20000000) := by
  have h := checkLog_sound (w := (1453 / 8787)) (n := 12)
    (lo := (333780549 / 1000000000)) (hi := (6675611 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3667) = 1/(3667 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6675611 / 20000000) (-333780549 / 1000000000) (Real.log (3667 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (450279123 / 1000000000) ≤ -Real.log (160 / 251) ∧
    -Real.log (160 / 251) ≤ (112569781 / 250000000) := by
  have h := checkLog_sound (w := (91 / 411)) (n := 12)
    (lo := (450279123 / 1000000000)) (hi := (112569781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251 / 160) = 1/(160 / 251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (450279123 / 1000000000) (112569781 / 250000000) (Real.log (251 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (251 / 160) = -Real.log (160 / 251) := by
    rw [show ((251 / 160) : ℝ) = ((160 / 251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (84106731 / 100000000) ≤ -Real.log (69 / 160) ∧
    -Real.log (69 / 160) ≤ (52566707 / 62500000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 69) = 1/(69 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-52566707 / 62500000) (-84106731 / 100000000) (Real.log (69 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (56191479 / 125000000) ≤ -Real.log (2560 / 4013) ∧
    -Real.log (2560 / 4013) ≤ (449531833 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 6573)) (n := 12)
    (lo := (56191479 / 125000000)) (hi := (449531833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4013 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4013 / 2560) = 1/(2560 / 4013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (56191479 / 125000000) (449531833 / 1000000000) (Real.log (4013 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4013 / 2560) = -Real.log (2560 / 4013) := by
    rw [show ((4013 / 2560) : ℝ) = ((2560 / 4013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (209588401 / 250000000) ≤ -Real.log (1107 / 2560) ∧
    -Real.log (1107 / 2560) ≤ (419176803 / 500000000) := by
  have h := checkLog_sound (w := (173 / 2387)) (n := 12)
    (lo := (18150803 / 125000000)) (hi := (5808257 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1107) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1107) = 1/(1107 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-419176803 / 500000000) (-209588401 / 250000000) (Real.log (1107 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341888257 / 1000000000) ≤ -Real.log (1000000 / 1407603) ∧
    -Real.log (1000000 / 1407603) ≤ (170944129 / 500000000) := by
  have h := checkLog_sound (w := (407603 / 2407603)) (n := 12)
    (lo := (341888257 / 1000000000)) (hi := (170944129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1407603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1407603 / 1000000) = 1/(1000000 / 1407603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341888257 / 1000000000) (170944129 / 500000000) (Real.log (1407603 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1407603 / 1000000) = -Real.log (1000000 / 1407603) := by
    rw [show ((1407603 / 1000000) : ℝ) = ((1000000 / 1407603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (26178913 / 50000000) ≤ -Real.log (592397 / 1000000) ∧
    -Real.log (592397 / 1000000) ≤ (523578261 / 1000000000) := by
  have h := checkLog_sound (w := (407603 / 1592397)) (n := 12)
    (lo := (26178913 / 50000000)) (hi := (523578261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 592397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 592397) = 1/(592397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-523578261 / 1000000000) (-26178913 / 50000000) (Real.log (592397 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (85627067 / 250000000) ≤ -Real.log (250000 / 352119) ∧
    -Real.log (250000 / 352119) ≤ (342508269 / 1000000000) := by
  have h := checkLog_sound (w := (102119 / 602119)) (n := 12)
    (lo := (85627067 / 250000000)) (hi := (342508269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352119 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352119 / 250000) = 1/(250000 / 352119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (85627067 / 250000000) (342508269 / 1000000000) (Real.log (352119 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (352119 / 250000) = -Real.log (250000 / 352119) := by
    rw [show ((352119 / 250000) : ℝ) = ((250000 / 352119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (525053021 / 1000000000) ≤ -Real.log (147881 / 250000) ∧
    -Real.log (147881 / 250000) ≤ (262526511 / 500000000) := by
  have h := checkLog_sound (w := (102119 / 397881)) (n := 12)
    (lo := (525053021 / 1000000000)) (hi := (262526511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 147881) = 1/(147881 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-262526511 / 500000000) (-525053021 / 1000000000) (Real.log (147881 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (263972201 / 1000000000) ≤ -Real.log (250000 / 325523) ∧
    -Real.log (250000 / 325523) ≤ (131986101 / 500000000) := by
  have h := checkLog_sound (w := (75523 / 575523)) (n := 12)
    (lo := (263972201 / 1000000000)) (hi := (131986101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325523 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325523 / 250000) = 1/(250000 / 325523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (263972201 / 1000000000) (131986101 / 500000000) (Real.log (325523 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (325523 / 250000) = -Real.log (250000 / 325523) := by
    rw [show ((325523 / 250000) : ℝ) = ((250000 / 325523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (35966799 / 100000000) ≤ -Real.log (174477 / 250000) ∧
    -Real.log (174477 / 250000) ≤ (359667991 / 1000000000) := by
  have h := checkLog_sound (w := (75523 / 424477)) (n := 12)
    (lo := (35966799 / 100000000)) (hi := (359667991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 174477) = 1/(174477 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-359667991 / 1000000000) (-35966799 / 100000000) (Real.log (174477 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (264516561 / 1000000000) ≤ -Real.log (1000000 / 1302801) ∧
    -Real.log (1000000 / 1302801) ≤ (132258281 / 500000000) := by
  have h := checkLog_sound (w := (302801 / 2302801)) (n := 12)
    (lo := (264516561 / 1000000000)) (hi := (132258281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302801 / 1000000) = 1/(1000000 / 1302801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (264516561 / 1000000000) (132258281 / 500000000) (Real.log (1302801 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1302801 / 1000000) = -Real.log (1000000 / 1302801) := by
    rw [show ((1302801 / 1000000) : ℝ) = ((1000000 / 1302801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (360684399 / 1000000000) ≤ -Real.log (697199 / 1000000) ∧
    -Real.log (697199 / 1000000) ≤ (901711 / 2500000) := by
  have h := checkLog_sound (w := (302801 / 1697199)) (n := 12)
    (lo := (360684399 / 1000000000)) (hi := (901711 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697199) = 1/(697199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-901711 / 2500000) (-360684399 / 1000000000) (Real.log (697199 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (865466517 / 1000000000) ≤ -Real.log (500000000000 / 1188057164367) ∧
    -Real.log (500000000000 / 1188057164367) ≤ (865466519 / 1000000000) := by
  have h := checkLog_sound (w := (188057164367 / 2188057164367)) (n := 12)
    (lo := (172319337 / 1000000000)) (hi := (86159669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188057164367 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1188057164367 / 1000000000000) = 1/(500000000000 / 1188057164367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (865466517 / 1000000000) (865466519 / 1000000000) (Real.log (1188057164367 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1188057164367 / 500000000000) = -Real.log (500000000000 / 1188057164367) := by
    rw [show ((1188057164367 / 500000000000) : ℝ) = ((500000000000 / 1188057164367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (867561289 / 1000000000) ≤ -Real.log (10000000000 / 23810969631) ∧
    -Real.log (10000000000 / 23810969631) ≤ (867561291 / 1000000000) := by
  have h := checkLog_sound (w := (3810969631 / 43810969631)) (n := 12)
    (lo := (174414109 / 1000000000)) (hi := (17441411 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23810969631 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(23810969631 / 20000000000) = 1/(10000000000 / 23810969631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (867561289 / 1000000000) (867561291 / 1000000000) (Real.log (23810969631 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23810969631 / 10000000000) = -Real.log (10000000000 / 23810969631) := by
    rw [show ((23810969631 / 10000000000) : ℝ) = ((10000000000 / 23810969631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (623640191 / 1000000000) ≤ -Real.log (500000000000 / 932853613943) ∧
    -Real.log (500000000000 / 932853613943) ≤ (4872189 / 7812500) := by
  have h := checkLog_sound (w := (432853613943 / 1432853613943)) (n := 12)
    (lo := (623640191 / 1000000000)) (hi := (4872189 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((932853613943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(932853613943 / 500000000000) = 1/(500000000000 / 932853613943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (623640191 / 1000000000) (4872189 / 7812500) (Real.log (932853613943 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (932853613943 / 500000000000) = -Real.log (500000000000 / 932853613943) := by
    rw [show ((932853613943 / 500000000000) : ℝ) = ((500000000000 / 932853613943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (625200961 / 1000000000) ≤ -Real.log (500000000000 / 934310720469) ∧
    -Real.log (500000000000 / 934310720469) ≤ (312600481 / 500000000) := by
  have h := checkLog_sound (w := (434310720469 / 1434310720469)) (n := 12)
    (lo := (625200961 / 1000000000)) (hi := (312600481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((934310720469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(934310720469 / 500000000000) = 1/(500000000000 / 934310720469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (625200961 / 1000000000) (312600481 / 500000000) (Real.log (934310720469 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (934310720469 / 500000000000) = -Real.log (500000000000 / 934310720469) := by
    rw [show ((934310720469 / 500000000000) : ℝ) = ((500000000000 / 934310720469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0234

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0235Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0235
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

theorem reflection_log_1_neg : (24981591 / 100000000) ≤ -Real.log (5120 / 6573) ∧
    -Real.log (5120 / 6573) ≤ (249815911 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 11693)) (n := 12)
    (lo := (24981591 / 100000000)) (hi := (249815911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6573 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6573 / 5120) = 1/(5120 / 6573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24981591 / 100000000) (249815911 / 1000000000) (Real.log (6573 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6573 / 5120) = -Real.log (5120 / 6573) := by
    rw [show ((6573 / 5120) : ℝ) = ((5120 / 6573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (333780549 / 1000000000) ≤ -Real.log (3667 / 5120) ∧
    -Real.log (3667 / 5120) ≤ (6675611 / 20000000) := by
  have h := checkLog_sound (w := (1453 / 8787)) (n := 12)
    (lo := (333780549 / 1000000000)) (hi := (6675611 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3667) = 1/(3667 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6675611 / 20000000) (-333780549 / 1000000000) (Real.log (3667 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (249359393 / 1000000000) ≤ -Real.log (512 / 657) ∧
    -Real.log (512 / 657) ≤ (124679697 / 500000000) := by
  have h := checkLog_sound (w := (145 / 1169)) (n := 12)
    (lo := (249359393 / 1000000000)) (hi := (124679697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657 / 512) = 1/(512 / 657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (249359393 / 1000000000) (124679697 / 500000000) (Real.log (657 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (657 / 512) = -Real.log (512 / 657) := by
    rw [show ((657 / 512) : ℝ) = ((512 / 657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (41620347 / 125000000) ≤ -Real.log (367 / 512) ∧
    -Real.log (367 / 512) ≤ (332962777 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 879)) (n := 12)
    (lo := (41620347 / 125000000)) (hi := (332962777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 367) = 1/(367 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-332962777 / 1000000000) (-41620347 / 125000000) (Real.log (367 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (56191479 / 125000000) ≤ -Real.log (2560 / 4013) ∧
    -Real.log (2560 / 4013) ≤ (449531833 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 6573)) (n := 12)
    (lo := (56191479 / 125000000)) (hi := (449531833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4013 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4013 / 2560) = 1/(2560 / 4013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (56191479 / 125000000) (449531833 / 1000000000) (Real.log (4013 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4013 / 2560) = -Real.log (2560 / 4013) := by
    rw [show ((4013 / 2560) : ℝ) = ((2560 / 4013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (209588401 / 250000000) ≤ -Real.log (1107 / 2560) ∧
    -Real.log (1107 / 2560) ≤ (419176803 / 500000000) := by
  have h := checkLog_sound (w := (173 / 2387)) (n := 12)
    (lo := (18150803 / 125000000)) (hi := (5808257 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1107) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1107) = 1/(1107 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-419176803 / 500000000) (-209588401 / 250000000) (Real.log (1107 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (224391991 / 500000000) ≤ -Real.log (256 / 401) ∧
    -Real.log (256 / 401) ≤ (448783983 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 657)) (n := 12)
    (lo := (224391991 / 500000000)) (hi := (448783983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401 / 256) = 1/(256 / 401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (224391991 / 500000000) (448783983 / 1000000000) (Real.log (401 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (401 / 256) = -Real.log (256 / 401) := by
    rw [show ((401 / 256) : ℝ) = ((256 / 401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (417823621 / 500000000) ≤ -Real.log (111 / 256) ∧
    -Real.log (111 / 256) ≤ (208911811 / 250000000) := by
  have h := checkLog_sound (w := (17 / 239)) (n := 12)
    (lo := (71250031 / 500000000)) (hi := (142500063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 111) = 1/(111 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-208911811 / 250000000) (-417823621 / 500000000) (Real.log (111 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85317143 / 250000000) ≤ -Real.log (1000000 / 1406731) ∧
    -Real.log (1000000 / 1406731) ≤ (341268573 / 1000000000) := by
  have h := checkLog_sound (w := (406731 / 2406731)) (n := 12)
    (lo := (85317143 / 250000000)) (hi := (341268573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1406731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1406731 / 1000000) = 1/(1000000 / 1406731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85317143 / 250000000) (341268573 / 1000000000) (Real.log (1406731 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1406731 / 1000000) = -Real.log (1000000 / 1406731) := by
    rw [show ((1406731 / 1000000) : ℝ) = ((1000000 / 1406731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (522107357 / 1000000000) ≤ -Real.log (593269 / 1000000) ∧
    -Real.log (593269 / 1000000) ≤ (261053679 / 500000000) := by
  have h := checkLog_sound (w := (406731 / 1593269)) (n := 12)
    (lo := (522107357 / 1000000000)) (hi := (261053679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 593269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 593269) = 1/(593269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-261053679 / 500000000) (-522107357 / 1000000000) (Real.log (593269 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42736121 / 125000000) ≤ -Real.log (250000 / 351901) ∧
    -Real.log (250000 / 351901) ≤ (341888969 / 1000000000) := by
  have h := checkLog_sound (w := (101901 / 601901)) (n := 12)
    (lo := (42736121 / 125000000)) (hi := (341888969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351901 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351901 / 250000) = 1/(250000 / 351901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42736121 / 125000000) (341888969 / 1000000000) (Real.log (351901 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (351901 / 250000) = -Real.log (250000 / 351901) := by
    rw [show ((351901 / 250000) : ℝ) = ((250000 / 351901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (130894987 / 250000000) ≤ -Real.log (148099 / 250000) ∧
    -Real.log (148099 / 250000) ≤ (523579949 / 1000000000) := by
  have h := checkLog_sound (w := (101901 / 398099)) (n := 12)
    (lo := (130894987 / 250000000)) (hi := (523579949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 148099) = 1/(148099 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-523579949 / 1000000000) (-130894987 / 250000000) (Real.log (148099 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (263428313 / 1000000000) ≤ -Real.log (125000 / 162673) ∧
    -Real.log (125000 / 162673) ≤ (131714157 / 500000000) := by
  have h := checkLog_sound (w := (37673 / 287673)) (n := 12)
    (lo := (263428313 / 1000000000)) (hi := (131714157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162673 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162673 / 125000) = 1/(125000 / 162673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (263428313 / 1000000000) (131714157 / 500000000) (Real.log (162673 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (162673 / 125000) = -Real.log (125000 / 162673) := by
    rw [show ((162673 / 125000) : ℝ) = ((125000 / 162673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (358654043 / 1000000000) ≤ -Real.log (87327 / 125000) ∧
    -Real.log (87327 / 125000) ≤ (89663511 / 250000000) := by
  have h := checkLog_sound (w := (37673 / 212327)) (n := 12)
    (lo := (358654043 / 1000000000)) (hi := (89663511 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 87327) = 1/(87327 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-89663511 / 250000000) (-358654043 / 1000000000) (Real.log (87327 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (263972969 / 1000000000) ≤ -Real.log (1000000 / 1302093) ∧
    -Real.log (1000000 / 1302093) ≤ (26397297 / 100000000) := by
  have h := checkLog_sound (w := (302093 / 2302093)) (n := 12)
    (lo := (263972969 / 1000000000)) (hi := (26397297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302093 / 1000000) = 1/(1000000 / 1302093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (263972969 / 1000000000) (26397297 / 100000000) (Real.log (1302093 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1302093 / 1000000) = -Real.log (1000000 / 1302093) := by
    rw [show ((1302093 / 1000000) : ℝ) = ((1000000 / 1302093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (179834711 / 500000000) ≤ -Real.log (697907 / 1000000) ∧
    -Real.log (697907 / 1000000) ≤ (359669423 / 1000000000) := by
  have h := checkLog_sound (w := (302093 / 1697907)) (n := 12)
    (lo := (179834711 / 500000000)) (hi := (359669423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697907) = 1/(697907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-359669423 / 1000000000) (-179834711 / 500000000) (Real.log (697907 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (863375929 / 1000000000) ≤ -Real.log (500000000000 / 1185576020321) ∧
    -Real.log (500000000000 / 1185576020321) ≤ (863375931 / 1000000000) := by
  have h := checkLog_sound (w := (185576020321 / 2185576020321)) (n := 12)
    (lo := (170228749 / 1000000000)) (hi := (136183 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185576020321 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1185576020321 / 1000000000000) = 1/(500000000000 / 1185576020321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (863375929 / 1000000000) (863375931 / 1000000000) (Real.log (1185576020321 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1185576020321 / 500000000000) = -Real.log (500000000000 / 1185576020321) := by
    rw [show ((1185576020321 / 500000000000) : ℝ) = ((500000000000 / 1185576020321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (216367229 / 250000000) ≤ -Real.log (50000000000 / 118806001391) ∧
    -Real.log (50000000000 / 118806001391) ≤ (432734459 / 500000000) := by
  have h := checkLog_sound (w := (18806001391 / 218806001391)) (n := 12)
    (lo := (21540217 / 125000000)) (hi := (172321737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118806001391 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118806001391 / 100000000000) = 1/(50000000000 / 118806001391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (216367229 / 250000000) (432734459 / 500000000) (Real.log (118806001391 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (118806001391 / 50000000000) = -Real.log (50000000000 / 118806001391) := by
    rw [show ((118806001391 / 50000000000) : ℝ) = ((50000000000 / 118806001391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (622082357 / 1000000000) ≤ -Real.log (10000000000 / 18628030277) ∧
    -Real.log (10000000000 / 18628030277) ≤ (311041179 / 500000000) := by
  have h := checkLog_sound (w := (8628030277 / 28628030277)) (n := 12)
    (lo := (622082357 / 1000000000)) (hi := (311041179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18628030277 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18628030277 / 10000000000) = 1/(10000000000 / 18628030277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (622082357 / 1000000000) (311041179 / 500000000) (Real.log (18628030277 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (18628030277 / 10000000000) = -Real.log (10000000000 / 18628030277) := by
    rw [show ((18628030277 / 10000000000) : ℝ) = ((10000000000 / 18628030277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (77955299 / 125000000) ≤ -Real.log (62500000000 / 116606958377) ∧
    -Real.log (62500000000 / 116606958377) ≤ (623642393 / 1000000000) := by
  have h := checkLog_sound (w := (54106958377 / 179106958377)) (n := 12)
    (lo := (77955299 / 125000000)) (hi := (623642393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116606958377 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116606958377 / 62500000000) = 1/(62500000000 / 116606958377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (77955299 / 125000000) (623642393 / 1000000000) (Real.log (116606958377 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (116606958377 / 62500000000) = -Real.log (62500000000 / 116606958377) := by
    rw [show ((116606958377 / 62500000000) : ℝ) = ((62500000000 / 116606958377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0235

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0236Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0236
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

theorem reflection_log_1_neg : (249359393 / 1000000000) ≤ -Real.log (512 / 657) ∧
    -Real.log (512 / 657) ≤ (124679697 / 500000000) := by
  have h := checkLog_sound (w := (145 / 1169)) (n := 12)
    (lo := (249359393 / 1000000000)) (hi := (124679697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657 / 512) = 1/(512 / 657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (249359393 / 1000000000) (124679697 / 500000000) (Real.log (657 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (657 / 512) = -Real.log (512 / 657) := by
    rw [show ((657 / 512) : ℝ) = ((512 / 657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (41620347 / 125000000) ≤ -Real.log (367 / 512) ∧
    -Real.log (367 / 512) ≤ (332962777 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 879)) (n := 12)
    (lo := (41620347 / 125000000)) (hi := (332962777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 367) = 1/(367 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-332962777 / 1000000000) (-41620347 / 125000000) (Real.log (367 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62225667 / 250000000) ≤ -Real.log (5120 / 6567) ∧
    -Real.log (5120 / 6567) ≤ (248902669 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 11687)) (n := 12)
    (lo := (62225667 / 250000000)) (hi := (248902669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6567 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6567 / 5120) = 1/(5120 / 6567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62225667 / 250000000) (248902669 / 1000000000) (Real.log (6567 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6567 / 5120) = -Real.log (5120 / 6567) := by
    rw [show ((6567 / 5120) : ℝ) = ((5120 / 6567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (41518209 / 125000000) ≤ -Real.log (3673 / 5120) ∧
    -Real.log (3673 / 5120) ≤ (332145673 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 8793)) (n := 12)
    (lo := (41518209 / 125000000)) (hi := (332145673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3673) = 1/(3673 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-332145673 / 1000000000) (-41518209 / 125000000) (Real.log (3673 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (224391991 / 500000000) ≤ -Real.log (256 / 401) ∧
    -Real.log (256 / 401) ≤ (448783983 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 657)) (n := 12)
    (lo := (224391991 / 500000000)) (hi := (448783983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401 / 256) = 1/(256 / 401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (224391991 / 500000000) (448783983 / 1000000000) (Real.log (401 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (401 / 256) = -Real.log (256 / 401) := by
    rw [show ((401 / 256) : ℝ) = ((256 / 401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (417823621 / 500000000) ≤ -Real.log (111 / 256) ∧
    -Real.log (111 / 256) ≤ (208911811 / 250000000) := by
  have h := checkLog_sound (w := (17 / 239)) (n := 12)
    (lo := (71250031 / 500000000)) (hi := (142500063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 111) = 1/(111 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-208911811 / 250000000) (-417823621 / 500000000) (Real.log (111 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (448035573 / 1000000000) ≤ -Real.log (2560 / 4007) ∧
    -Real.log (2560 / 4007) ≤ (224017787 / 500000000) := by
  have h := checkLog_sound (w := (1447 / 6567)) (n := 12)
    (lo := (448035573 / 1000000000)) (hi := (224017787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4007 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4007 / 2560) = 1/(2560 / 4007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (448035573 / 1000000000) (224017787 / 500000000) (Real.log (4007 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4007 / 2560) = -Real.log (2560 / 4007) := by
    rw [show ((4007 / 2560) : ℝ) = ((2560 / 4007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (166589637 / 200000000) ≤ -Real.log (1113 / 2560) ∧
    -Real.log (1113 / 2560) ≤ (832948187 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 2393)) (n := 12)
    (lo := (27960201 / 200000000)) (hi := (69900503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1113) = 1/(1113 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-832948187 / 1000000000) (-166589637 / 200000000) (Real.log (1113 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340648503 / 1000000000) ≤ -Real.log (1000000 / 1405859) ∧
    -Real.log (1000000 / 1405859) ≤ (42581063 / 125000000) := by
  have h := checkLog_sound (w := (405859 / 2405859)) (n := 12)
    (lo := (340648503 / 1000000000)) (hi := (42581063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1405859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1405859 / 1000000) = 1/(1000000 / 1405859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340648503 / 1000000000) (42581063 / 125000000) (Real.log (1405859 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1405859 / 1000000) = -Real.log (1000000 / 1405859) := by
    rw [show ((1405859 / 1000000) : ℝ) = ((1000000 / 1405859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (260319307 / 500000000) ≤ -Real.log (594141 / 1000000) ∧
    -Real.log (594141 / 1000000) ≤ (104127723 / 200000000) := by
  have h := checkLog_sound (w := (405859 / 1594141)) (n := 12)
    (lo := (260319307 / 500000000)) (hi := (104127723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 594141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 594141) = 1/(594141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-104127723 / 200000000) (-260319307 / 500000000) (Real.log (594141 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341269283 / 1000000000) ≤ -Real.log (250000 / 351683) ∧
    -Real.log (250000 / 351683) ≤ (85317321 / 250000000) := by
  have h := checkLog_sound (w := (101683 / 601683)) (n := 12)
    (lo := (341269283 / 1000000000)) (hi := (85317321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351683 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351683 / 250000) = 1/(250000 / 351683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341269283 / 1000000000) (85317321 / 250000000) (Real.log (351683 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (351683 / 250000) = -Real.log (250000 / 351683) := by
    rw [show ((351683 / 250000) : ℝ) = ((250000 / 351683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (261054521 / 500000000) ≤ -Real.log (148317 / 250000) ∧
    -Real.log (148317 / 250000) ≤ (522109043 / 1000000000) := by
  have h := checkLog_sound (w := (101683 / 398317)) (n := 12)
    (lo := (261054521 / 500000000)) (hi := (522109043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 148317) = 1/(148317 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-522109043 / 1000000000) (-261054521 / 500000000) (Real.log (148317 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (262884129 / 1000000000) ≤ -Real.log (250000 / 325169) ∧
    -Real.log (250000 / 325169) ≤ (26288413 / 100000000) := by
  have h := checkLog_sound (w := (75169 / 575169)) (n := 12)
    (lo := (262884129 / 1000000000)) (hi := (26288413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325169 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325169 / 250000) = 1/(250000 / 325169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (262884129 / 1000000000) (26288413 / 100000000) (Real.log (325169 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (325169 / 250000) = -Real.log (250000 / 325169) := by
    rw [show ((325169 / 250000) : ℝ) = ((250000 / 325169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (89410281 / 250000000) ≤ -Real.log (174831 / 250000) ∧
    -Real.log (174831 / 250000) ≤ (2861129 / 8000000) := by
  have h := checkLog_sound (w := (75169 / 424831)) (n := 12)
    (lo := (89410281 / 250000000)) (hi := (2861129 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 174831) = 1/(174831 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2861129 / 8000000) (-89410281 / 250000000) (Real.log (174831 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (263429081 / 1000000000) ≤ -Real.log (200000 / 260277) ∧
    -Real.log (200000 / 260277) ≤ (131714541 / 500000000) := by
  have h := checkLog_sound (w := (60277 / 460277)) (n := 12)
    (lo := (263429081 / 1000000000)) (hi := (131714541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260277 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(260277 / 200000) = 1/(200000 / 260277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (263429081 / 1000000000) (131714541 / 500000000) (Real.log (260277 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (260277 / 200000) = -Real.log (200000 / 260277) := by
    rw [show ((260277 / 200000) : ℝ) = ((200000 / 260277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (14346219 / 40000000) ≤ -Real.log (139723 / 200000) ∧
    -Real.log (139723 / 200000) ≤ (89663869 / 250000000) := by
  have h := checkLog_sound (w := (60277 / 339723)) (n := 12)
    (lo := (14346219 / 40000000)) (hi := (89663869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 139723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 139723) = 1/(139723 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-89663869 / 250000000) (-14346219 / 40000000) (Real.log (139723 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (861287117 / 1000000000) ≤ -Real.log (500000000000 / 1183102159251) ∧
    -Real.log (500000000000 / 1183102159251) ≤ (861287119 / 1000000000) := by
  have h := checkLog_sound (w := (183102159251 / 2183102159251)) (n := 12)
    (lo := (168139937 / 1000000000)) (hi := (84069969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183102159251 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1183102159251 / 1000000000000) = 1/(500000000000 / 1183102159251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (861287117 / 1000000000) (861287119 / 1000000000) (Real.log (1183102159251 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1183102159251 / 500000000000) = -Real.log (500000000000 / 1183102159251) := by
    rw [show ((1183102159251 / 500000000000) : ℝ) = ((500000000000 / 1183102159251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (431689163 / 500000000) ≤ -Real.log (500000000000 / 1185578861493) ∧
    -Real.log (500000000000 / 1185578861493) ≤ (107922291 / 125000000) := by
  have h := checkLog_sound (w := (185578861493 / 2185578861493)) (n := 12)
    (lo := (85115573 / 500000000)) (hi := (170231147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185578861493 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1185578861493 / 1000000000000) = 1/(500000000000 / 1185578861493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (431689163 / 500000000) (107922291 / 125000000) (Real.log (1185578861493 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1185578861493 / 500000000000) = -Real.log (500000000000 / 1185578861493) := by
    rw [show ((1185578861493 / 500000000000) : ℝ) = ((500000000000 / 1185578861493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (310262627 / 500000000) ≤ -Real.log (500000000000 / 929952353987) ∧
    -Real.log (500000000000 / 929952353987) ≤ (124105051 / 200000000) := by
  have h := checkLog_sound (w := (429952353987 / 1429952353987)) (n := 12)
    (lo := (310262627 / 500000000)) (hi := (124105051 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929952353987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929952353987 / 500000000000) = 1/(500000000000 / 929952353987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (310262627 / 500000000) (124105051 / 200000000) (Real.log (929952353987 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (929952353987 / 500000000000) = -Real.log (500000000000 / 929952353987) := by
    rw [show ((929952353987 / 500000000000) : ℝ) = ((500000000000 / 929952353987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (622084557 / 1000000000) ≤ -Real.log (125000000000 / 232850890691) ∧
    -Real.log (125000000000 / 232850890691) ≤ (311042279 / 500000000) := by
  have h := checkLog_sound (w := (107850890691 / 357850890691)) (n := 12)
    (lo := (622084557 / 1000000000)) (hi := (311042279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232850890691 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(232850890691 / 125000000000) = 1/(125000000000 / 232850890691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (622084557 / 1000000000) (311042279 / 500000000) (Real.log (232850890691 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (232850890691 / 125000000000) = -Real.log (125000000000 / 232850890691) := by
    rw [show ((232850890691 / 125000000000) : ℝ) = ((125000000000 / 232850890691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0236

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0237Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0237
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

theorem reflection_log_1_neg : (62225667 / 250000000) ≤ -Real.log (5120 / 6567) ∧
    -Real.log (5120 / 6567) ≤ (248902669 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 11687)) (n := 12)
    (lo := (62225667 / 250000000)) (hi := (248902669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6567 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6567 / 5120) = 1/(5120 / 6567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62225667 / 250000000) (248902669 / 1000000000) (Real.log (6567 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6567 / 5120) = -Real.log (5120 / 6567) := by
    rw [show ((6567 / 5120) : ℝ) = ((5120 / 6567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (41518209 / 125000000) ≤ -Real.log (3673 / 5120) ∧
    -Real.log (3673 / 5120) ≤ (332145673 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 8793)) (n := 12)
    (lo := (41518209 / 125000000)) (hi := (332145673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3673) = 1/(3673 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-332145673 / 1000000000) (-41518209 / 125000000) (Real.log (3673 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (124222867 / 500000000) ≤ -Real.log (1280 / 1641) ∧
    -Real.log (1280 / 1641) ≤ (49689147 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2921)) (n := 12)
    (lo := (124222867 / 500000000)) (hi := (49689147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1641 / 1280) = 1/(1280 / 1641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (124222867 / 500000000) (49689147 / 200000000) (Real.log (1641 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1641 / 1280) = -Real.log (1280 / 1641) := by
    rw [show ((1641 / 1280) : ℝ) = ((1280 / 1641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (165664617 / 500000000) ≤ -Real.log (919 / 1280) ∧
    -Real.log (919 / 1280) ≤ (66265847 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2199)) (n := 12)
    (lo := (165664617 / 500000000)) (hi := (66265847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 919) = 1/(919 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-66265847 / 200000000) (-165664617 / 500000000) (Real.log (919 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (448035573 / 1000000000) ≤ -Real.log (2560 / 4007) ∧
    -Real.log (2560 / 4007) ≤ (224017787 / 500000000) := by
  have h := checkLog_sound (w := (1447 / 6567)) (n := 12)
    (lo := (448035573 / 1000000000)) (hi := (224017787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4007 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4007 / 2560) = 1/(2560 / 4007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (448035573 / 1000000000) (224017787 / 500000000) (Real.log (4007 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4007 / 2560) = -Real.log (2560 / 4007) := by
    rw [show ((4007 / 2560) : ℝ) = ((2560 / 4007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (166589637 / 200000000) ≤ -Real.log (1113 / 2560) ∧
    -Real.log (1113 / 2560) ≤ (832948187 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 2393)) (n := 12)
    (lo := (27960201 / 200000000)) (hi := (69900503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1113) = 1/(1113 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-832948187 / 1000000000) (-166589637 / 200000000) (Real.log (1113 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (223643301 / 500000000) ≤ -Real.log (640 / 1001) ∧
    -Real.log (640 / 1001) ≤ (447286603 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 1641)) (n := 12)
    (lo := (223643301 / 500000000)) (hi := (447286603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1001 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1001 / 640) = 1/(640 / 1001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (223643301 / 500000000) (447286603 / 1000000000) (Real.log (1001 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1001 / 640) = -Real.log (640 / 1001) := by
    rw [show ((1001 / 640) : ℝ) = ((640 / 1001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (830256393 / 1000000000) ≤ -Real.log (279 / 640) ∧
    -Real.log (279 / 640) ≤ (166051279 / 200000000) := by
  have h := checkLog_sound (w := (41 / 599)) (n := 12)
    (lo := (137109213 / 1000000000)) (hi := (68554607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 279) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 279) = 1/(279 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-166051279 / 200000000) (-830256393 / 1000000000) (Real.log (279 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340028761 / 1000000000) ≤ -Real.log (250000 / 351247) ∧
    -Real.log (250000 / 351247) ≤ (170014381 / 500000000) := by
  have h := checkLog_sound (w := (101247 / 601247)) (n := 12)
    (lo := (340028761 / 1000000000)) (hi := (170014381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351247 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351247 / 250000) = 1/(250000 / 351247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340028761 / 1000000000) (170014381 / 500000000) (Real.log (351247 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (351247 / 250000) = -Real.log (250000 / 351247) := by
    rw [show ((351247 / 250000) : ℝ) = ((250000 / 351247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (103834741 / 200000000) ≤ -Real.log (148753 / 250000) ∧
    -Real.log (148753 / 250000) ≤ (259586853 / 500000000) := by
  have h := checkLog_sound (w := (101247 / 398753)) (n := 12)
    (lo := (103834741 / 200000000)) (hi := (259586853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 148753) = 1/(148753 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-259586853 / 500000000) (-103834741 / 200000000) (Real.log (148753 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68129843 / 200000000) ≤ -Real.log (50000 / 70293) ∧
    -Real.log (50000 / 70293) ≤ (1330661 / 3906250) := by
  have h := checkLog_sound (w := (20293 / 120293)) (n := 12)
    (lo := (68129843 / 200000000)) (hi := (1330661 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70293 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70293 / 50000) = 1/(50000 / 70293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68129843 / 200000000) (1330661 / 3906250) (Real.log (70293 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (70293 / 50000) = -Real.log (50000 / 70293) := by
    rw [show ((70293 / 50000) : ℝ) = ((50000 / 70293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (520640297 / 1000000000) ≤ -Real.log (29707 / 50000) ∧
    -Real.log (29707 / 50000) ≤ (260320149 / 500000000) := by
  have h := checkLog_sound (w := (20293 / 79707)) (n := 12)
    (lo := (520640297 / 1000000000)) (hi := (260320149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 29707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 29707) = 1/(29707 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-260320149 / 500000000) (-520640297 / 1000000000) (Real.log (29707 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (262341187 / 1000000000) ≤ -Real.log (100000 / 129997) ∧
    -Real.log (100000 / 129997) ≤ (65585297 / 250000000) := by
  have h := checkLog_sound (w := (29997 / 229997)) (n := 12)
    (lo := (262341187 / 1000000000)) (hi := (65585297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129997 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(129997 / 100000) = 1/(100000 / 129997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (262341187 / 1000000000) (65585297 / 250000000) (Real.log (129997 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (129997 / 100000) = -Real.log (100000 / 129997) := by
    rw [show ((129997 / 100000) : ℝ) = ((100000 / 129997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (356632087 / 1000000000) ≤ -Real.log (70003 / 100000) ∧
    -Real.log (70003 / 100000) ≤ (44579011 / 125000000) := by
  have h := checkLog_sound (w := (29997 / 170003)) (n := 12)
    (lo := (356632087 / 1000000000)) (hi := (44579011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 70003) = 1/(70003 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-44579011 / 125000000) (-356632087 / 1000000000) (Real.log (70003 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (131442833 / 500000000) ≤ -Real.log (500000 / 650339) ∧
    -Real.log (500000 / 650339) ≤ (262885667 / 1000000000) := by
  have h := checkLog_sound (w := (150339 / 1150339)) (n := 12)
    (lo := (131442833 / 500000000)) (hi := (262885667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650339 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650339 / 500000) = 1/(500000 / 650339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (131442833 / 500000000) (262885667 / 1000000000) (Real.log (650339 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (650339 / 500000) = -Real.log (500000 / 650339) := by
    rw [show ((650339 / 500000) : ℝ) = ((500000 / 650339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (22352749 / 62500000) ≤ -Real.log (349661 / 500000) ∧
    -Real.log (349661 / 500000) ≤ (71528797 / 200000000) := by
  have h := checkLog_sound (w := (150339 / 849661)) (n := 12)
    (lo := (22352749 / 62500000)) (hi := (71528797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 349661) = 1/(349661 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-71528797 / 200000000) (-22352749 / 62500000) (Real.log (349661 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (429601233 / 500000000) ≤ -Real.log (500000000000 / 1180638373679) ∧
    -Real.log (500000000000 / 1180638373679) ≤ (214800617 / 250000000) := by
  have h := checkLog_sound (w := (180638373679 / 2180638373679)) (n := 12)
    (lo := (83027643 / 500000000)) (hi := (166055287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180638373679 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1180638373679 / 1000000000000) = 1/(500000000000 / 1180638373679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (429601233 / 500000000) (214800617 / 250000000) (Real.log (1180638373679 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1180638373679 / 500000000000) = -Real.log (500000000000 / 1180638373679) := by
    rw [show ((1180638373679 / 500000000000) : ℝ) = ((500000000000 / 1180638373679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (861289511 / 1000000000) ≤ -Real.log (50000000000 / 118310499209) ∧
    -Real.log (50000000000 / 118310499209) ≤ (861289513 / 1000000000) := by
  have h := checkLog_sound (w := (18310499209 / 218310499209)) (n := 12)
    (lo := (168142331 / 1000000000)) (hi := (42035583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118310499209 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118310499209 / 100000000000) = 1/(50000000000 / 118310499209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (861289511 / 1000000000) (861289513 / 1000000000) (Real.log (118310499209 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (118310499209 / 50000000000) = -Real.log (50000000000 / 118310499209) := by
    rw [show ((118310499209 / 50000000000) : ℝ) = ((50000000000 / 118310499209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (309486637 / 500000000) ≤ -Real.log (100000000000 / 185702041341) ∧
    -Real.log (100000000000 / 185702041341) ≤ (24758931 / 40000000) := by
  have h := checkLog_sound (w := (85702041341 / 285702041341)) (n := 12)
    (lo := (309486637 / 500000000)) (hi := (24758931 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185702041341 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185702041341 / 100000000000) = 1/(100000000000 / 185702041341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (309486637 / 500000000) (24758931 / 40000000) (Real.log (185702041341 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (185702041341 / 100000000000) = -Real.log (100000000000 / 185702041341) := by
    rw [show ((185702041341 / 100000000000) : ℝ) = ((100000000000 / 185702041341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (620529651 / 1000000000) ≤ -Real.log (500000000000 / 929956443527) ∧
    -Real.log (500000000000 / 929956443527) ≤ (155132413 / 250000000) := by
  have h := checkLog_sound (w := (429956443527 / 1429956443527)) (n := 12)
    (lo := (620529651 / 1000000000)) (hi := (155132413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929956443527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929956443527 / 500000000000) = 1/(500000000000 / 929956443527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (620529651 / 1000000000) (155132413 / 250000000) (Real.log (929956443527 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (929956443527 / 500000000000) = -Real.log (500000000000 / 929956443527) := by
    rw [show ((929956443527 / 500000000000) : ℝ) = ((500000000000 / 929956443527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0237

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0238Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0238
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

theorem reflection_log_1_neg : (124222867 / 500000000) ≤ -Real.log (1280 / 1641) ∧
    -Real.log (1280 / 1641) ≤ (49689147 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2921)) (n := 12)
    (lo := (124222867 / 500000000)) (hi := (49689147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1641 / 1280) = 1/(1280 / 1641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (124222867 / 500000000) (49689147 / 200000000) (Real.log (1641 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1641 / 1280) = -Real.log (1280 / 1641) := by
    rw [show ((1641 / 1280) : ℝ) = ((1280 / 1641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (165664617 / 500000000) ≤ -Real.log (919 / 1280) ∧
    -Real.log (919 / 1280) ≤ (66265847 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2199)) (n := 12)
    (lo := (165664617 / 500000000)) (hi := (66265847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 919) = 1/(919 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-66265847 / 200000000) (-165664617 / 500000000) (Real.log (919 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (247988591 / 1000000000) ≤ -Real.log (5120 / 6561) ∧
    -Real.log (5120 / 6561) ≤ (15499287 / 62500000) := by
  have h := checkLog_sound (w := (1441 / 11681)) (n := 12)
    (lo := (247988591 / 1000000000)) (hi := (15499287 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6561 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6561 / 5120) = 1/(5120 / 6561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (247988591 / 1000000000) (15499287 / 62500000) (Real.log (6561 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6561 / 5120) = -Real.log (5120 / 6561) := by
    rw [show ((6561 / 5120) : ℝ) = ((5120 / 6561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (165256731 / 500000000) ≤ -Real.log (3679 / 5120) ∧
    -Real.log (3679 / 5120) ≤ (330513463 / 1000000000) := by
  have h := checkLog_sound (w := (1441 / 8799)) (n := 12)
    (lo := (165256731 / 500000000)) (hi := (330513463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3679) = 1/(3679 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-330513463 / 1000000000) (-165256731 / 500000000) (Real.log (3679 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (223643301 / 500000000) ≤ -Real.log (640 / 1001) ∧
    -Real.log (640 / 1001) ≤ (447286603 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 1641)) (n := 12)
    (lo := (223643301 / 500000000)) (hi := (447286603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1001 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1001 / 640) = 1/(640 / 1001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (223643301 / 500000000) (447286603 / 1000000000) (Real.log (1001 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1001 / 640) = -Real.log (640 / 1001) := by
    rw [show ((1001 / 640) : ℝ) = ((640 / 1001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (830256393 / 1000000000) ≤ -Real.log (279 / 640) ∧
    -Real.log (279 / 640) ≤ (166051279 / 200000000) := by
  have h := checkLog_sound (w := (41 / 599)) (n := 12)
    (lo := (137109213 / 1000000000)) (hi := (68554607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 279) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 279) = 1/(279 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166051279 / 200000000) (-830256393 / 1000000000) (Real.log (279 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (446537071 / 1000000000) ≤ -Real.log (2560 / 4001) ∧
    -Real.log (2560 / 4001) ≤ (27908567 / 62500000) := by
  have h := checkLog_sound (w := (1441 / 6561)) (n := 12)
    (lo := (446537071 / 1000000000)) (hi := (27908567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4001 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4001 / 2560) = 1/(2560 / 4001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (446537071 / 1000000000) (27908567 / 62500000) (Real.log (4001 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4001 / 2560) = -Real.log (2560 / 4001) := by
    rw [show ((4001 / 2560) : ℝ) = ((2560 / 4001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (206892957 / 250000000) ≤ -Real.log (1119 / 2560) ∧
    -Real.log (1119 / 2560) ≤ (82757183 / 100000000) := by
  have h := checkLog_sound (w := (161 / 2399)) (n := 12)
    (lo := (16803081 / 125000000)) (hi := (134424649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1119) = 1/(1119 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-82757183 / 100000000) (-206892957 / 250000000) (Real.log (1119 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67881727 / 200000000) ≤ -Real.log (1000000 / 1404117) ∧
    -Real.log (1000000 / 1404117) ≤ (84852159 / 250000000) := by
  have h := checkLog_sound (w := (404117 / 2404117)) (n := 12)
    (lo := (67881727 / 200000000)) (hi := (84852159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1404117 / 1000000) = 1/(1000000 / 1404117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67881727 / 200000000) (84852159 / 250000000) (Real.log (1404117 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1404117 / 1000000) = -Real.log (1000000 / 1404117) := by
    rw [show ((1404117 / 1000000) : ℝ) = ((1000000 / 1404117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (517710939 / 1000000000) ≤ -Real.log (595883 / 1000000) ∧
    -Real.log (595883 / 1000000) ≤ (25885547 / 50000000) := by
  have h := checkLog_sound (w := (404117 / 1595883)) (n := 12)
    (lo := (517710939 / 1000000000)) (hi := (25885547 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 595883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 595883) = 1/(595883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-25885547 / 50000000) (-517710939 / 1000000000) (Real.log (595883 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340029473 / 1000000000) ≤ -Real.log (1000000 / 1404989) ∧
    -Real.log (1000000 / 1404989) ≤ (170014737 / 500000000) := by
  have h := checkLog_sound (w := (404989 / 2404989)) (n := 12)
    (lo := (340029473 / 1000000000)) (hi := (170014737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1404989 / 1000000) = 1/(1000000 / 1404989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340029473 / 1000000000) (170014737 / 500000000) (Real.log (1404989 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1404989 / 1000000) = -Real.log (1000000 / 1404989) := by
    rw [show ((1404989 / 1000000) : ℝ) = ((1000000 / 1404989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (259587693 / 500000000) ≤ -Real.log (595011 / 1000000) ∧
    -Real.log (595011 / 1000000) ≤ (519175387 / 1000000000) := by
  have h := checkLog_sound (w := (404989 / 1595011)) (n := 12)
    (lo := (259587693 / 500000000)) (hi := (519175387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 595011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 595011) = 1/(595011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-519175387 / 1000000000) (-259587693 / 500000000) (Real.log (595011 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5235959 / 20000000) ≤ -Real.log (15625 / 20301) ∧
    -Real.log (15625 / 20301) ≤ (261797951 / 1000000000) := by
  have h := checkLog_sound (w := (2338 / 17963)) (n := 12)
    (lo := (5235959 / 20000000)) (hi := (261797951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20301 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20301 / 15625) = 1/(15625 / 20301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5235959 / 20000000) (261797951 / 1000000000) (Real.log (20301 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (20301 / 15625) = -Real.log (15625 / 20301) := by
    rw [show ((20301 / 15625) : ℝ) = ((15625 / 20301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (355624067 / 1000000000) ≤ -Real.log (10949 / 15625) ∧
    -Real.log (10949 / 15625) ≤ (88906017 / 250000000) := by
  have h := checkLog_sound (w := (2338 / 13287)) (n := 12)
    (lo := (355624067 / 1000000000)) (hi := (88906017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10949) = 1/(10949 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-88906017 / 250000000) (-355624067 / 1000000000) (Real.log (10949 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (65585489 / 250000000) ≤ -Real.log (1000000 / 1299971) ∧
    -Real.log (1000000 / 1299971) ≤ (262341957 / 1000000000) := by
  have h := checkLog_sound (w := (299971 / 2299971)) (n := 12)
    (lo := (65585489 / 250000000)) (hi := (262341957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299971 / 1000000) = 1/(1000000 / 1299971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (65585489 / 250000000) (262341957 / 1000000000) (Real.log (1299971 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1299971 / 1000000) = -Real.log (1000000 / 1299971) := by
    rw [show ((1299971 / 1000000) : ℝ) = ((1000000 / 1299971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (89158379 / 250000000) ≤ -Real.log (700029 / 1000000) ∧
    -Real.log (700029 / 1000000) ≤ (356633517 / 1000000000) := by
  have h := checkLog_sound (w := (299971 / 1700029)) (n := 12)
    (lo := (89158379 / 250000000)) (hi := (356633517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 700029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 700029) = 1/(700029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-356633517 / 1000000000) (-89158379 / 250000000) (Real.log (700029 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (428559787 / 500000000) ≤ -Real.log (97656250 / 230113631) ∧
    -Real.log (97656250 / 230113631) ≤ (107139947 / 125000000) := by
  have h := checkLog_sound (w := (34801131 / 425426131)) (n := 12)
    (lo := (81986197 / 500000000)) (hi := (32794479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230113631 / 195312500) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(230113631 / 195312500) = 1/(97656250 / 230113631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (428559787 / 500000000) (107139947 / 125000000) (Real.log (230113631 / 97656250)) := by
  have h := reflection_log_17_neg
  have he : Real.log (230113631 / 97656250) = -Real.log (97656250 / 230113631) := by
    rw [show ((230113631 / 97656250) : ℝ) = ((97656250 / 230113631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (859204859 / 1000000000) ≤ -Real.log (50000000000 / 118064119823) ∧
    -Real.log (50000000000 / 118064119823) ≤ (859204861 / 1000000000) := by
  have h := checkLog_sound (w := (18064119823 / 218064119823)) (n := 12)
    (lo := (166057679 / 1000000000)) (hi := (2075721 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118064119823 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118064119823 / 100000000000) = 1/(50000000000 / 118064119823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (859204859 / 1000000000) (859204861 / 1000000000) (Real.log (118064119823 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (118064119823 / 50000000000) = -Real.log (50000000000 / 118064119823) := by
    rw [show ((118064119823 / 50000000000) : ℝ) = ((50000000000 / 118064119823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (308711009 / 500000000) ≤ -Real.log (62500000000 / 115883870673) ∧
    -Real.log (62500000000 / 115883870673) ≤ (617422019 / 1000000000) := by
  have h := checkLog_sound (w := (53383870673 / 178383870673)) (n := 12)
    (lo := (308711009 / 500000000)) (hi := (617422019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115883870673 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115883870673 / 62500000000) = 1/(62500000000 / 115883870673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (308711009 / 500000000) (617422019 / 1000000000) (Real.log (115883870673 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (115883870673 / 62500000000) = -Real.log (62500000000 / 115883870673) := by
    rw [show ((115883870673 / 62500000000) : ℝ) = ((62500000000 / 115883870673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (38685967 / 62500000) ≤ -Real.log (10000000000 / 18570244947) ∧
    -Real.log (10000000000 / 18570244947) ≤ (618975473 / 1000000000) := by
  have h := checkLog_sound (w := (8570244947 / 28570244947)) (n := 12)
    (lo := (38685967 / 62500000)) (hi := (618975473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18570244947 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18570244947 / 10000000000) = 1/(10000000000 / 18570244947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (38685967 / 62500000) (618975473 / 1000000000) (Real.log (18570244947 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18570244947 / 10000000000) = -Real.log (10000000000 / 18570244947) := by
    rw [show ((18570244947 / 10000000000) : ℝ) = ((10000000000 / 18570244947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0238

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0239Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0239
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

theorem reflection_log_1_neg : (247988591 / 1000000000) ≤ -Real.log (5120 / 6561) ∧
    -Real.log (5120 / 6561) ≤ (15499287 / 62500000) := by
  have h := checkLog_sound (w := (1441 / 11681)) (n := 12)
    (lo := (247988591 / 1000000000)) (hi := (15499287 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6561 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6561 / 5120) = 1/(5120 / 6561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (247988591 / 1000000000) (15499287 / 62500000) (Real.log (6561 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6561 / 5120) = -Real.log (5120 / 6561) := by
    rw [show ((6561 / 5120) : ℝ) = ((5120 / 6561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (165256731 / 500000000) ≤ -Real.log (3679 / 5120) ∧
    -Real.log (3679 / 5120) ≤ (330513463 / 1000000000) := by
  have h := checkLog_sound (w := (1441 / 8799)) (n := 12)
    (lo := (165256731 / 500000000)) (hi := (330513463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3679) = 1/(3679 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-330513463 / 1000000000) (-165256731 / 500000000) (Real.log (3679 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (247531239 / 1000000000) ≤ -Real.log (2560 / 3279) ∧
    -Real.log (2560 / 3279) ≤ (6188281 / 25000000) := by
  have h := checkLog_sound (w := (719 / 5839)) (n := 12)
    (lo := (247531239 / 1000000000)) (hi := (6188281 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3279 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3279 / 2560) = 1/(2560 / 3279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (247531239 / 1000000000) (6188281 / 25000000) (Real.log (3279 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3279 / 2560) = -Real.log (2560 / 3279) := by
    rw [show ((3279 / 2560) : ℝ) = ((2560 / 3279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (82424589 / 250000000) ≤ -Real.log (1841 / 2560) ∧
    -Real.log (1841 / 2560) ≤ (329698357 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 4401)) (n := 12)
    (lo := (82424589 / 250000000)) (hi := (329698357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1841) = 1/(1841 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-329698357 / 1000000000) (-82424589 / 250000000) (Real.log (1841 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (446537071 / 1000000000) ≤ -Real.log (2560 / 4001) ∧
    -Real.log (2560 / 4001) ≤ (27908567 / 62500000) := by
  have h := checkLog_sound (w := (1441 / 6561)) (n := 12)
    (lo := (446537071 / 1000000000)) (hi := (27908567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4001 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4001 / 2560) = 1/(2560 / 4001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (446537071 / 1000000000) (27908567 / 62500000) (Real.log (4001 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4001 / 2560) = -Real.log (2560 / 4001) := by
    rw [show ((4001 / 2560) : ℝ) = ((2560 / 4001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (206892957 / 250000000) ≤ -Real.log (1119 / 2560) ∧
    -Real.log (1119 / 2560) ≤ (82757183 / 100000000) := by
  have h := checkLog_sound (w := (161 / 2399)) (n := 12)
    (lo := (16803081 / 125000000)) (hi := (134424649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1119) = 1/(1119 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-82757183 / 100000000) (-206892957 / 250000000) (Real.log (1119 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (445786977 / 1000000000) ≤ -Real.log (1280 / 1999) ∧
    -Real.log (1280 / 1999) ≤ (222893489 / 500000000) := by
  have h := checkLog_sound (w := (719 / 3279)) (n := 12)
    (lo := (445786977 / 1000000000)) (hi := (222893489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1999 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1999 / 1280) = 1/(1280 / 1999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (445786977 / 1000000000) (222893489 / 500000000) (Real.log (1999 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1999 / 1280) = -Real.log (1280 / 1999) := by
    rw [show ((1999 / 1280) : ℝ) = ((1280 / 1999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (16497889 / 20000000) ≤ -Real.log (561 / 1280) ∧
    -Real.log (561 / 1280) ≤ (206223613 / 250000000) := by
  have h := checkLog_sound (w := (79 / 1201)) (n := 12)
    (lo := (13174727 / 100000000)) (hi := (131747271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 561) = 1/(561 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-206223613 / 250000000) (-16497889 / 20000000) (Real.log (561 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (84697031 / 250000000) ≤ -Real.log (500000 / 701623) ∧
    -Real.log (500000 / 701623) ≤ (542061 / 1600000) := by
  have h := checkLog_sound (w := (201623 / 1201623)) (n := 12)
    (lo := (84697031 / 250000000)) (hi := (542061 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701623 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701623 / 500000) = 1/(500000 / 701623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (84697031 / 250000000) (542061 / 1600000) (Real.log (701623 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (701623 / 500000) = -Real.log (500000 / 701623) := by
    rw [show ((701623 / 500000) : ℝ) = ((500000 / 701623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (51625031 / 100000000) ≤ -Real.log (298377 / 500000) ∧
    -Real.log (298377 / 500000) ≤ (516250311 / 1000000000) := by
  have h := checkLog_sound (w := (201623 / 798377)) (n := 12)
    (lo := (51625031 / 100000000)) (hi := (516250311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 298377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 298377) = 1/(298377 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-516250311 / 1000000000) (-51625031 / 100000000) (Real.log (298377 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339409347 / 1000000000) ≤ -Real.log (500000 / 702059) ∧
    -Real.log (500000 / 702059) ≤ (84852337 / 250000000) := by
  have h := checkLog_sound (w := (202059 / 1202059)) (n := 12)
    (lo := (339409347 / 1000000000)) (hi := (84852337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702059 / 500000) = 1/(500000 / 702059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339409347 / 1000000000) (84852337 / 250000000) (Real.log (702059 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (702059 / 500000) = -Real.log (500000 / 702059) := by
    rw [show ((702059 / 500000) : ℝ) = ((500000 / 702059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (258856309 / 500000000) ≤ -Real.log (297941 / 500000) ∧
    -Real.log (297941 / 500000) ≤ (517712619 / 1000000000) := by
  have h := checkLog_sound (w := (202059 / 797941)) (n := 12)
    (lo := (258856309 / 500000000)) (hi := (517712619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 297941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 297941) = 1/(297941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-517712619 / 1000000000) (-258856309 / 500000000) (Real.log (297941 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (130627209 / 500000000) ≤ -Real.log (500000 / 649279) ∧
    -Real.log (500000 / 649279) ≤ (261254419 / 1000000000) := by
  have h := checkLog_sound (w := (149279 / 1149279)) (n := 12)
    (lo := (130627209 / 500000000)) (hi := (261254419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649279 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649279 / 500000) = 1/(500000 / 649279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (130627209 / 500000000) (261254419 / 1000000000) (Real.log (649279 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (649279 / 500000) = -Real.log (500000 / 649279) := by
    rw [show ((649279 / 500000) : ℝ) = ((500000 / 649279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (177308531 / 500000000) ≤ -Real.log (350721 / 500000) ∧
    -Real.log (350721 / 500000) ≤ (354617063 / 1000000000) := by
  have h := checkLog_sound (w := (149279 / 850721)) (n := 12)
    (lo := (177308531 / 500000000)) (hi := (354617063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 350721) = 1/(350721 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-354617063 / 1000000000) (-177308531 / 500000000) (Real.log (350721 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (261798719 / 1000000000) ≤ -Real.log (200000 / 259853) ∧
    -Real.log (200000 / 259853) ≤ (818121 / 3125000) := by
  have h := checkLog_sound (w := (59853 / 459853)) (n := 12)
    (lo := (261798719 / 1000000000)) (hi := (818121 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259853 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259853 / 200000) = 1/(200000 / 259853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (261798719 / 1000000000) (818121 / 3125000) (Real.log (259853 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (259853 / 200000) = -Real.log (200000 / 259853) := by
    rw [show ((259853 / 200000) : ℝ) = ((200000 / 259853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (177812747 / 500000000) ≤ -Real.log (140147 / 200000) ∧
    -Real.log (140147 / 200000) ≤ (71125099 / 200000000) := by
  have h := checkLog_sound (w := (59853 / 340147)) (n := 12)
    (lo := (177812747 / 500000000)) (hi := (71125099 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 140147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 140147) = 1/(140147 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-71125099 / 200000000) (-177812747 / 500000000) (Real.log (140147 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (427519217 / 500000000) ≤ -Real.log (125000000000 / 293933094709) ∧
    -Real.log (125000000000 / 293933094709) ≤ (213759609 / 250000000) := by
  have h := checkLog_sound (w := (43933094709 / 543933094709)) (n := 12)
    (lo := (80945627 / 500000000)) (hi := (32378251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293933094709 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(293933094709 / 250000000000) = 1/(125000000000 / 293933094709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (427519217 / 500000000) (213759609 / 250000000) (Real.log (293933094709 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (293933094709 / 125000000000) = -Real.log (125000000000 / 293933094709) := by
    rw [show ((293933094709 / 125000000000) : ℝ) = ((125000000000 / 293933094709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (171424393 / 200000000) ≤ -Real.log (25000000000 / 58909230351) ∧
    -Real.log (25000000000 / 58909230351) ≤ (857121967 / 1000000000) := by
  have h := checkLog_sound (w := (8909230351 / 108909230351)) (n := 12)
    (lo := (32794957 / 200000000)) (hi := (81987393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58909230351 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(58909230351 / 50000000000) = 1/(25000000000 / 58909230351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (171424393 / 200000000) (857121967 / 1000000000) (Real.log (58909230351 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (58909230351 / 25000000000) = -Real.log (25000000000 / 58909230351) := by
    rw [show ((58909230351 / 25000000000) : ℝ) = ((25000000000 / 58909230351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15396787 / 25000000) ≤ -Real.log (500000000000 / 925634621251) ∧
    -Real.log (500000000000 / 925634621251) ≤ (615871481 / 1000000000) := by
  have h := checkLog_sound (w := (425634621251 / 1425634621251)) (n := 12)
    (lo := (15396787 / 25000000)) (hi := (615871481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925634621251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925634621251 / 500000000000) = 1/(500000000000 / 925634621251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15396787 / 25000000) (615871481 / 1000000000) (Real.log (925634621251 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (925634621251 / 500000000000) = -Real.log (500000000000 / 925634621251) := by
    rw [show ((925634621251 / 500000000000) : ℝ) = ((500000000000 / 925634621251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (308712107 / 500000000) ≤ -Real.log (1562500000 / 2897103131) ∧
    -Real.log (1562500000 / 2897103131) ≤ (123484843 / 200000000) := by
  have h := checkLog_sound (w := (1334603131 / 4459603131)) (n := 12)
    (lo := (308712107 / 500000000)) (hi := (123484843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2897103131 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2897103131 / 1562500000) = 1/(1562500000 / 2897103131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (308712107 / 500000000) (123484843 / 200000000) (Real.log (2897103131 / 1562500000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2897103131 / 1562500000) = -Real.log (1562500000 / 2897103131) := by
    rw [show ((2897103131 / 1562500000) : ℝ) = ((1562500000 / 2897103131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0239

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0240Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0240
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

theorem reflection_log_1_neg : (247531239 / 1000000000) ≤ -Real.log (2560 / 3279) ∧
    -Real.log (2560 / 3279) ≤ (6188281 / 25000000) := by
  have h := checkLog_sound (w := (719 / 5839)) (n := 12)
    (lo := (247531239 / 1000000000)) (hi := (6188281 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3279 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3279 / 2560) = 1/(2560 / 3279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (247531239 / 1000000000) (6188281 / 25000000) (Real.log (3279 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3279 / 2560) = -Real.log (2560 / 3279) := by
    rw [show ((3279 / 2560) : ℝ) = ((2560 / 3279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (82424589 / 250000000) ≤ -Real.log (1841 / 2560) ∧
    -Real.log (1841 / 2560) ≤ (329698357 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 4401)) (n := 12)
    (lo := (82424589 / 250000000)) (hi := (329698357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1841) = 1/(1841 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-329698357 / 1000000000) (-82424589 / 250000000) (Real.log (1841 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (123536839 / 500000000) ≤ -Real.log (1024 / 1311) ∧
    -Real.log (1024 / 1311) ≤ (247073679 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 2335)) (n := 12)
    (lo := (123536839 / 500000000)) (hi := (247073679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311 / 1024) = 1/(1024 / 1311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (123536839 / 500000000) (247073679 / 1000000000) (Real.log (1311 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1311 / 1024) = -Real.log (1024 / 1311) := by
    rw [show ((1311 / 1024) : ℝ) = ((1024 / 1311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (328883913 / 1000000000) ≤ -Real.log (737 / 1024) ∧
    -Real.log (737 / 1024) ≤ (164441957 / 500000000) := by
  have h := checkLog_sound (w := (287 / 1761)) (n := 12)
    (lo := (328883913 / 1000000000)) (hi := (164441957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 737) = 1/(737 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-164441957 / 500000000) (-328883913 / 1000000000) (Real.log (737 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (445786977 / 1000000000) ≤ -Real.log (1280 / 1999) ∧
    -Real.log (1280 / 1999) ≤ (222893489 / 500000000) := by
  have h := checkLog_sound (w := (719 / 3279)) (n := 12)
    (lo := (445786977 / 1000000000)) (hi := (222893489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1999 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1999 / 1280) = 1/(1280 / 1999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (445786977 / 1000000000) (222893489 / 500000000) (Real.log (1999 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1999 / 1280) = -Real.log (1280 / 1999) := by
    rw [show ((1999 / 1280) : ℝ) = ((1280 / 1999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (16497889 / 20000000) ≤ -Real.log (561 / 1280) ∧
    -Real.log (561 / 1280) ≤ (206223613 / 250000000) := by
  have h := checkLog_sound (w := (79 / 1201)) (n := 12)
    (lo := (13174727 / 100000000)) (hi := (131747271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 561) = 1/(561 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-206223613 / 250000000) (-16497889 / 20000000) (Real.log (561 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2781477 / 6250000) ≤ -Real.log (512 / 799) ∧
    -Real.log (512 / 799) ≤ (445036321 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 1311)) (n := 12)
    (lo := (2781477 / 6250000)) (hi := (445036321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((799 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(799 / 512) = 1/(512 / 799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2781477 / 6250000) (445036321 / 1000000000) (Real.log (799 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (799 / 512) = -Real.log (512 / 799) := by
    rw [show ((799 / 512) : ℝ) = ((512 / 799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (411112111 / 500000000) ≤ -Real.log (225 / 512) ∧
    -Real.log (225 / 512) ≤ (25694507 / 31250000) := by
  have h := checkLog_sound (w := (31 / 481)) (n := 12)
    (lo := (64538521 / 500000000)) (hi := (129077043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 225) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 225) = 1/(225 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-25694507 / 31250000) (-411112111 / 500000000) (Real.log (225 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (338167227 / 1000000000) ≤ -Real.log (8000 / 11219) ∧
    -Real.log (8000 / 11219) ≤ (84541807 / 250000000) := by
  have h := checkLog_sound (w := (3219 / 19219)) (n := 12)
    (lo := (338167227 / 1000000000)) (hi := (84541807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11219 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11219 / 8000) = 1/(8000 / 11219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (338167227 / 1000000000) (84541807 / 250000000) (Real.log (11219 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (11219 / 8000) = -Real.log (8000 / 11219) := by
    rw [show ((11219 / 8000) : ℝ) = ((8000 / 11219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (128697953 / 250000000) ≤ -Real.log (4781 / 8000) ∧
    -Real.log (4781 / 8000) ≤ (514791813 / 1000000000) := by
  have h := checkLog_sound (w := (3219 / 12781)) (n := 12)
    (lo := (128697953 / 250000000)) (hi := (514791813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 4781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 4781) = 1/(4781 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-514791813 / 1000000000) (-128697953 / 250000000) (Real.log (4781 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84697209 / 250000000) ≤ -Real.log (1000000 / 1403247) ∧
    -Real.log (1000000 / 1403247) ≤ (338788837 / 1000000000) := by
  have h := checkLog_sound (w := (403247 / 2403247)) (n := 12)
    (lo := (84697209 / 250000000)) (hi := (338788837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403247 / 1000000) = 1/(1000000 / 1403247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84697209 / 250000000) (338788837 / 1000000000) (Real.log (1403247 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1403247 / 1000000) = -Real.log (1000000 / 1403247) := by
    rw [show ((1403247 / 1000000) : ℝ) = ((1000000 / 1403247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (258125993 / 500000000) ≤ -Real.log (596753 / 1000000) ∧
    -Real.log (596753 / 1000000) ≤ (516251987 / 1000000000) := by
  have h := checkLog_sound (w := (403247 / 1596753)) (n := 12)
    (lo := (258125993 / 500000000)) (hi := (516251987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 596753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 596753) = 1/(596753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-516251987 / 1000000000) (-258125993 / 500000000) (Real.log (596753 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (814723 / 3125000) ≤ -Real.log (1000000 / 1297853) ∧
    -Real.log (1000000 / 1297853) ≤ (260711361 / 1000000000) := by
  have h := checkLog_sound (w := (297853 / 2297853)) (n := 12)
    (lo := (814723 / 3125000)) (hi := (260711361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297853 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297853 / 1000000) = 1/(1000000 / 1297853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (814723 / 3125000) (260711361 / 1000000000) (Real.log (1297853 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1297853 / 1000000) = -Real.log (1000000 / 1297853) := by
    rw [show ((1297853 / 1000000) : ℝ) = ((1000000 / 1297853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (70722499 / 200000000) ≤ -Real.log (702147 / 1000000) ∧
    -Real.log (702147 / 1000000) ≤ (22100781 / 62500000) := by
  have h := checkLog_sound (w := (297853 / 1702147)) (n := 12)
    (lo := (70722499 / 200000000)) (hi := (22100781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 702147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 702147) = 1/(702147 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-22100781 / 62500000) (-70722499 / 200000000) (Real.log (702147 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (65313797 / 250000000) ≤ -Real.log (1000000 / 1298559) ∧
    -Real.log (1000000 / 1298559) ≤ (261255189 / 1000000000) := by
  have h := checkLog_sound (w := (298559 / 2298559)) (n := 12)
    (lo := (65313797 / 250000000)) (hi := (261255189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1298559 / 1000000) = 1/(1000000 / 1298559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (65313797 / 250000000) (261255189 / 1000000000) (Real.log (1298559 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1298559 / 1000000) = -Real.log (1000000 / 1298559) := by
    rw [show ((1298559 / 1000000) : ℝ) = ((1000000 / 1298559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (44327311 / 125000000) ≤ -Real.log (701441 / 1000000) ∧
    -Real.log (701441 / 1000000) ≤ (354618489 / 1000000000) := by
  have h := checkLog_sound (w := (298559 / 1701441)) (n := 12)
    (lo := (44327311 / 125000000)) (hi := (354618489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 701441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 701441) = 1/(701441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-354618489 / 1000000000) (-44327311 / 125000000) (Real.log (701441 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (852959039 / 1000000000) ≤ -Real.log (31250000000 / 73330631667) ∧
    -Real.log (31250000000 / 73330631667) ≤ (852959041 / 1000000000) := by
  have h := checkLog_sound (w := (10830631667 / 135830631667)) (n := 12)
    (lo := (159811859 / 1000000000)) (hi := (7990593 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73330631667 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(73330631667 / 62500000000) = 1/(31250000000 / 73330631667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (852959039 / 1000000000) (852959041 / 1000000000) (Real.log (73330631667 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (73330631667 / 31250000000) = -Real.log (31250000000 / 73330631667) := by
    rw [show ((73330631667 / 31250000000) : ℝ) = ((31250000000 / 73330631667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (427520411 / 500000000) ≤ -Real.log (12500000000 / 29393379673) ∧
    -Real.log (12500000000 / 29393379673) ≤ (106880103 / 125000000) := by
  have h := checkLog_sound (w := (4393379673 / 54393379673)) (n := 12)
    (lo := (80946821 / 500000000)) (hi := (161893643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29393379673 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(29393379673 / 25000000000) = 1/(12500000000 / 29393379673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (427520411 / 500000000) (106880103 / 125000000) (Real.log (29393379673 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (29393379673 / 12500000000) = -Real.log (12500000000 / 29393379673) := by
    rw [show ((29393379673 / 12500000000) : ℝ) = ((12500000000 / 29393379673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (122864771 / 200000000) ≤ -Real.log (250000000000 / 462101596959) ∧
    -Real.log (250000000000 / 462101596959) ≤ (38395241 / 62500000) := by
  have h := checkLog_sound (w := (212101596959 / 712101596959)) (n := 12)
    (lo := (122864771 / 200000000)) (hi := (38395241 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462101596959 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462101596959 / 250000000000) = 1/(250000000000 / 462101596959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (122864771 / 200000000) (38395241 / 62500000) (Real.log (462101596959 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (462101596959 / 250000000000) = -Real.log (250000000000 / 462101596959) := by
    rw [show ((462101596959 / 250000000000) : ℝ) = ((250000000000 / 462101596959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (153968419 / 250000000) ≤ -Real.log (500000000000 / 925636653689) ∧
    -Real.log (500000000000 / 925636653689) ≤ (615873677 / 1000000000) := by
  have h := checkLog_sound (w := (425636653689 / 1425636653689)) (n := 12)
    (lo := (153968419 / 250000000)) (hi := (615873677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925636653689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925636653689 / 500000000000) = 1/(500000000000 / 925636653689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (153968419 / 250000000) (615873677 / 1000000000) (Real.log (925636653689 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (925636653689 / 500000000000) = -Real.log (500000000000 / 925636653689) := by
    rw [show ((925636653689 / 500000000000) : ℝ) = ((500000000000 / 925636653689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0240

end


