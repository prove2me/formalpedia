-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0115Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0115Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:14:05.223787+00:00
-- url     : https://prove2.me/theorems/128ce01b-e403-4b90-98b8-9f2fd02771b2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0115Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0116Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0115Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0116Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0117Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0118Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0119Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0120Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0115Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0116Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0117Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0118Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0119Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0120Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0115Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0116Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0117Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0118Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0119Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0120Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0115Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0116Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0117Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0118Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0119Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0120Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0115Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0115
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

theorem reflection_log_1_neg : (320723879 / 1000000000) ≤ -Real.log (320 / 441) ∧
    -Real.log (320 / 441) ≤ (8018097 / 25000000) := by
  have h := checkLog_sound (w := (121 / 761)) (n := 12)
    (lo := (320723879 / 1000000000)) (hi := (8018097 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 320) = 1/(320 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (320723879 / 1000000000) (8018097 / 25000000) (Real.log (441 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (441 / 320) = -Real.log (320 / 441) := by
    rw [show ((441 / 320) : ℝ) = ((320 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (475016171 / 1000000000) ≤ -Real.log (199 / 320) ∧
    -Real.log (199 / 320) ≤ (118754043 / 250000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 199) = 1/(199 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-118754043 / 250000000) (-475016171 / 1000000000) (Real.log (199 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (319873177 / 1000000000) ≤ -Real.log (512 / 705) ∧
    -Real.log (512 / 705) ≤ (159936589 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1217)) (n := 12)
    (lo := (319873177 / 1000000000)) (hi := (159936589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705 / 512) = 1/(512 / 705) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (319873177 / 1000000000) (159936589 / 500000000) (Real.log (705 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (705 / 512) = -Real.log (512 / 705) := by
    rw [show ((705 / 512) : ℝ) = ((512 / 705) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (236566761 / 500000000) ≤ -Real.log (319 / 512) ∧
    -Real.log (319 / 512) ≤ (473133523 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 831)) (n := 12)
    (lo := (236566761 / 500000000)) (hi := (473133523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 319) = 1/(319 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-473133523 / 1000000000) (-236566761 / 500000000) (Real.log (319 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (281590427 / 500000000) ≤ -Real.log (160 / 281) ∧
    -Real.log (160 / 281) ≤ (112636171 / 200000000) := by
  have h := checkLog_sound (w := (121 / 441)) (n := 12)
    (lo := (281590427 / 500000000)) (hi := (112636171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281 / 160) = 1/(160 / 281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (281590427 / 500000000) (112636171 / 200000000) (Real.log (281 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (281 / 160) = -Real.log (160 / 281) := by
    rw [show ((281 / 160) : ℝ) = ((160 / 281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1411612167 / 1000000000) ≤ -Real.log (39 / 160) ∧
    -Real.log (39 / 160) ≤ (141161217 / 100000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 39) = 1/(39 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-141161217 / 100000000) (-1411612167 / 1000000000) (Real.log (39 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (561845443 / 1000000000) ≤ -Real.log (256 / 449) ∧
    -Real.log (256 / 449) ≤ (140461361 / 250000000) := by
  have h := checkLog_sound (w := (193 / 705)) (n := 12)
    (lo := (561845443 / 1000000000)) (hi := (140461361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449 / 256) = 1/(256 / 449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (561845443 / 1000000000) (140461361 / 250000000) (Real.log (449 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (449 / 256) = -Real.log (256 / 449) := by
    rw [show ((449 / 256) : ℝ) = ((256 / 449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (350510679 / 250000000) ≤ -Real.log (63 / 256) ∧
    -Real.log (63 / 256) ≤ (1402042719 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 63) = 1/(63 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1402042719 / 1000000000) (-350510679 / 250000000) (Real.log (63 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (438373633 / 1000000000) ≤ -Real.log (125000 / 193773) ∧
    -Real.log (125000 / 193773) ≤ (219186817 / 500000000) := by
  have h := checkLog_sound (w := (68773 / 318773)) (n := 12)
    (lo := (438373633 / 1000000000)) (hi := (219186817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193773 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193773 / 125000) = 1/(125000 / 193773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (438373633 / 1000000000) (219186817 / 500000000) (Real.log (193773 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (193773 / 125000) = -Real.log (125000 / 193773) := by
    rw [show ((193773 / 125000) : ℝ) = ((125000 / 193773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199729167 / 250000000) ≤ -Real.log (56227 / 125000) ∧
    -Real.log (56227 / 125000) ≤ (79891667 / 100000000) := by
  have h := checkLog_sound (w := (6273 / 118727)) (n := 12)
    (lo := (6610593 / 62500000)) (hi := (105769489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 56227) = 1/(56227 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-79891667 / 100000000) (-199729167 / 250000000) (Real.log (56227 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21978703 / 50000000) ≤ -Real.log (500000 / 776023) ∧
    -Real.log (500000 / 776023) ≤ (439574061 / 1000000000) := by
  have h := checkLog_sound (w := (276023 / 1276023)) (n := 12)
    (lo := (21978703 / 50000000)) (hi := (439574061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776023 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776023 / 500000) = 1/(500000 / 776023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21978703 / 50000000) (439574061 / 1000000000) (Real.log (776023 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (776023 / 500000) = -Real.log (500000 / 776023) := by
    rw [show ((776023 / 500000) : ℝ) = ((500000 / 776023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (803064729 / 1000000000) ≤ -Real.log (223977 / 500000) ∧
    -Real.log (223977 / 500000) ≤ (803064731 / 1000000000) := by
  have h := checkLog_sound (w := (26023 / 473977)) (n := 12)
    (lo := (109917549 / 1000000000)) (hi := (2198351 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 223977) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 223977) = 1/(223977 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-803064731 / 1000000000) (-803064729 / 1000000000) (Real.log (223977 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (353759799 / 1000000000) ≤ -Real.log (1000000 / 1424413) ∧
    -Real.log (1000000 / 1424413) ≤ (1768799 / 5000000) := by
  have h := checkLog_sound (w := (424413 / 2424413)) (n := 12)
    (lo := (353759799 / 1000000000)) (hi := (1768799 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1424413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1424413 / 1000000) = 1/(1000000 / 1424413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (353759799 / 1000000000) (1768799 / 5000000) (Real.log (1424413 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1424413 / 1000000) = -Real.log (1000000 / 1424413) := by
    rw [show ((1424413 / 1000000) : ℝ) = ((1000000 / 1424413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (552364889 / 1000000000) ≤ -Real.log (575587 / 1000000) ∧
    -Real.log (575587 / 1000000) ≤ (55236489 / 100000000) := by
  have h := checkLog_sound (w := (424413 / 1575587)) (n := 12)
    (lo := (552364889 / 1000000000)) (hi := (55236489 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 575587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 575587) = 1/(575587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-55236489 / 100000000) (-552364889 / 1000000000) (Real.log (575587 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (354950457 / 1000000000) ≤ -Real.log (100000 / 142611) ∧
    -Real.log (100000 / 142611) ≤ (177475229 / 500000000) := by
  have h := checkLog_sound (w := (42611 / 242611)) (n := 12)
    (lo := (354950457 / 1000000000)) (hi := (177475229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142611 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142611 / 100000) = 1/(100000 / 142611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (354950457 / 1000000000) (177475229 / 500000000) (Real.log (142611 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (142611 / 100000) = -Real.log (100000 / 142611) := by
    rw [show ((142611 / 100000) : ℝ) = ((100000 / 142611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (277658769 / 500000000) ≤ -Real.log (57389 / 100000) ∧
    -Real.log (57389 / 100000) ≤ (555317539 / 1000000000) := by
  have h := checkLog_sound (w := (42611 / 157389)) (n := 12)
    (lo := (277658769 / 500000000)) (hi := (555317539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 57389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 57389) = 1/(57389 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-555317539 / 1000000000) (-277658769 / 500000000) (Real.log (57389 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1237290301 / 1000000000) ≤ -Real.log (500000000000 / 1723131235883) ∧
    -Real.log (500000000000 / 1723131235883) ≤ (1237290303 / 1000000000) := by
  have h := checkLog_sound (w := (723131235883 / 2723131235883)) (n := 12)
    (lo := (544143121 / 1000000000)) (hi := (272071561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723131235883 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1723131235883 / 1000000000000) = 1/(500000000000 / 1723131235883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1237290301 / 1000000000) (1237290303 / 1000000000) (Real.log (1723131235883 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1723131235883 / 500000000000) = -Real.log (500000000000 / 1723131235883) := by
    rw [show ((1723131235883 / 500000000000) : ℝ) = ((500000000000 / 1723131235883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (124263879 / 100000000) ≤ -Real.log (500000000000 / 1732372073919) ∧
    -Real.log (500000000000 / 1732372073919) ≤ (155329849 / 125000000) := by
  have h := checkLog_sound (w := (732372073919 / 2732372073919)) (n := 12)
    (lo := (54949161 / 100000000)) (hi := (549491611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1732372073919 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1732372073919 / 1000000000000) = 1/(500000000000 / 1732372073919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (124263879 / 100000000) (155329849 / 125000000) (Real.log (1732372073919 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1732372073919 / 500000000000) = -Real.log (500000000000 / 1732372073919) := by
    rw [show ((1732372073919 / 500000000000) : ℝ) = ((500000000000 / 1732372073919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (906124687 / 1000000000) ≤ -Real.log (500000000000 / 1237356820081) ∧
    -Real.log (500000000000 / 1237356820081) ≤ (906124689 / 1000000000) := by
  have h := checkLog_sound (w := (237356820081 / 2237356820081)) (n := 12)
    (lo := (212977507 / 1000000000)) (hi := (53244377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237356820081 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1237356820081 / 1000000000000) = 1/(500000000000 / 1237356820081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (906124687 / 1000000000) (906124689 / 1000000000) (Real.log (1237356820081 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1237356820081 / 500000000000) = -Real.log (500000000000 / 1237356820081) := by
    rw [show ((1237356820081 / 500000000000) : ℝ) = ((500000000000 / 1237356820081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (182053599 / 200000000) ≤ -Real.log (500000000000 / 1242494206207) ∧
    -Real.log (500000000000 / 1242494206207) ≤ (910267997 / 1000000000) := by
  have h := checkLog_sound (w := (242494206207 / 2242494206207)) (n := 12)
    (lo := (43424163 / 200000000)) (hi := (13570051 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242494206207 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1242494206207 / 1000000000000) = 1/(500000000000 / 1242494206207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (182053599 / 200000000) (910267997 / 1000000000) (Real.log (1242494206207 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1242494206207 / 500000000000) = -Real.log (500000000000 / 1242494206207) := by
    rw [show ((1242494206207 / 500000000000) : ℝ) = ((500000000000 / 1242494206207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0115

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0116Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0116
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

theorem reflection_log_1_neg : (319873177 / 1000000000) ≤ -Real.log (512 / 705) ∧
    -Real.log (512 / 705) ≤ (159936589 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1217)) (n := 12)
    (lo := (319873177 / 1000000000)) (hi := (159936589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705 / 512) = 1/(512 / 705) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (319873177 / 1000000000) (159936589 / 500000000) (Real.log (705 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (705 / 512) = -Real.log (512 / 705) := by
    rw [show ((705 / 512) : ℝ) = ((512 / 705) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (236566761 / 500000000) ≤ -Real.log (319 / 512) ∧
    -Real.log (319 / 512) ≤ (473133523 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 831)) (n := 12)
    (lo := (236566761 / 500000000)) (hi := (473133523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 319) = 1/(319 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-473133523 / 1000000000) (-236566761 / 500000000) (Real.log (319 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (319021751 / 1000000000) ≤ -Real.log (1280 / 1761) ∧
    -Real.log (1280 / 1761) ≤ (39877719 / 125000000) := by
  have h := checkLog_sound (w := (481 / 3041)) (n := 12)
    (lo := (319021751 / 1000000000)) (hi := (39877719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1761 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1761 / 1280) = 1/(1280 / 1761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (319021751 / 1000000000) (39877719 / 125000000) (Real.log (1761 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1761 / 1280) = -Real.log (1280 / 1761) := by
    rw [show ((1761 / 1280) : ℝ) = ((1280 / 1761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (471254411 / 1000000000) ≤ -Real.log (799 / 1280) ∧
    -Real.log (799 / 1280) ≤ (117813603 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2079)) (n := 12)
    (lo := (471254411 / 1000000000)) (hi := (117813603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 799) = 1/(799 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-117813603 / 250000000) (-471254411 / 1000000000) (Real.log (799 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (561845443 / 1000000000) ≤ -Real.log (256 / 449) ∧
    -Real.log (256 / 449) ≤ (140461361 / 250000000) := by
  have h := checkLog_sound (w := (193 / 705)) (n := 12)
    (lo := (561845443 / 1000000000)) (hi := (140461361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449 / 256) = 1/(256 / 449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (561845443 / 1000000000) (140461361 / 250000000) (Real.log (449 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (449 / 256) = -Real.log (256 / 449) := by
    rw [show ((449 / 256) : ℝ) = ((256 / 449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (350510679 / 250000000) ≤ -Real.log (63 / 256) ∧
    -Real.log (63 / 256) ≤ (1402042719 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 63) = 1/(63 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1402042719 / 1000000000) (-350510679 / 250000000) (Real.log (63 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (280254123 / 500000000) ≤ -Real.log (640 / 1121) ∧
    -Real.log (640 / 1121) ≤ (560508247 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 1761)) (n := 12)
    (lo := (280254123 / 500000000)) (hi := (560508247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121 / 640) = 1/(640 / 1121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (280254123 / 500000000) (560508247 / 1000000000) (Real.log (1121 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1121 / 640) = -Real.log (640 / 1121) := by
    rw [show ((1121 / 640) : ℝ) = ((640 / 1121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1392563973 / 1000000000) ≤ -Real.log (159 / 640) ∧
    -Real.log (159 / 640) ≤ (174070497 / 125000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 159) = 1/(159 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-174070497 / 125000000) (-1392563973 / 1000000000) (Real.log (159 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (437173701 / 1000000000) ≤ -Real.log (40000 / 61933) ∧
    -Real.log (40000 / 61933) ≤ (218586851 / 500000000) := by
  have h := checkLog_sound (w := (21933 / 101933)) (n := 12)
    (lo := (437173701 / 1000000000)) (hi := (218586851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61933 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61933 / 40000) = 1/(40000 / 61933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (437173701 / 1000000000) (218586851 / 500000000) (Real.log (61933 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (61933 / 40000) = -Real.log (40000 / 61933) := by
    rw [show ((61933 / 40000) : ℝ) = ((40000 / 61933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (794792383 / 1000000000) ≤ -Real.log (18067 / 40000) ∧
    -Real.log (18067 / 40000) ≤ (158958477 / 200000000) := by
  have h := checkLog_sound (w := (1933 / 38067)) (n := 12)
    (lo := (101645203 / 1000000000)) (hi := (25411301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18067) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 18067) = 1/(18067 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158958477 / 200000000) (-794792383 / 1000000000) (Real.log (18067 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (219187139 / 500000000) ≤ -Real.log (200000 / 310037) ∧
    -Real.log (200000 / 310037) ≤ (438374279 / 1000000000) := by
  have h := checkLog_sound (w := (110037 / 510037)) (n := 12)
    (lo := (219187139 / 500000000)) (hi := (438374279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310037 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310037 / 200000) = 1/(200000 / 310037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (219187139 / 500000000) (438374279 / 1000000000) (Real.log (310037 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (310037 / 200000) = -Real.log (200000 / 310037) := by
    rw [show ((310037 / 200000) : ℝ) = ((200000 / 310037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (798918891 / 1000000000) ≤ -Real.log (89963 / 200000) ∧
    -Real.log (89963 / 200000) ≤ (798918893 / 1000000000) := by
  have h := checkLog_sound (w := (10037 / 189963)) (n := 12)
    (lo := (105771711 / 1000000000)) (hi := (1652683 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89963) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 89963) = 1/(89963 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-798918893 / 1000000000) (-798918891 / 1000000000) (Real.log (89963 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2203579 / 6250000) ≤ -Real.log (1000000 / 1422723) ∧
    -Real.log (1000000 / 1422723) ≤ (352572641 / 1000000000) := by
  have h := checkLog_sound (w := (422723 / 2422723)) (n := 12)
    (lo := (2203579 / 6250000)) (hi := (352572641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1422723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1422723 / 1000000) = 1/(1000000 / 1422723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2203579 / 6250000) (352572641 / 1000000000) (Real.log (1422723 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1422723 / 1000000) = -Real.log (1000000 / 1422723) := by
    rw [show ((1422723 / 1000000) : ℝ) = ((1000000 / 1422723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (274716529 / 500000000) ≤ -Real.log (577277 / 1000000) ∧
    -Real.log (577277 / 1000000) ≤ (549433059 / 1000000000) := by
  have h := checkLog_sound (w := (422723 / 1577277)) (n := 12)
    (lo := (274716529 / 500000000)) (hi := (549433059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 577277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 577277) = 1/(577277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-549433059 / 1000000000) (-274716529 / 500000000) (Real.log (577277 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (353760501 / 1000000000) ≤ -Real.log (500000 / 712207) ∧
    -Real.log (500000 / 712207) ≤ (176880251 / 500000000) := by
  have h := checkLog_sound (w := (212207 / 1212207)) (n := 12)
    (lo := (353760501 / 1000000000)) (hi := (176880251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712207 / 500000) = 1/(500000 / 712207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (353760501 / 1000000000) (176880251 / 500000000) (Real.log (712207 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (712207 / 500000) = -Real.log (500000 / 712207) := by
    rw [show ((712207 / 500000) : ℝ) = ((500000 / 712207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (276183313 / 500000000) ≤ -Real.log (287793 / 500000) ∧
    -Real.log (287793 / 500000) ≤ (552366627 / 1000000000) := by
  have h := checkLog_sound (w := (212207 / 787793)) (n := 12)
    (lo := (276183313 / 500000000)) (hi := (552366627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 287793) = 1/(287793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-552366627 / 1000000000) (-276183313 / 500000000) (Real.log (287793 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (246393217 / 200000000) ≤ -Real.log (250000000000 / 856990645929) ∧
    -Real.log (250000000000 / 856990645929) ≤ (1231966087 / 1000000000) := by
  have h := checkLog_sound (w := (356990645929 / 1356990645929)) (n := 12)
    (lo := (107763781 / 200000000)) (hi := (269409453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856990645929 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(856990645929 / 500000000000) = 1/(250000000000 / 856990645929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (246393217 / 200000000) (1231966087 / 1000000000) (Real.log (856990645929 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (856990645929 / 250000000000) = -Real.log (250000000000 / 856990645929) := by
    rw [show ((856990645929 / 250000000000) : ℝ) = ((250000000000 / 856990645929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1237293169 / 1000000000) ≤ -Real.log (500000000000 / 1723136178207) ∧
    -Real.log (500000000000 / 1723136178207) ≤ (1237293171 / 1000000000) := by
  have h := checkLog_sound (w := (723136178207 / 2723136178207)) (n := 12)
    (lo := (544145989 / 1000000000)) (hi := (54414599 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723136178207 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1723136178207 / 1000000000000) = 1/(500000000000 / 1723136178207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1237293169 / 1000000000) (1237293171 / 1000000000) (Real.log (1723136178207 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1723136178207 / 500000000000) = -Real.log (500000000000 / 1723136178207) := by
    rw [show ((1723136178207 / 500000000000) : ℝ) = ((500000000000 / 1723136178207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (451002849 / 500000000) ≤ -Real.log (125000000000 / 308067660759) ∧
    -Real.log (125000000000 / 308067660759) ≤ (9020057 / 10000000) := by
  have h := checkLog_sound (w := (58067660759 / 558067660759)) (n := 12)
    (lo := (104429259 / 500000000)) (hi := (208858519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308067660759 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(308067660759 / 250000000000) = 1/(125000000000 / 308067660759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (451002849 / 500000000) (9020057 / 10000000) (Real.log (308067660759 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (308067660759 / 125000000000) = -Real.log (125000000000 / 308067660759) := by
    rw [show ((308067660759 / 125000000000) : ℝ) = ((125000000000 / 308067660759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (906127127 / 1000000000) ≤ -Real.log (15625000000 / 38667494953) ∧
    -Real.log (15625000000 / 38667494953) ≤ (906127129 / 1000000000) := by
  have h := checkLog_sound (w := (7417494953 / 69917494953)) (n := 12)
    (lo := (212979947 / 1000000000)) (hi := (53244987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38667494953 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(38667494953 / 31250000000) = 1/(15625000000 / 38667494953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (906127127 / 1000000000) (906127129 / 1000000000) (Real.log (38667494953 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (38667494953 / 15625000000) = -Real.log (15625000000 / 38667494953) := by
    rw [show ((38667494953 / 15625000000) : ℝ) = ((15625000000 / 38667494953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0116

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0117Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0117
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

theorem reflection_log_1_neg : (319021751 / 1000000000) ≤ -Real.log (1280 / 1761) ∧
    -Real.log (1280 / 1761) ≤ (39877719 / 125000000) := by
  have h := checkLog_sound (w := (481 / 3041)) (n := 12)
    (lo := (319021751 / 1000000000)) (hi := (39877719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1761 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1761 / 1280) = 1/(1280 / 1761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (319021751 / 1000000000) (39877719 / 125000000) (Real.log (1761 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1761 / 1280) = -Real.log (1280 / 1761) := by
    rw [show ((1761 / 1280) : ℝ) = ((1280 / 1761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (471254411 / 1000000000) ≤ -Real.log (799 / 1280) ∧
    -Real.log (799 / 1280) ≤ (117813603 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2079)) (n := 12)
    (lo := (471254411 / 1000000000)) (hi := (117813603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 799) = 1/(799 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-117813603 / 250000000) (-471254411 / 1000000000) (Real.log (799 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (318169599 / 1000000000) ≤ -Real.log (2560 / 3519) ∧
    -Real.log (2560 / 3519) ≤ (24857 / 78125) := by
  have h := checkLog_sound (w := (959 / 6079)) (n := 12)
    (lo := (318169599 / 1000000000)) (hi := (24857 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3519 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3519 / 2560) = 1/(2560 / 3519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (318169599 / 1000000000) (24857 / 78125) (Real.log (3519 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3519 / 2560) = -Real.log (2560 / 3519) := by
    rw [show ((3519 / 2560) : ℝ) = ((2560 / 3519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58672353 / 125000000) ≤ -Real.log (1601 / 2560) ∧
    -Real.log (1601 / 2560) ≤ (18775153 / 40000000) := by
  have h := checkLog_sound (w := (959 / 4161)) (n := 12)
    (lo := (58672353 / 125000000)) (hi := (18775153 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1601) = 1/(1601 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18775153 / 40000000) (-58672353 / 125000000) (Real.log (1601 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (280254123 / 500000000) ≤ -Real.log (640 / 1121) ∧
    -Real.log (640 / 1121) ≤ (560508247 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 1761)) (n := 12)
    (lo := (280254123 / 500000000)) (hi := (560508247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121 / 640) = 1/(640 / 1121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (280254123 / 500000000) (560508247 / 1000000000) (Real.log (1121 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1121 / 640) = -Real.log (640 / 1121) := by
    rw [show ((1121 / 640) : ℝ) = ((640 / 1121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1392563973 / 1000000000) ≤ -Real.log (159 / 640) ∧
    -Real.log (159 / 640) ≤ (174070497 / 125000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 159) = 1/(159 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-174070497 / 125000000) (-1392563973 / 1000000000) (Real.log (159 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (559169259 / 1000000000) ≤ -Real.log (1280 / 2239) ∧
    -Real.log (1280 / 2239) ≤ (27958463 / 50000000) := by
  have h := checkLog_sound (w := (959 / 3519)) (n := 12)
    (lo := (559169259 / 1000000000)) (hi := (27958463 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2239 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2239 / 1280) = 1/(1280 / 2239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (559169259 / 1000000000) (27958463 / 50000000) (Real.log (2239 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2239 / 1280) = -Real.log (1280 / 2239) := by
    rw [show ((2239 / 1280) : ℝ) = ((1280 / 2239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1383174233 / 1000000000) ≤ -Real.log (321 / 1280) ∧
    -Real.log (321 / 1280) ≤ (276634847 / 200000000) := by
  have h := checkLog_sound (w := (319 / 961)) (n := 12)
    (lo := (690027053 / 1000000000)) (hi := (345013527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 321) = 1/(321 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-276634847 / 200000000) (-1383174233 / 1000000000) (Real.log (321 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (435974267 / 1000000000) ≤ -Real.log (1000000 / 1546469) ∧
    -Real.log (1000000 / 1546469) ≤ (108993567 / 250000000) := by
  have h := checkLog_sound (w := (546469 / 2546469)) (n := 12)
    (lo := (435974267 / 1000000000)) (hi := (108993567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1546469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1546469 / 1000000) = 1/(1000000 / 1546469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (435974267 / 1000000000) (108993567 / 250000000) (Real.log (1546469 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1546469 / 1000000) = -Real.log (1000000 / 1546469) := by
    rw [show ((1546469 / 1000000) : ℝ) = ((1000000 / 1546469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (790691653 / 1000000000) ≤ -Real.log (453531 / 1000000) ∧
    -Real.log (453531 / 1000000) ≤ (158138331 / 200000000) := by
  have h := checkLog_sound (w := (46469 / 953531)) (n := 12)
    (lo := (97544473 / 1000000000)) (hi := (48772237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 453531) = 1/(453531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158138331 / 200000000) (-790691653 / 1000000000) (Real.log (453531 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (437174347 / 1000000000) ≤ -Real.log (500000 / 774163) ∧
    -Real.log (500000 / 774163) ≤ (109293587 / 250000000) := by
  have h := checkLog_sound (w := (274163 / 1274163)) (n := 12)
    (lo := (437174347 / 1000000000)) (hi := (109293587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774163 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774163 / 500000) = 1/(500000 / 774163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (437174347 / 1000000000) (109293587 / 250000000) (Real.log (774163 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (774163 / 500000) = -Real.log (500000 / 774163) := by
    rw [show ((774163 / 500000) : ℝ) = ((500000 / 774163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (794794597 / 1000000000) ≤ -Real.log (225837 / 500000) ∧
    -Real.log (225837 / 500000) ≤ (794794599 / 1000000000) := by
  have h := checkLog_sound (w := (24163 / 475837)) (n := 12)
    (lo := (101647417 / 1000000000)) (hi := (50823709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225837) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 225837) = 1/(225837 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-794794599 / 1000000000) (-794794597 / 1000000000) (Real.log (225837 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (175693443 / 500000000) ≤ -Real.log (1000000 / 1421037) ∧
    -Real.log (1000000 / 1421037) ≤ (351386887 / 1000000000) := by
  have h := checkLog_sound (w := (421037 / 2421037)) (n := 12)
    (lo := (175693443 / 500000000)) (hi := (351386887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421037 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421037 / 1000000) = 1/(1000000 / 1421037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (175693443 / 500000000) (351386887 / 1000000000) (Real.log (1421037 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1421037 / 1000000) = -Real.log (1000000 / 1421037) := by
    rw [show ((1421037 / 1000000) : ℝ) = ((1000000 / 1421037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (273258353 / 500000000) ≤ -Real.log (578963 / 1000000) ∧
    -Real.log (578963 / 1000000) ≤ (546516707 / 1000000000) := by
  have h := checkLog_sound (w := (421037 / 1578963)) (n := 12)
    (lo := (273258353 / 500000000)) (hi := (546516707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 578963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 578963) = 1/(578963 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-546516707 / 1000000000) (-273258353 / 500000000) (Real.log (578963 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (352573343 / 1000000000) ≤ -Real.log (250000 / 355681) ∧
    -Real.log (250000 / 355681) ≤ (11017917 / 31250000) := by
  have h := checkLog_sound (w := (105681 / 605681)) (n := 12)
    (lo := (352573343 / 1000000000)) (hi := (11017917 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355681 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355681 / 250000) = 1/(250000 / 355681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (352573343 / 1000000000) (11017917 / 31250000) (Real.log (355681 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (355681 / 250000) = -Real.log (250000 / 355681) := by
    rw [show ((355681 / 250000) : ℝ) = ((250000 / 355681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (54943479 / 100000000) ≤ -Real.log (144319 / 250000) ∧
    -Real.log (144319 / 250000) ≤ (549434791 / 1000000000) := by
  have h := checkLog_sound (w := (105681 / 394319)) (n := 12)
    (lo := (54943479 / 100000000)) (hi := (549434791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 144319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 144319) = 1/(144319 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-549434791 / 1000000000) (-54943479 / 100000000) (Real.log (144319 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1226665921 / 1000000000) ≤ -Real.log (500000000000 / 1704920942559) ∧
    -Real.log (500000000000 / 1704920942559) ≤ (1226665923 / 1000000000) := by
  have h := checkLog_sound (w := (704920942559 / 2704920942559)) (n := 12)
    (lo := (533518741 / 1000000000)) (hi := (266759371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1704920942559 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1704920942559 / 1000000000000) = 1/(500000000000 / 1704920942559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1226665921 / 1000000000) (1226665923 / 1000000000) (Real.log (1704920942559 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1704920942559 / 500000000000) = -Real.log (500000000000 / 1704920942559) := by
    rw [show ((1704920942559 / 500000000000) : ℝ) = ((500000000000 / 1704920942559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (246393789 / 200000000) ≤ -Real.log (500000000000 / 1713986193583) ∧
    -Real.log (500000000000 / 1713986193583) ≤ (1231968947 / 1000000000) := by
  have h := checkLog_sound (w := (713986193583 / 2713986193583)) (n := 12)
    (lo := (107764353 / 200000000)) (hi := (269410883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713986193583 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1713986193583 / 1000000000000) = 1/(500000000000 / 1713986193583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (246393789 / 200000000) (1231968947 / 1000000000) (Real.log (1713986193583 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1713986193583 / 500000000000) = -Real.log (500000000000 / 1713986193583) := by
    rw [show ((1713986193583 / 500000000000) : ℝ) = ((500000000000 / 1713986193583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (112237949 / 125000000) ≤ -Real.log (62500000000 / 153403261521) ∧
    -Real.log (62500000000 / 153403261521) ≤ (448951797 / 500000000) := by
  have h := checkLog_sound (w := (28403261521 / 278403261521)) (n := 12)
    (lo := (51189103 / 250000000)) (hi := (204756413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153403261521 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153403261521 / 125000000000) = 1/(62500000000 / 153403261521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (112237949 / 125000000) (448951797 / 500000000) (Real.log (153403261521 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (153403261521 / 62500000000) = -Real.log (62500000000 / 153403261521) := by
    rw [show ((153403261521 / 62500000000) : ℝ) = ((62500000000 / 153403261521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (902008133 / 1000000000) ≤ -Real.log (500000000000 / 1232273643803) ∧
    -Real.log (500000000000 / 1232273643803) ≤ (180401627 / 200000000) := by
  have h := checkLog_sound (w := (232273643803 / 2232273643803)) (n := 12)
    (lo := (208860953 / 1000000000)) (hi := (104430477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232273643803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1232273643803 / 1000000000000) = 1/(500000000000 / 1232273643803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (902008133 / 1000000000) (180401627 / 200000000) (Real.log (1232273643803 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1232273643803 / 500000000000) = -Real.log (500000000000 / 1232273643803) := by
    rw [show ((1232273643803 / 500000000000) : ℝ) = ((500000000000 / 1232273643803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0117

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0118Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0118
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

theorem reflection_log_1_neg : (318169599 / 1000000000) ≤ -Real.log (2560 / 3519) ∧
    -Real.log (2560 / 3519) ≤ (24857 / 78125) := by
  have h := checkLog_sound (w := (959 / 6079)) (n := 12)
    (lo := (318169599 / 1000000000)) (hi := (24857 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3519 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3519 / 2560) = 1/(2560 / 3519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (318169599 / 1000000000) (24857 / 78125) (Real.log (3519 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3519 / 2560) = -Real.log (2560 / 3519) := by
    rw [show ((3519 / 2560) : ℝ) = ((2560 / 3519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58672353 / 125000000) ≤ -Real.log (1601 / 2560) ∧
    -Real.log (1601 / 2560) ≤ (18775153 / 40000000) := by
  have h := checkLog_sound (w := (959 / 4161)) (n := 12)
    (lo := (58672353 / 125000000)) (hi := (18775153 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1601) = 1/(1601 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18775153 / 40000000) (-58672353 / 125000000) (Real.log (1601 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (317316721 / 1000000000) ≤ -Real.log (640 / 879) ∧
    -Real.log (640 / 879) ≤ (158658361 / 500000000) := by
  have h := checkLog_sound (w := (239 / 1519)) (n := 12)
    (lo := (317316721 / 1000000000)) (hi := (158658361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879 / 640) = 1/(640 / 879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (317316721 / 1000000000) (158658361 / 500000000) (Real.log (879 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (879 / 640) = -Real.log (640 / 879) := by
    rw [show ((879 / 640) : ℝ) = ((640 / 879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (467506749 / 1000000000) ≤ -Real.log (401 / 640) ∧
    -Real.log (401 / 640) ≤ (1870027 / 4000000) := by
  have h := checkLog_sound (w := (239 / 1041)) (n := 12)
    (lo := (467506749 / 1000000000)) (hi := (1870027 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 401) = 1/(401 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1870027 / 4000000) (-467506749 / 1000000000) (Real.log (401 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (559169259 / 1000000000) ≤ -Real.log (1280 / 2239) ∧
    -Real.log (1280 / 2239) ≤ (27958463 / 50000000) := by
  have h := checkLog_sound (w := (959 / 3519)) (n := 12)
    (lo := (559169259 / 1000000000)) (hi := (27958463 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2239 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2239 / 1280) = 1/(1280 / 2239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (559169259 / 1000000000) (27958463 / 50000000) (Real.log (2239 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2239 / 1280) = -Real.log (1280 / 2239) := by
    rw [show ((2239 / 1280) : ℝ) = ((1280 / 2239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1383174233 / 1000000000) ≤ -Real.log (321 / 1280) ∧
    -Real.log (321 / 1280) ≤ (276634847 / 200000000) := by
  have h := checkLog_sound (w := (319 / 961)) (n := 12)
    (lo := (690027053 / 1000000000)) (hi := (345013527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 321) = 1/(321 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-276634847 / 200000000) (-1383174233 / 1000000000) (Real.log (321 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (557828477 / 1000000000) ≤ -Real.log (320 / 559) ∧
    -Real.log (320 / 559) ≤ (278914239 / 500000000) := by
  have h := checkLog_sound (w := (239 / 879)) (n := 12)
    (lo := (557828477 / 1000000000)) (hi := (278914239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559 / 320) = 1/(320 / 559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (557828477 / 1000000000) (278914239 / 500000000) (Real.log (559 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (559 / 320) = -Real.log (320 / 559) := by
    rw [show ((559 / 320) : ℝ) = ((320 / 559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8586699 / 6250000) ≤ -Real.log (81 / 320) ∧
    -Real.log (81 / 320) ≤ (686935921 / 500000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 81) = 1/(81 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-686935921 / 500000000) (-8586699 / 6250000) (Real.log (81 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10869351 / 25000000) ≤ -Real.log (500000 / 772307) ∧
    -Real.log (500000 / 772307) ≤ (434774041 / 1000000000) := by
  have h := checkLog_sound (w := (272307 / 1272307)) (n := 12)
    (lo := (10869351 / 25000000)) (hi := (434774041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772307 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772307 / 500000) = 1/(500000 / 772307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10869351 / 25000000) (434774041 / 1000000000) (Real.log (772307 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (772307 / 500000) = -Real.log (500000 / 772307) := by
    rw [show ((772307 / 500000) : ℝ) = ((500000 / 772307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (786609867 / 1000000000) ≤ -Real.log (227693 / 500000) ∧
    -Real.log (227693 / 500000) ≤ (786609869 / 1000000000) := by
  have h := checkLog_sound (w := (22307 / 477693)) (n := 12)
    (lo := (93462687 / 1000000000)) (hi := (2920709 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227693) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 227693) = 1/(227693 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-786609869 / 1000000000) (-786609867 / 1000000000) (Real.log (227693 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (217987457 / 500000000) ≤ -Real.log (100000 / 154647) ∧
    -Real.log (100000 / 154647) ≤ (87194983 / 200000000) := by
  have h := checkLog_sound (w := (54647 / 254647)) (n := 12)
    (lo := (217987457 / 500000000)) (hi := (87194983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154647 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154647 / 100000) = 1/(100000 / 154647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (217987457 / 500000000) (87194983 / 200000000) (Real.log (154647 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (154647 / 100000) = -Real.log (100000 / 154647) := by
    rw [show ((154647 / 100000) : ℝ) = ((100000 / 154647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (395346929 / 500000000) ≤ -Real.log (45353 / 100000) ∧
    -Real.log (45353 / 100000) ≤ (39534693 / 50000000) := by
  have h := checkLog_sound (w := (4647 / 95353)) (n := 12)
    (lo := (48773339 / 500000000)) (hi := (97546679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45353) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 45353) = 1/(45353 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-39534693 / 50000000) (-395346929 / 500000000) (Real.log (45353 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (350203247 / 1000000000) ≤ -Real.log (250000 / 354839) ∧
    -Real.log (250000 / 354839) ≤ (21887703 / 62500000) := by
  have h := checkLog_sound (w := (104839 / 604839)) (n := 12)
    (lo := (350203247 / 1000000000)) (hi := (21887703 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354839 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354839 / 250000) = 1/(250000 / 354839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (350203247 / 1000000000) (21887703 / 62500000) (Real.log (354839 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (354839 / 250000) = -Real.log (250000 / 354839) := by
    rw [show ((354839 / 250000) : ℝ) = ((250000 / 354839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (271808723 / 500000000) ≤ -Real.log (145161 / 250000) ∧
    -Real.log (145161 / 250000) ≤ (543617447 / 1000000000) := by
  have h := checkLog_sound (w := (104839 / 395161)) (n := 12)
    (lo := (271808723 / 500000000)) (hi := (543617447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 145161) = 1/(145161 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-543617447 / 1000000000) (-271808723 / 500000000) (Real.log (145161 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (35138759 / 100000000) ≤ -Real.log (500000 / 710519) ∧
    -Real.log (500000 / 710519) ≤ (351387591 / 1000000000) := by
  have h := checkLog_sound (w := (210519 / 1210519)) (n := 12)
    (lo := (35138759 / 100000000)) (hi := (351387591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710519 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710519 / 500000) = 1/(500000 / 710519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (35138759 / 100000000) (351387591 / 1000000000) (Real.log (710519 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (710519 / 500000) = -Real.log (500000 / 710519) := by
    rw [show ((710519 / 500000) : ℝ) = ((500000 / 710519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (546518433 / 1000000000) ≤ -Real.log (289481 / 500000) ∧
    -Real.log (289481 / 500000) ≤ (273259217 / 500000000) := by
  have h := checkLog_sound (w := (210519 / 789481)) (n := 12)
    (lo := (546518433 / 1000000000)) (hi := (273259217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 289481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 289481) = 1/(289481 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-273259217 / 500000000) (-546518433 / 1000000000) (Real.log (289481 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (305345977 / 250000000) ≤ -Real.log (500000000000 / 1695939269103) ∧
    -Real.log (500000000000 / 1695939269103) ≤ (122138391 / 100000000) := by
  have h := checkLog_sound (w := (695939269103 / 2695939269103)) (n := 12)
    (lo := (66029591 / 125000000)) (hi := (528236729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1695939269103 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1695939269103 / 1000000000000) = 1/(500000000000 / 1695939269103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (305345977 / 250000000) (122138391 / 100000000) (Real.log (1695939269103 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1695939269103 / 500000000000) = -Real.log (500000000000 / 1695939269103) := by
    rw [show ((1695939269103 / 500000000000) : ℝ) = ((500000000000 / 1695939269103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1226668773 / 1000000000) ≤ -Real.log (500000000000 / 1704925804247) ∧
    -Real.log (500000000000 / 1704925804247) ≤ (49066751 / 40000000) := by
  have h := checkLog_sound (w := (704925804247 / 2704925804247)) (n := 12)
    (lo := (533521593 / 1000000000)) (hi := (266760797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1704925804247 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1704925804247 / 1000000000000) = 1/(500000000000 / 1704925804247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1226668773 / 1000000000) (49066751 / 40000000) (Real.log (1704925804247 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1704925804247 / 500000000000) = -Real.log (500000000000 / 1704925804247) := by
    rw [show ((1704925804247 / 500000000000) : ℝ) = ((500000000000 / 1704925804247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (893820693 / 1000000000) ≤ -Real.log (500000000000 / 1222225666673) ∧
    -Real.log (500000000000 / 1222225666673) ≤ (178764139 / 200000000) := by
  have h := checkLog_sound (w := (222225666673 / 2222225666673)) (n := 12)
    (lo := (200673513 / 1000000000)) (hi := (100336757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222225666673 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1222225666673 / 1000000000000) = 1/(500000000000 / 1222225666673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (893820693 / 1000000000) (178764139 / 200000000) (Real.log (1222225666673 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1222225666673 / 500000000000) = -Real.log (500000000000 / 1222225666673) := by
    rw [show ((1222225666673 / 500000000000) : ℝ) = ((500000000000 / 1222225666673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (897906023 / 1000000000) ≤ -Real.log (125000000000 / 306807268871) ∧
    -Real.log (125000000000 / 306807268871) ≤ (35916241 / 40000000) := by
  have h := checkLog_sound (w := (56807268871 / 556807268871)) (n := 12)
    (lo := (204758843 / 1000000000)) (hi := (51189711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306807268871 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(306807268871 / 250000000000) = 1/(125000000000 / 306807268871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (897906023 / 1000000000) (35916241 / 40000000) (Real.log (306807268871 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (306807268871 / 125000000000) = -Real.log (125000000000 / 306807268871) := by
    rw [show ((306807268871 / 125000000000) : ℝ) = ((125000000000 / 306807268871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0118

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0119Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0119
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

theorem reflection_log_1_neg : (317316721 / 1000000000) ≤ -Real.log (640 / 879) ∧
    -Real.log (640 / 879) ≤ (158658361 / 500000000) := by
  have h := checkLog_sound (w := (239 / 1519)) (n := 12)
    (lo := (317316721 / 1000000000)) (hi := (158658361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879 / 640) = 1/(640 / 879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (317316721 / 1000000000) (158658361 / 500000000) (Real.log (879 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (879 / 640) = -Real.log (640 / 879) := by
    rw [show ((879 / 640) : ℝ) = ((640 / 879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (467506749 / 1000000000) ≤ -Real.log (401 / 640) ∧
    -Real.log (401 / 640) ≤ (1870027 / 4000000) := by
  have h := checkLog_sound (w := (239 / 1041)) (n := 12)
    (lo := (467506749 / 1000000000)) (hi := (1870027 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 401) = 1/(401 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1870027 / 4000000) (-467506749 / 1000000000) (Real.log (401 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (158231557 / 500000000) ≤ -Real.log (2560 / 3513) ∧
    -Real.log (2560 / 3513) ≤ (63292623 / 200000000) := by
  have h := checkLog_sound (w := (953 / 6073)) (n := 12)
    (lo := (158231557 / 500000000)) (hi := (63292623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3513 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3513 / 2560) = 1/(2560 / 3513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (158231557 / 500000000) (63292623 / 200000000) (Real.log (3513 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3513 / 2560) = -Real.log (2560 / 3513) := by
    rw [show ((3513 / 2560) : ℝ) = ((2560 / 3513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (465638171 / 1000000000) ≤ -Real.log (1607 / 2560) ∧
    -Real.log (1607 / 2560) ≤ (116409543 / 250000000) := by
  have h := checkLog_sound (w := (953 / 4167)) (n := 12)
    (lo := (465638171 / 1000000000)) (hi := (116409543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1607) = 1/(1607 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-116409543 / 250000000) (-465638171 / 1000000000) (Real.log (1607 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (557828477 / 1000000000) ≤ -Real.log (320 / 559) ∧
    -Real.log (320 / 559) ≤ (278914239 / 500000000) := by
  have h := checkLog_sound (w := (239 / 879)) (n := 12)
    (lo := (557828477 / 1000000000)) (hi := (278914239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559 / 320) = 1/(320 / 559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (557828477 / 1000000000) (278914239 / 500000000) (Real.log (559 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (559 / 320) = -Real.log (320 / 559) := by
    rw [show ((559 / 320) : ℝ) = ((320 / 559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (8586699 / 6250000) ≤ -Real.log (81 / 320) ∧
    -Real.log (81 / 320) ≤ (686935921 / 500000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 81) = 1/(81 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-686935921 / 500000000) (-8586699 / 6250000) (Real.log (81 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (278242947 / 500000000) ≤ -Real.log (1280 / 2233) ∧
    -Real.log (1280 / 2233) ≤ (111297179 / 200000000) := by
  have h := checkLog_sound (w := (953 / 3513)) (n := 12)
    (lo := (278242947 / 500000000)) (hi := (111297179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2233 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2233 / 1280) = 1/(1280 / 2233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (278242947 / 500000000) (111297179 / 200000000) (Real.log (2233 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2233 / 1280) = -Real.log (1280 / 2233) := by
    rw [show ((2233 / 1280) : ℝ) = ((1280 / 2233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (272931037 / 200000000) ≤ -Real.log (327 / 1280) ∧
    -Real.log (327 / 1280) ≤ (1364655187 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 967)) (n := 12)
    (lo := (134301601 / 200000000)) (hi := (335754003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 327) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 327) = 1/(327 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1364655187 / 1000000000) (-272931037 / 200000000) (Real.log (327 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (108393579 / 250000000) ≤ -Real.log (500000 / 771381) ∧
    -Real.log (500000 / 771381) ≤ (433574317 / 1000000000) := by
  have h := checkLog_sound (w := (271381 / 1271381)) (n := 12)
    (lo := (108393579 / 250000000)) (hi := (433574317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771381 / 500000) = 1/(500000 / 771381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (108393579 / 250000000) (433574317 / 1000000000) (Real.log (771381 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (771381 / 500000) = -Real.log (500000 / 771381) := by
    rw [show ((771381 / 500000) : ℝ) = ((500000 / 771381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (156510247 / 200000000) ≤ -Real.log (228619 / 500000) ∧
    -Real.log (228619 / 500000) ≤ (782551237 / 1000000000) := by
  have h := checkLog_sound (w := (21381 / 478619)) (n := 12)
    (lo := (17880811 / 200000000)) (hi := (11175507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228619) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 228619) = 1/(228619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-782551237 / 1000000000) (-156510247 / 200000000) (Real.log (228619 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13586709 / 31250000) ≤ -Real.log (200000 / 308923) ∧
    -Real.log (200000 / 308923) ≤ (434774689 / 1000000000) := by
  have h := checkLog_sound (w := (108923 / 508923)) (n := 12)
    (lo := (13586709 / 31250000)) (hi := (434774689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308923 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308923 / 200000) = 1/(200000 / 308923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13586709 / 31250000) (434774689 / 1000000000) (Real.log (308923 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (308923 / 200000) = -Real.log (200000 / 308923) := by
    rw [show ((308923 / 200000) : ℝ) = ((200000 / 308923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (786612063 / 1000000000) ≤ -Real.log (91077 / 200000) ∧
    -Real.log (91077 / 200000) ≤ (157322413 / 200000000) := by
  have h := checkLog_sound (w := (8923 / 191077)) (n := 12)
    (lo := (93464883 / 1000000000)) (hi := (23366221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91077) = 1/(91077 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-157322413 / 200000000) (-786612063 / 1000000000) (Real.log (91077 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (87255433 / 250000000) ≤ -Real.log (12500 / 17721) ∧
    -Real.log (12500 / 17721) ≤ (349021733 / 1000000000) := by
  have h := checkLog_sound (w := (5221 / 30221)) (n := 12)
    (lo := (87255433 / 250000000)) (hi := (349021733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17721 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17721 / 12500) = 1/(12500 / 17721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (87255433 / 250000000) (349021733 / 1000000000) (Real.log (17721 / 12500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (17721 / 12500) = -Real.log (12500 / 17721) := by
    rw [show ((17721 / 12500) : ℝ) = ((12500 / 17721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (270367577 / 500000000) ≤ -Real.log (7279 / 12500) ∧
    -Real.log (7279 / 12500) ≤ (108147031 / 200000000) := by
  have h := checkLog_sound (w := (5221 / 19779)) (n := 12)
    (lo := (270367577 / 500000000)) (hi := (108147031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 7279) = 1/(7279 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-108147031 / 200000000) (-270367577 / 500000000) (Real.log (7279 / 12500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21887747 / 62500000) ≤ -Real.log (1000000 / 1419357) ∧
    -Real.log (1000000 / 1419357) ≤ (350203953 / 1000000000) := by
  have h := checkLog_sound (w := (419357 / 2419357)) (n := 12)
    (lo := (21887747 / 62500000)) (hi := (350203953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1419357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1419357 / 1000000) = 1/(1000000 / 1419357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21887747 / 62500000) (350203953 / 1000000000) (Real.log (1419357 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1419357 / 1000000) = -Real.log (1000000 / 1419357) := by
    rw [show ((1419357 / 1000000) : ℝ) = ((1000000 / 1419357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16988099 / 31250000) ≤ -Real.log (580643 / 1000000) ∧
    -Real.log (580643 / 1000000) ≤ (543619169 / 1000000000) := by
  have h := checkLog_sound (w := (419357 / 1580643)) (n := 12)
    (lo := (16988099 / 31250000)) (hi := (543619169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 580643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 580643) = 1/(580643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-543619169 / 1000000000) (-16988099 / 31250000) (Real.log (580643 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1216125551 / 1000000000) ≤ -Real.log (31250000000 / 105440301331) ∧
    -Real.log (31250000000 / 105440301331) ≤ (1216125553 / 1000000000) := by
  have h := checkLog_sound (w := (42940301331 / 167940301331)) (n := 12)
    (lo := (522978371 / 1000000000)) (hi := (130744593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105440301331 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(105440301331 / 62500000000) = 1/(31250000000 / 105440301331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1216125551 / 1000000000) (1216125553 / 1000000000) (Real.log (105440301331 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (105440301331 / 31250000000) = -Real.log (31250000000 / 105440301331) := by
    rw [show ((105440301331 / 31250000000) : ℝ) = ((31250000000 / 105440301331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1221386751 / 1000000000) ≤ -Real.log (3906250000 / 13249563213) ∧
    -Real.log (3906250000 / 13249563213) ≤ (1221386753 / 1000000000) := by
  have h := checkLog_sound (w := (5437063213 / 21062063213)) (n := 12)
    (lo := (528239571 / 1000000000)) (hi := (132059893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13249563213 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(13249563213 / 7812500000) = 1/(3906250000 / 13249563213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1221386751 / 1000000000) (1221386753 / 1000000000) (Real.log (13249563213 / 3906250000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13249563213 / 3906250000) = -Real.log (3906250000 / 13249563213) := by
    rw [show ((13249563213 / 3906250000) : ℝ) = ((3906250000 / 13249563213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (444878443 / 500000000) ≤ -Real.log (125000000000 / 304317213903) ∧
    -Real.log (125000000000 / 304317213903) ≤ (111219611 / 125000000) := by
  have h := checkLog_sound (w := (54317213903 / 554317213903)) (n := 12)
    (lo := (98304853 / 500000000)) (hi := (196609707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304317213903 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(304317213903 / 250000000000) = 1/(125000000000 / 304317213903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (444878443 / 500000000) (111219611 / 125000000) (Real.log (304317213903 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (304317213903 / 125000000000) = -Real.log (125000000000 / 304317213903) := by
    rw [show ((304317213903 / 125000000000) : ℝ) = ((125000000000 / 304317213903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (11172789 / 12500000) ≤ -Real.log (25000000000 / 61111431637) ∧
    -Real.log (25000000000 / 61111431637) ≤ (446911561 / 500000000) := by
  have h := checkLog_sound (w := (11111431637 / 111111431637)) (n := 12)
    (lo := (10033797 / 50000000)) (hi := (200675941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61111431637 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(61111431637 / 50000000000) = 1/(25000000000 / 61111431637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (11172789 / 12500000) (446911561 / 500000000) (Real.log (61111431637 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (61111431637 / 25000000000) = -Real.log (25000000000 / 61111431637) := by
    rw [show ((61111431637 / 25000000000) : ℝ) = ((25000000000 / 61111431637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0119

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0120Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0120
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

theorem reflection_log_1_neg : (158231557 / 500000000) ≤ -Real.log (2560 / 3513) ∧
    -Real.log (2560 / 3513) ≤ (63292623 / 200000000) := by
  have h := checkLog_sound (w := (953 / 6073)) (n := 12)
    (lo := (158231557 / 500000000)) (hi := (63292623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3513 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3513 / 2560) = 1/(2560 / 3513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (158231557 / 500000000) (63292623 / 200000000) (Real.log (3513 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3513 / 2560) = -Real.log (2560 / 3513) := by
    rw [show ((3513 / 2560) : ℝ) = ((2560 / 3513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (465638171 / 1000000000) ≤ -Real.log (1607 / 2560) ∧
    -Real.log (1607 / 2560) ≤ (116409543 / 250000000) := by
  have h := checkLog_sound (w := (953 / 4167)) (n := 12)
    (lo := (465638171 / 1000000000)) (hi := (116409543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1607) = 1/(1607 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-116409543 / 250000000) (-465638171 / 1000000000) (Real.log (1607 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157804389 / 500000000) ≤ -Real.log (256 / 351) ∧
    -Real.log (256 / 351) ≤ (315608779 / 1000000000) := by
  have h := checkLog_sound (w := (95 / 607)) (n := 12)
    (lo := (157804389 / 500000000)) (hi := (315608779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351 / 256) = 1/(256 / 351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (157804389 / 500000000) (315608779 / 1000000000) (Real.log (351 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (351 / 256) = -Real.log (256 / 351) := by
    rw [show ((351 / 256) : ℝ) = ((256 / 351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (463773079 / 1000000000) ≤ -Real.log (161 / 256) ∧
    -Real.log (161 / 256) ≤ (11594327 / 25000000) := by
  have h := checkLog_sound (w := (95 / 417)) (n := 12)
    (lo := (463773079 / 1000000000)) (hi := (11594327 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 161) = 1/(161 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-11594327 / 25000000) (-463773079 / 1000000000) (Real.log (161 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (278242947 / 500000000) ≤ -Real.log (1280 / 2233) ∧
    -Real.log (1280 / 2233) ≤ (111297179 / 200000000) := by
  have h := checkLog_sound (w := (953 / 3513)) (n := 12)
    (lo := (278242947 / 500000000)) (hi := (111297179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2233 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2233 / 1280) = 1/(1280 / 2233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (278242947 / 500000000) (111297179 / 200000000) (Real.log (2233 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2233 / 1280) = -Real.log (1280 / 2233) := by
    rw [show ((2233 / 1280) : ℝ) = ((1280 / 2233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (272931037 / 200000000) ≤ -Real.log (327 / 1280) ∧
    -Real.log (327 / 1280) ≤ (1364655187 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 967)) (n := 12)
    (lo := (134301601 / 200000000)) (hi := (335754003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 327) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 327) = 1/(327 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1364655187 / 1000000000) (-272931037 / 200000000) (Real.log (327 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (555141507 / 1000000000) ≤ -Real.log (128 / 223) ∧
    -Real.log (128 / 223) ≤ (138785377 / 250000000) := by
  have h := checkLog_sound (w := (95 / 351)) (n := 12)
    (lo := (555141507 / 1000000000)) (hi := (138785377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223 / 128) = 1/(128 / 223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (555141507 / 1000000000) (138785377 / 250000000) (Real.log (223 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (223 / 128) = -Real.log (128 / 223) := by
    rw [show ((223 / 128) : ℝ) = ((128 / 223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1355522701 / 1000000000) ≤ -Real.log (33 / 128) ∧
    -Real.log (33 / 128) ≤ (1355522703 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 33) = 1/(33 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1355522703 / 1000000000) (-1355522701 / 1000000000) (Real.log (33 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27023403 / 62500000) ≤ -Real.log (62500 / 96307) ∧
    -Real.log (62500 / 96307) ≤ (432374449 / 1000000000) := by
  have h := checkLog_sound (w := (33807 / 158807)) (n := 12)
    (lo := (27023403 / 62500000)) (hi := (432374449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96307 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96307 / 62500) = 1/(62500 / 96307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27023403 / 62500000) (432374449 / 1000000000) (Real.log (96307 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (96307 / 62500) = -Real.log (62500 / 96307) := by
    rw [show ((96307 / 62500) : ℝ) = ((62500 / 96307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (155702673 / 200000000) ≤ -Real.log (28693 / 62500) ∧
    -Real.log (28693 / 62500) ≤ (778513367 / 1000000000) := by
  have h := checkLog_sound (w := (2557 / 59943)) (n := 12)
    (lo := (17073237 / 200000000)) (hi := (42683093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28693) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 28693) = 1/(28693 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-778513367 / 1000000000) (-155702673 / 200000000) (Real.log (28693 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (108393741 / 250000000) ≤ -Real.log (1000000 / 1542763) ∧
    -Real.log (1000000 / 1542763) ≤ (86714993 / 200000000) := by
  have h := checkLog_sound (w := (542763 / 2542763)) (n := 12)
    (lo := (108393741 / 250000000)) (hi := (86714993 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1542763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1542763 / 1000000) = 1/(1000000 / 1542763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (108393741 / 250000000) (86714993 / 200000000) (Real.log (1542763 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1542763 / 1000000) = -Real.log (1000000 / 1542763) := by
    rw [show ((1542763 / 1000000) : ℝ) = ((1000000 / 1542763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (391276711 / 500000000) ≤ -Real.log (457237 / 1000000) ∧
    -Real.log (457237 / 1000000) ≤ (48909589 / 62500000) := by
  have h := checkLog_sound (w := (42763 / 957237)) (n := 12)
    (lo := (44703121 / 500000000)) (hi := (89406243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 457237) = 1/(457237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48909589 / 62500000) (-391276711 / 500000000) (Real.log (457237 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (86960411 / 250000000) ≤ -Real.log (125000 / 177001) ∧
    -Real.log (125000 / 177001) ≤ (69568329 / 200000000) := by
  have h := checkLog_sound (w := (52001 / 302001)) (n := 12)
    (lo := (86960411 / 250000000)) (hi := (69568329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177001 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177001 / 125000) = 1/(125000 / 177001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (86960411 / 250000000) (69568329 / 200000000) (Real.log (177001 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (177001 / 125000) = -Real.log (125000 / 177001) := by
    rw [show ((177001 / 125000) : ℝ) = ((125000 / 177001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (268933997 / 500000000) ≤ -Real.log (72999 / 125000) ∧
    -Real.log (72999 / 125000) ≤ (107573599 / 200000000) := by
  have h := checkLog_sound (w := (52001 / 197999)) (n := 12)
    (lo := (268933997 / 500000000)) (hi := (107573599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 72999) = 1/(72999 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-107573599 / 200000000) (-268933997 / 500000000) (Real.log (72999 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (174511219 / 500000000) ≤ -Real.log (1000000 / 1417681) ∧
    -Real.log (1000000 / 1417681) ≤ (349022439 / 1000000000) := by
  have h := checkLog_sound (w := (417681 / 2417681)) (n := 12)
    (lo := (174511219 / 500000000)) (hi := (349022439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1417681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1417681 / 1000000) = 1/(1000000 / 1417681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (174511219 / 500000000) (349022439 / 1000000000) (Real.log (1417681 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1417681 / 1000000) = -Real.log (1000000 / 1417681) := by
    rw [show ((1417681 / 1000000) : ℝ) = ((1000000 / 1417681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (540736871 / 1000000000) ≤ -Real.log (582319 / 1000000) ∧
    -Real.log (582319 / 1000000) ≤ (67592109 / 125000000) := by
  have h := checkLog_sound (w := (417681 / 1582319)) (n := 12)
    (lo := (540736871 / 1000000000)) (hi := (67592109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 582319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 582319) = 1/(582319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-67592109 / 125000000) (-540736871 / 1000000000) (Real.log (582319 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (605443907 / 500000000) ≤ -Real.log (250000000000 / 839115812219) ∧
    -Real.log (250000000000 / 839115812219) ≤ (151360977 / 125000000) := by
  have h := checkLog_sound (w := (339115812219 / 1339115812219)) (n := 12)
    (lo := (258870317 / 500000000)) (hi := (103548127 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839115812219 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(839115812219 / 500000000000) = 1/(250000000000 / 839115812219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (605443907 / 500000000) (151360977 / 125000000) (Real.log (839115812219 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (839115812219 / 250000000000) = -Real.log (250000000000 / 839115812219) := by
    rw [show ((839115812219 / 250000000000) : ℝ) = ((250000000000 / 839115812219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1216128387 / 1000000000) ≤ -Real.log (500000000000 / 1687049604473) ∧
    -Real.log (500000000000 / 1687049604473) ≤ (1216128389 / 1000000000) := by
  have h := checkLog_sound (w := (687049604473 / 2687049604473)) (n := 12)
    (lo := (522981207 / 1000000000)) (hi := (65372651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1687049604473 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1687049604473 / 1000000000000) = 1/(500000000000 / 1687049604473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1216128387 / 1000000000) (1216128389 / 1000000000) (Real.log (1687049604473 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1687049604473 / 500000000000) = -Real.log (500000000000 / 1687049604473) := by
    rw [show ((1687049604473 / 500000000000) : ℝ) = ((500000000000 / 1687049604473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (885709639 / 1000000000) ≤ -Real.log (500000000000 / 1212352224003) ∧
    -Real.log (500000000000 / 1212352224003) ≤ (885709641 / 1000000000) := by
  have h := checkLog_sound (w := (212352224003 / 2212352224003)) (n := 12)
    (lo := (192562459 / 1000000000)) (hi := (9628123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212352224003 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1212352224003 / 1000000000000) = 1/(500000000000 / 1212352224003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (885709639 / 1000000000) (885709641 / 1000000000) (Real.log (1212352224003 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1212352224003 / 500000000000) = -Real.log (500000000000 / 1212352224003) := by
    rw [show ((1212352224003 / 500000000000) : ℝ) = ((500000000000 / 1212352224003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (222439827 / 250000000) ≤ -Real.log (50000000000 / 121727180463) ∧
    -Real.log (50000000000 / 121727180463) ≤ (88975931 / 100000000) := by
  have h := checkLog_sound (w := (21727180463 / 221727180463)) (n := 12)
    (lo := (6144129 / 31250000)) (hi := (196612129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121727180463 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(121727180463 / 100000000000) = 1/(50000000000 / 121727180463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (222439827 / 250000000) (88975931 / 100000000) (Real.log (121727180463 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (121727180463 / 50000000000) = -Real.log (50000000000 / 121727180463) := by
    rw [show ((121727180463 / 50000000000) : ℝ) = ((50000000000 / 121727180463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0120

end


