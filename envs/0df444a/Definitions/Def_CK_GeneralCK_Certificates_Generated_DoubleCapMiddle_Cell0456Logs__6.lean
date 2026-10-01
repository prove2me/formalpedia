-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0456Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0456Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:19:50.813865+00:00
-- url     : https://prove2.me/theorems/a4ead934-a166-41fc-acd9-3927972c3a34
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0456Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0457Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0456Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0457Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0458Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0459Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0460Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0461Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0456Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0457Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0458Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0459Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0460Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0461Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0456Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0457Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0458Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0459Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0460Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0461Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0456Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0457Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0458Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0459Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0460Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0461Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0456Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0456
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

theorem reflection_log_1_neg : (9335323 / 50000000) ≤ -Real.log (5120 / 6171) ∧
    -Real.log (5120 / 6171) ≤ (186706461 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 11291)) (n := 12)
    (lo := (9335323 / 50000000)) (hi := (186706461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6171 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6171 / 5120) = 1/(5120 / 6171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (9335323 / 50000000) (186706461 / 1000000000) (Real.log (6171 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6171 / 5120) = -Real.log (5120 / 6171) := by
    rw [show ((6171 / 5120) : ℝ) = ((5120 / 6171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (22975717 / 100000000) ≤ -Real.log (4069 / 5120) ∧
    -Real.log (4069 / 5120) ≤ (229757171 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 9189)) (n := 12)
    (lo := (22975717 / 100000000)) (hi := (229757171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4069) = 1/(4069 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-229757171 / 1000000000) (-22975717 / 100000000) (Real.log (4069 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (93231679 / 500000000) ≤ -Real.log (10240 / 12339) ∧
    -Real.log (10240 / 12339) ≤ (186463359 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 22579)) (n := 12)
    (lo := (93231679 / 500000000)) (hi := (186463359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12339 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12339 / 10240) = 1/(10240 / 12339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (93231679 / 500000000) (186463359 / 1000000000) (Real.log (12339 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12339 / 10240) = -Real.log (10240 / 12339) := by
    rw [show ((12339 / 10240) : ℝ) = ((10240 / 12339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (229388597 / 1000000000) ≤ -Real.log (8141 / 10240) ∧
    -Real.log (8141 / 10240) ≤ (114694299 / 500000000) := by
  have h := checkLog_sound (w := (2099 / 18381)) (n := 12)
    (lo := (229388597 / 1000000000)) (hi := (114694299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8141) = 1/(8141 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-114694299 / 500000000) (-229388597 / 1000000000) (Real.log (8141 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (343977483 / 1000000000) ≤ -Real.log (2560 / 3611) ∧
    -Real.log (2560 / 3611) ≤ (85994371 / 250000000) := by
  have h := checkLog_sound (w := (1051 / 6171)) (n := 12)
    (lo := (343977483 / 1000000000)) (hi := (85994371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3611 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3611 / 2560) = 1/(2560 / 3611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (343977483 / 1000000000) (85994371 / 250000000) (Real.log (3611 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3611 / 2560) = -Real.log (2560 / 3611) := by
    rw [show ((3611 / 2560) : ℝ) = ((2560 / 3611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (264280039 / 500000000) ≤ -Real.log (1509 / 2560) ∧
    -Real.log (1509 / 2560) ≤ (528560079 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 4069)) (n := 12)
    (lo := (264280039 / 500000000)) (hi := (528560079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1509) = 1/(1509 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-528560079 / 1000000000) (-264280039 / 500000000) (Real.log (1509 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (171781 / 500000) ≤ -Real.log (5120 / 7219) ∧
    -Real.log (5120 / 7219) ≤ (343562001 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 12339)) (n := 12)
    (lo := (171781 / 500000)) (hi := (343562001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7219 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7219 / 5120) = 1/(5120 / 7219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (171781 / 500000) (343562001 / 1000000000) (Real.log (7219 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7219 / 5120) = -Real.log (5120 / 7219) := by
    rw [show ((7219 / 5120) : ℝ) = ((5120 / 7219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (65945817 / 125000000) ≤ -Real.log (3021 / 5120) ∧
    -Real.log (3021 / 5120) ≤ (527566537 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 8141)) (n := 12)
    (lo := (65945817 / 125000000)) (hi := (527566537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3021) = 1/(3021 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-527566537 / 1000000000) (-65945817 / 125000000) (Real.log (3021 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (256246357 / 1000000000) ≤ -Real.log (1000000 / 1292071) ∧
    -Real.log (1000000 / 1292071) ≤ (128123179 / 500000000) := by
  have h := checkLog_sound (w := (292071 / 2292071)) (n := 12)
    (lo := (256246357 / 1000000000)) (hi := (128123179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292071 / 1000000) = 1/(1000000 / 1292071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (256246357 / 1000000000) (128123179 / 500000000) (Real.log (1292071 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1292071 / 1000000) = -Real.log (1000000 / 1292071) := by
    rw [show ((1292071 / 1000000) : ℝ) = ((1000000 / 1292071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21588217 / 62500000) ≤ -Real.log (707929 / 1000000) ∧
    -Real.log (707929 / 1000000) ≤ (345411473 / 1000000000) := by
  have h := checkLog_sound (w := (292071 / 1707929)) (n := 12)
    (lo := (21588217 / 62500000)) (hi := (345411473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707929) = 1/(707929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-345411473 / 1000000000) (-21588217 / 62500000) (Real.log (707929 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1002247 / 3906250) ≤ -Real.log (62500 / 80781) ∧
    -Real.log (62500 / 80781) ≤ (256575233 / 1000000000) := by
  have h := checkLog_sound (w := (18281 / 143281)) (n := 12)
    (lo := (1002247 / 3906250)) (hi := (256575233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80781 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80781 / 62500) = 1/(62500 / 80781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1002247 / 3906250) (256575233 / 1000000000) (Real.log (80781 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (80781 / 62500) = -Real.log (62500 / 80781) := by
    rw [show ((80781 / 62500) : ℝ) = ((62500 / 80781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (69202399 / 200000000) ≤ -Real.log (44219 / 62500) ∧
    -Real.log (44219 / 62500) ≤ (86502999 / 250000000) := by
  have h := checkLog_sound (w := (18281 / 106719)) (n := 12)
    (lo := (69202399 / 200000000)) (hi := (86502999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44219) = 1/(44219 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86502999 / 250000000) (-69202399 / 200000000) (Real.log (44219 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9593871 / 50000000) ≤ -Real.log (500000 / 605761) ∧
    -Real.log (500000 / 605761) ≤ (191877421 / 1000000000) := by
  have h := checkLog_sound (w := (105761 / 1105761)) (n := 12)
    (lo := (9593871 / 50000000)) (hi := (191877421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605761 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605761 / 500000) = 1/(500000 / 605761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9593871 / 50000000) (191877421 / 1000000000) (Real.log (605761 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (605761 / 500000) = -Real.log (500000 / 605761) := by
    rw [show ((605761 / 500000) : ℝ) = ((500000 / 605761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (118825387 / 500000000) ≤ -Real.log (394239 / 500000) ∧
    -Real.log (394239 / 500000) ≤ (9506031 / 40000000) := by
  have h := checkLog_sound (w := (105761 / 894239)) (n := 12)
    (lo := (118825387 / 500000000)) (hi := (9506031 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394239) = 1/(394239 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-9506031 / 40000000) (-118825387 / 500000000) (Real.log (394239 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (192143991 / 1000000000) ≤ -Real.log (200000 / 242369) ∧
    -Real.log (200000 / 242369) ≤ (24017999 / 125000000) := by
  have h := checkLog_sound (w := (42369 / 442369)) (n := 12)
    (lo := (192143991 / 1000000000)) (hi := (24017999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242369 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242369 / 200000) = 1/(200000 / 242369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192143991 / 1000000000) (24017999 / 125000000) (Real.log (242369 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (242369 / 200000) = -Real.log (200000 / 242369) := by
    rw [show ((242369 / 200000) : ℝ) = ((200000 / 242369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (238060507 / 1000000000) ≤ -Real.log (157631 / 200000) ∧
    -Real.log (157631 / 200000) ≤ (59515127 / 250000000) := by
  have h := checkLog_sound (w := (42369 / 357631)) (n := 12)
    (lo := (238060507 / 1000000000)) (hi := (59515127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157631) = 1/(157631 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-59515127 / 250000000) (-238060507 / 1000000000) (Real.log (157631 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (60165783 / 100000000) ≤ -Real.log (100000000000 / 182514206933) ∧
    -Real.log (100000000000 / 182514206933) ≤ (601657831 / 1000000000) := by
  have h := checkLog_sound (w := (82514206933 / 282514206933)) (n := 12)
    (lo := (60165783 / 100000000)) (hi := (601657831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182514206933 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182514206933 / 100000000000) = 1/(100000000000 / 182514206933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (60165783 / 100000000) (601657831 / 1000000000) (Real.log (182514206933 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (182514206933 / 100000000000) = -Real.log (100000000000 / 182514206933) := by
    rw [show ((182514206933 / 100000000000) : ℝ) = ((100000000000 / 182514206933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (150646807 / 250000000) ≤ -Real.log (500000000000 / 913419570773) ∧
    -Real.log (500000000000 / 913419570773) ≤ (602587229 / 1000000000) := by
  have h := checkLog_sound (w := (413419570773 / 1413419570773)) (n := 12)
    (lo := (150646807 / 250000000)) (hi := (602587229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913419570773 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(913419570773 / 500000000000) = 1/(500000000000 / 913419570773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (150646807 / 250000000) (602587229 / 1000000000) (Real.log (913419570773 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (913419570773 / 500000000000) = -Real.log (500000000000 / 913419570773) := by
    rw [show ((913419570773 / 500000000000) : ℝ) = ((500000000000 / 913419570773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (214764097 / 500000000) ≤ -Real.log (500000000000 / 768266204003) ∧
    -Real.log (500000000000 / 768266204003) ≤ (85905639 / 200000000) := by
  have h := checkLog_sound (w := (268266204003 / 1268266204003)) (n := 12)
    (lo := (214764097 / 500000000)) (hi := (85905639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768266204003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768266204003 / 500000000000) = 1/(500000000000 / 768266204003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (214764097 / 500000000) (85905639 / 200000000) (Real.log (768266204003 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (768266204003 / 500000000000) = -Real.log (500000000000 / 768266204003) := by
    rw [show ((768266204003 / 500000000000) : ℝ) = ((500000000000 / 768266204003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (430204499 / 1000000000) ≤ -Real.log (500000000000 / 768785962153) ∧
    -Real.log (500000000000 / 768785962153) ≤ (860409 / 2000000) := by
  have h := checkLog_sound (w := (268785962153 / 1268785962153)) (n := 12)
    (lo := (430204499 / 1000000000)) (hi := (860409 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768785962153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768785962153 / 500000000000) = 1/(500000000000 / 768785962153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (430204499 / 1000000000) (860409 / 2000000) (Real.log (768785962153 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (768785962153 / 500000000000) = -Real.log (500000000000 / 768785962153) := by
    rw [show ((768785962153 / 500000000000) : ℝ) = ((500000000000 / 768785962153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0456

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0457Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0457
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

theorem reflection_log_1_neg : (93231679 / 500000000) ≤ -Real.log (10240 / 12339) ∧
    -Real.log (10240 / 12339) ≤ (186463359 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 22579)) (n := 12)
    (lo := (93231679 / 500000000)) (hi := (186463359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12339 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12339 / 10240) = 1/(10240 / 12339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (93231679 / 500000000) (186463359 / 1000000000) (Real.log (12339 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12339 / 10240) = -Real.log (10240 / 12339) := by
    rw [show ((12339 / 10240) : ℝ) = ((10240 / 12339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (229388597 / 1000000000) ≤ -Real.log (8141 / 10240) ∧
    -Real.log (8141 / 10240) ≤ (114694299 / 500000000) := by
  have h := checkLog_sound (w := (2099 / 18381)) (n := 12)
    (lo := (229388597 / 1000000000)) (hi := (114694299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8141) = 1/(8141 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-114694299 / 500000000) (-229388597 / 1000000000) (Real.log (8141 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (186220197 / 1000000000) ≤ -Real.log (640 / 771) ∧
    -Real.log (640 / 771) ≤ (93110099 / 500000000) := by
  have h := checkLog_sound (w := (131 / 1411)) (n := 12)
    (lo := (186220197 / 1000000000)) (hi := (93110099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771 / 640) = 1/(640 / 771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (186220197 / 1000000000) (93110099 / 500000000) (Real.log (771 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (771 / 640) = -Real.log (640 / 771) := by
    rw [show ((771 / 640) : ℝ) = ((640 / 771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (229020159 / 1000000000) ≤ -Real.log (509 / 640) ∧
    -Real.log (509 / 640) ≤ (89461 / 390625) := by
  have h := checkLog_sound (w := (131 / 1149)) (n := 12)
    (lo := (229020159 / 1000000000)) (hi := (89461 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 509) = 1/(509 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-89461 / 390625) (-229020159 / 1000000000) (Real.log (509 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (171781 / 500000) ≤ -Real.log (5120 / 7219) ∧
    -Real.log (5120 / 7219) ≤ (343562001 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 12339)) (n := 12)
    (lo := (171781 / 500000)) (hi := (343562001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7219 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7219 / 5120) = 1/(5120 / 7219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (171781 / 500000) (343562001 / 1000000000) (Real.log (7219 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7219 / 5120) = -Real.log (5120 / 7219) := by
    rw [show ((7219 / 5120) : ℝ) = ((5120 / 7219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (65945817 / 125000000) ≤ -Real.log (3021 / 5120) ∧
    -Real.log (3021 / 5120) ≤ (527566537 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 8141)) (n := 12)
    (lo := (65945817 / 125000000)) (hi := (527566537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3021) = 1/(3021 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-527566537 / 1000000000) (-65945817 / 125000000) (Real.log (3021 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (343146343 / 1000000000) ≤ -Real.log (320 / 451) ∧
    -Real.log (320 / 451) ≤ (42893293 / 125000000) := by
  have h := checkLog_sound (w := (131 / 771)) (n := 12)
    (lo := (343146343 / 1000000000)) (hi := (42893293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((451 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(451 / 320) = 1/(320 / 451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (343146343 / 1000000000) (42893293 / 125000000) (Real.log (451 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (451 / 320) = -Real.log (320 / 451) := by
    rw [show ((451 / 320) : ℝ) = ((320 / 451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (26328699 / 50000000) ≤ -Real.log (189 / 320) ∧
    -Real.log (189 / 320) ≤ (526573981 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 189) = 1/(189 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-526573981 / 1000000000) (-26328699 / 50000000) (Real.log (189 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (63979537 / 250000000) ≤ -Real.log (1000000 / 1291647) ∧
    -Real.log (1000000 / 1291647) ≤ (255918149 / 1000000000) := by
  have h := checkLog_sound (w := (291647 / 2291647)) (n := 12)
    (lo := (63979537 / 250000000)) (hi := (255918149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1291647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1291647 / 1000000) = 1/(1000000 / 1291647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (63979537 / 250000000) (255918149 / 1000000000) (Real.log (1291647 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1291647 / 1000000) = -Real.log (1000000 / 1291647) := by
    rw [show ((1291647 / 1000000) : ℝ) = ((1000000 / 1291647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (344812721 / 1000000000) ≤ -Real.log (708353 / 1000000) ∧
    -Real.log (708353 / 1000000) ≤ (172406361 / 500000000) := by
  have h := checkLog_sound (w := (291647 / 1708353)) (n := 12)
    (lo := (344812721 / 1000000000)) (hi := (172406361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 708353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 708353) = 1/(708353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-172406361 / 500000000) (-344812721 / 1000000000) (Real.log (708353 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256247131 / 1000000000) ≤ -Real.log (125000 / 161509) ∧
    -Real.log (125000 / 161509) ≤ (64061783 / 250000000) := by
  have h := checkLog_sound (w := (36509 / 286509)) (n := 12)
    (lo := (256247131 / 1000000000)) (hi := (64061783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161509 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161509 / 125000) = 1/(125000 / 161509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256247131 / 1000000000) (64061783 / 250000000) (Real.log (161509 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161509 / 125000) = -Real.log (125000 / 161509) := by
    rw [show ((161509 / 125000) : ℝ) = ((125000 / 161509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (69082577 / 200000000) ≤ -Real.log (88491 / 125000) ∧
    -Real.log (88491 / 125000) ≤ (172706443 / 500000000) := by
  have h := checkLog_sound (w := (36509 / 213491)) (n := 12)
    (lo := (69082577 / 200000000)) (hi := (172706443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88491) = 1/(88491 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-172706443 / 500000000) (-69082577 / 200000000) (Real.log (88491 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (191611603 / 1000000000) ≤ -Real.log (625 / 757) ∧
    -Real.log (625 / 757) ≤ (47902901 / 250000000) := by
  have h := checkLog_sound (w := (66 / 691)) (n := 12)
    (lo := (191611603 / 1000000000)) (hi := (47902901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757 / 625) = 1/(625 / 757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (191611603 / 1000000000) (47902901 / 250000000) (Real.log (757 / 625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (757 / 625) = -Real.log (625 / 757) := by
    rw [show ((757 / 625) : ℝ) = ((625 / 757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9489699 / 40000000) ≤ -Real.log (493 / 625) ∧
    -Real.log (493 / 625) ≤ (59310619 / 250000000) := by
  have h := checkLog_sound (w := (66 / 559)) (n := 12)
    (lo := (9489699 / 40000000)) (hi := (59310619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 493) = 1/(493 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-59310619 / 250000000) (-9489699 / 40000000) (Real.log (493 / 625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38375649 / 200000000) ≤ -Real.log (1000000 / 1211523) ∧
    -Real.log (1000000 / 1211523) ≤ (95939123 / 500000000) := by
  have h := checkLog_sound (w := (211523 / 2211523)) (n := 12)
    (lo := (38375649 / 200000000)) (hi := (95939123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211523 / 1000000) = 1/(1000000 / 1211523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38375649 / 200000000) (95939123 / 500000000) (Real.log (1211523 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1211523 / 1000000) = -Real.log (1000000 / 1211523) := by
    rw [show ((1211523 / 1000000) : ℝ) = ((1000000 / 1211523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (118826021 / 500000000) ≤ -Real.log (788477 / 1000000) ∧
    -Real.log (788477 / 1000000) ≤ (237652043 / 1000000000) := by
  have h := checkLog_sound (w := (211523 / 1788477)) (n := 12)
    (lo := (118826021 / 500000000)) (hi := (237652043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788477) = 1/(788477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-237652043 / 1000000000) (-118826021 / 500000000) (Real.log (788477 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (60073087 / 100000000) ≤ -Real.log (250000000000 / 455862754869) ∧
    -Real.log (250000000000 / 455862754869) ≤ (600730871 / 1000000000) := by
  have h := checkLog_sound (w := (205862754869 / 705862754869)) (n := 12)
    (lo := (60073087 / 100000000)) (hi := (600730871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455862754869 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455862754869 / 250000000000) = 1/(250000000000 / 455862754869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (60073087 / 100000000) (600730871 / 1000000000) (Real.log (455862754869 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (455862754869 / 250000000000) = -Real.log (250000000000 / 455862754869) := by
    rw [show ((455862754869 / 250000000000) : ℝ) = ((250000000000 / 455862754869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (37603751 / 62500000) ≤ -Real.log (250000000000 / 456286515013) ∧
    -Real.log (250000000000 / 456286515013) ≤ (601660017 / 1000000000) := by
  have h := checkLog_sound (w := (206286515013 / 706286515013)) (n := 12)
    (lo := (37603751 / 62500000)) (hi := (601660017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((456286515013 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(456286515013 / 250000000000) = 1/(250000000000 / 456286515013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (37603751 / 62500000) (601660017 / 1000000000) (Real.log (456286515013 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (456286515013 / 250000000000) = -Real.log (250000000000 / 456286515013) := by
    rw [show ((456286515013 / 250000000000) : ℝ) = ((250000000000 / 456286515013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (428854079 / 1000000000) ≤ -Real.log (500000000000 / 767748478701) ∧
    -Real.log (500000000000 / 767748478701) ≤ (1340169 / 3125000) := by
  have h := checkLog_sound (w := (267748478701 / 1267748478701)) (n := 12)
    (lo := (428854079 / 1000000000)) (hi := (1340169 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767748478701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767748478701 / 500000000000) = 1/(500000000000 / 767748478701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (428854079 / 1000000000) (1340169 / 3125000) (Real.log (767748478701 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (767748478701 / 500000000000) = -Real.log (500000000000 / 767748478701) := by
    rw [show ((767748478701 / 500000000000) : ℝ) = ((500000000000 / 767748478701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (26845643 / 62500000) ≤ -Real.log (100000000000 / 153653562501) ∧
    -Real.log (100000000000 / 153653562501) ≤ (429530289 / 1000000000) := by
  have h := checkLog_sound (w := (53653562501 / 253653562501)) (n := 12)
    (lo := (26845643 / 62500000)) (hi := (429530289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153653562501 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153653562501 / 100000000000) = 1/(100000000000 / 153653562501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (26845643 / 62500000) (429530289 / 1000000000) (Real.log (153653562501 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (153653562501 / 100000000000) = -Real.log (100000000000 / 153653562501) := by
    rw [show ((153653562501 / 100000000000) : ℝ) = ((100000000000 / 153653562501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0457

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0458Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0458
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

theorem reflection_log_1_neg : (186220197 / 1000000000) ≤ -Real.log (640 / 771) ∧
    -Real.log (640 / 771) ≤ (93110099 / 500000000) := by
  have h := checkLog_sound (w := (131 / 1411)) (n := 12)
    (lo := (186220197 / 1000000000)) (hi := (93110099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771 / 640) = 1/(640 / 771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (186220197 / 1000000000) (93110099 / 500000000) (Real.log (771 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (771 / 640) = -Real.log (640 / 771) := by
    rw [show ((771 / 640) : ℝ) = ((640 / 771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (229020159 / 1000000000) ≤ -Real.log (509 / 640) ∧
    -Real.log (509 / 640) ≤ (89461 / 390625) := by
  have h := checkLog_sound (w := (131 / 1149)) (n := 12)
    (lo := (229020159 / 1000000000)) (hi := (89461 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 509) = 1/(509 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-89461 / 390625) (-229020159 / 1000000000) (Real.log (509 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11623561 / 62500000) ≤ -Real.log (10240 / 12333) ∧
    -Real.log (10240 / 12333) ≤ (185976977 / 1000000000) := by
  have h := checkLog_sound (w := (2093 / 22573)) (n := 12)
    (lo := (11623561 / 62500000)) (hi := (185976977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12333 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12333 / 10240) = 1/(10240 / 12333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11623561 / 62500000) (185976977 / 1000000000) (Real.log (12333 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12333 / 10240) = -Real.log (10240 / 12333) := by
    rw [show ((12333 / 10240) : ℝ) = ((10240 / 12333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (114325929 / 500000000) ≤ -Real.log (8147 / 10240) ∧
    -Real.log (8147 / 10240) ≤ (228651859 / 1000000000) := by
  have h := checkLog_sound (w := (2093 / 18387)) (n := 12)
    (lo := (114325929 / 500000000)) (hi := (228651859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8147) = 1/(8147 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-228651859 / 1000000000) (-114325929 / 500000000) (Real.log (8147 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (343146343 / 1000000000) ≤ -Real.log (320 / 451) ∧
    -Real.log (320 / 451) ≤ (42893293 / 125000000) := by
  have h := checkLog_sound (w := (131 / 771)) (n := 12)
    (lo := (343146343 / 1000000000)) (hi := (42893293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((451 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(451 / 320) = 1/(320 / 451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (343146343 / 1000000000) (42893293 / 125000000) (Real.log (451 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (451 / 320) = -Real.log (320 / 451) := by
    rw [show ((451 / 320) : ℝ) = ((320 / 451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (26328699 / 50000000) ≤ -Real.log (189 / 320) ∧
    -Real.log (189 / 320) ≤ (526573981 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 189) = 1/(189 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-526573981 / 1000000000) (-26328699 / 50000000) (Real.log (189 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (171365257 / 500000000) ≤ -Real.log (5120 / 7213) ∧
    -Real.log (5120 / 7213) ≤ (68546103 / 200000000) := by
  have h := checkLog_sound (w := (2093 / 12333)) (n := 12)
    (lo := (171365257 / 500000000)) (hi := (68546103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7213 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7213 / 5120) = 1/(5120 / 7213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (171365257 / 500000000) (68546103 / 200000000) (Real.log (7213 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7213 / 5120) = -Real.log (5120 / 7213) := by
    rw [show ((7213 / 5120) : ℝ) = ((5120 / 7213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (525582409 / 1000000000) ≤ -Real.log (3027 / 5120) ∧
    -Real.log (3027 / 5120) ≤ (52558241 / 100000000) := by
  have h := checkLog_sound (w := (2093 / 8147)) (n := 12)
    (lo := (525582409 / 1000000000)) (hi := (52558241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3027) = 1/(3027 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-52558241 / 100000000) (-525582409 / 1000000000) (Real.log (3027 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (255589831 / 1000000000) ≤ -Real.log (1000000 / 1291223) ∧
    -Real.log (1000000 / 1291223) ≤ (31948729 / 125000000) := by
  have h := checkLog_sound (w := (291223 / 2291223)) (n := 12)
    (lo := (255589831 / 1000000000)) (hi := (31948729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1291223 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1291223 / 1000000) = 1/(1000000 / 1291223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (255589831 / 1000000000) (31948729 / 125000000) (Real.log (1291223 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1291223 / 1000000) = -Real.log (1000000 / 1291223) := by
    rw [show ((1291223 / 1000000) : ℝ) = ((1000000 / 1291223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (344214329 / 1000000000) ≤ -Real.log (708777 / 1000000) ∧
    -Real.log (708777 / 1000000) ≤ (34421433 / 100000000) := by
  have h := checkLog_sound (w := (291223 / 1708777)) (n := 12)
    (lo := (344214329 / 1000000000)) (hi := (34421433 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 708777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 708777) = 1/(708777 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-34421433 / 100000000) (-344214329 / 1000000000) (Real.log (708777 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (127959461 / 500000000) ≤ -Real.log (15625 / 20182) ∧
    -Real.log (15625 / 20182) ≤ (255918923 / 1000000000) := by
  have h := checkLog_sound (w := (4557 / 35807)) (n := 12)
    (lo := (127959461 / 500000000)) (hi := (255918923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20182 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20182 / 15625) = 1/(15625 / 20182) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (127959461 / 500000000) (255918923 / 1000000000) (Real.log (20182 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (20182 / 15625) = -Real.log (15625 / 20182) := by
    rw [show ((20182 / 15625) : ℝ) = ((15625 / 20182) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (344814133 / 1000000000) ≤ -Real.log (11068 / 15625) ∧
    -Real.log (11068 / 15625) ≤ (172407067 / 500000000) := by
  have h := checkLog_sound (w := (4557 / 26693)) (n := 12)
    (lo := (344814133 / 1000000000)) (hi := (172407067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11068) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11068) = 1/(11068 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-172407067 / 500000000) (-344814133 / 1000000000) (Real.log (11068 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (47836429 / 250000000) ≤ -Real.log (500000 / 605439) ∧
    -Real.log (500000 / 605439) ≤ (191345717 / 1000000000) := by
  have h := checkLog_sound (w := (105439 / 1105439)) (n := 12)
    (lo := (47836429 / 250000000)) (hi := (191345717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605439 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605439 / 500000) = 1/(500000 / 605439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (47836429 / 250000000) (191345717 / 1000000000) (Real.log (605439 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (605439 / 500000) = -Real.log (500000 / 605439) := by
    rw [show ((605439 / 500000) : ℝ) = ((500000 / 605439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (236834343 / 1000000000) ≤ -Real.log (394561 / 500000) ∧
    -Real.log (394561 / 500000) ≤ (29604293 / 125000000) := by
  have h := checkLog_sound (w := (105439 / 894561)) (n := 12)
    (lo := (236834343 / 1000000000)) (hi := (29604293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394561) = 1/(394561 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-29604293 / 125000000) (-236834343 / 1000000000) (Real.log (394561 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (191612429 / 1000000000) ≤ -Real.log (1000000 / 1211201) ∧
    -Real.log (1000000 / 1211201) ≤ (19161243 / 100000000) := by
  have h := checkLog_sound (w := (211201 / 2211201)) (n := 12)
    (lo := (191612429 / 1000000000)) (hi := (19161243 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211201 / 1000000) = 1/(1000000 / 1211201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (191612429 / 1000000000) (19161243 / 100000000) (Real.log (1211201 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1211201 / 1000000) = -Real.log (1000000 / 1211201) := by
    rw [show ((1211201 / 1000000) : ℝ) = ((1000000 / 1211201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (237243743 / 1000000000) ≤ -Real.log (788799 / 1000000) ∧
    -Real.log (788799 / 1000000) ≤ (7413867 / 31250000) := by
  have h := checkLog_sound (w := (211201 / 1788799)) (n := 12)
    (lo := (237243743 / 1000000000)) (hi := (7413867 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788799) = 1/(788799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-7413867 / 31250000) (-237243743 / 1000000000) (Real.log (788799 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (468597 / 781250) ≤ -Real.log (25000000000 / 45544049821) ∧
    -Real.log (25000000000 / 45544049821) ≤ (599804161 / 1000000000) := by
  have h := checkLog_sound (w := (20544049821 / 70544049821)) (n := 12)
    (lo := (468597 / 781250)) (hi := (599804161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45544049821 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45544049821 / 25000000000) = 1/(25000000000 / 45544049821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (468597 / 781250) (599804161 / 1000000000) (Real.log (45544049821 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45544049821 / 25000000000) = -Real.log (25000000000 / 45544049821) := by
    rw [show ((45544049821 / 25000000000) : ℝ) = ((25000000000 / 45544049821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4693227 / 7812500) ≤ -Real.log (500000000000 / 911727502711) ∧
    -Real.log (500000000000 / 911727502711) ≤ (600733057 / 1000000000) := by
  have h := checkLog_sound (w := (411727502711 / 1411727502711)) (n := 12)
    (lo := (4693227 / 7812500)) (hi := (600733057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911727502711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911727502711 / 500000000000) = 1/(500000000000 / 911727502711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4693227 / 7812500) (600733057 / 1000000000) (Real.log (911727502711 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (911727502711 / 500000000000) = -Real.log (500000000000 / 911727502711) := by
    rw [show ((911727502711 / 500000000000) : ℝ) = ((500000000000 / 911727502711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21409003 / 50000000) ≤ -Real.log (250000000000 / 383615587957) ∧
    -Real.log (250000000000 / 383615587957) ≤ (428180061 / 1000000000) := by
  have h := checkLog_sound (w := (133615587957 / 633615587957)) (n := 12)
    (lo := (21409003 / 50000000)) (hi := (428180061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383615587957 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383615587957 / 250000000000) = 1/(250000000000 / 383615587957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (21409003 / 50000000) (428180061 / 1000000000) (Real.log (383615587957 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (383615587957 / 250000000000) = -Real.log (250000000000 / 383615587957) := by
    rw [show ((383615587957 / 250000000000) : ℝ) = ((250000000000 / 383615587957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (107214043 / 250000000) ≤ -Real.log (500000000000 / 767750085891) ∧
    -Real.log (500000000000 / 767750085891) ≤ (428856173 / 1000000000) := by
  have h := checkLog_sound (w := (267750085891 / 1267750085891)) (n := 12)
    (lo := (107214043 / 250000000)) (hi := (428856173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767750085891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767750085891 / 500000000000) = 1/(500000000000 / 767750085891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (107214043 / 250000000) (428856173 / 1000000000) (Real.log (767750085891 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (767750085891 / 500000000000) = -Real.log (500000000000 / 767750085891) := by
    rw [show ((767750085891 / 500000000000) : ℝ) = ((500000000000 / 767750085891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0458

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0459Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0459
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

theorem reflection_log_1_neg : (11623561 / 62500000) ≤ -Real.log (10240 / 12333) ∧
    -Real.log (10240 / 12333) ≤ (185976977 / 1000000000) := by
  have h := checkLog_sound (w := (2093 / 22573)) (n := 12)
    (lo := (11623561 / 62500000)) (hi := (185976977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12333 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12333 / 10240) = 1/(10240 / 12333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11623561 / 62500000) (185976977 / 1000000000) (Real.log (12333 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12333 / 10240) = -Real.log (10240 / 12333) := by
    rw [show ((12333 / 10240) : ℝ) = ((10240 / 12333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (114325929 / 500000000) ≤ -Real.log (8147 / 10240) ∧
    -Real.log (8147 / 10240) ≤ (228651859 / 1000000000) := by
  have h := checkLog_sound (w := (2093 / 18387)) (n := 12)
    (lo := (114325929 / 500000000)) (hi := (228651859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8147) = 1/(8147 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-228651859 / 1000000000) (-114325929 / 500000000) (Real.log (8147 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (185733697 / 1000000000) ≤ -Real.log (1024 / 1233) ∧
    -Real.log (1024 / 1233) ≤ (92866849 / 500000000) := by
  have h := checkLog_sound (w := (209 / 2257)) (n := 12)
    (lo := (185733697 / 1000000000)) (hi := (92866849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 1024) = 1/(1024 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (185733697 / 1000000000) (92866849 / 500000000) (Real.log (1233 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1233 / 1024) = -Real.log (1024 / 1233) := by
    rw [show ((1233 / 1024) : ℝ) = ((1024 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57070923 / 250000000) ≤ -Real.log (815 / 1024) ∧
    -Real.log (815 / 1024) ≤ (228283693 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1839)) (n := 12)
    (lo := (57070923 / 250000000)) (hi := (228283693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 815) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 815) = 1/(815 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-228283693 / 1000000000) (-57070923 / 250000000) (Real.log (815 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (171365257 / 500000000) ≤ -Real.log (5120 / 7213) ∧
    -Real.log (5120 / 7213) ≤ (68546103 / 200000000) := by
  have h := checkLog_sound (w := (2093 / 12333)) (n := 12)
    (lo := (171365257 / 500000000)) (hi := (68546103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7213 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7213 / 5120) = 1/(5120 / 7213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (171365257 / 500000000) (68546103 / 200000000) (Real.log (7213 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7213 / 5120) = -Real.log (5120 / 7213) := by
    rw [show ((7213 / 5120) : ℝ) = ((5120 / 7213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (525582409 / 1000000000) ≤ -Real.log (3027 / 5120) ∧
    -Real.log (3027 / 5120) ≤ (52558241 / 100000000) := by
  have h := checkLog_sound (w := (2093 / 8147)) (n := 12)
    (lo := (525582409 / 1000000000)) (hi := (52558241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3027) = 1/(3027 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-52558241 / 100000000) (-525582409 / 1000000000) (Real.log (3027 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (21394657 / 62500000) ≤ -Real.log (512 / 721) ∧
    -Real.log (512 / 721) ≤ (342314513 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1233)) (n := 12)
    (lo := (21394657 / 62500000)) (hi := (342314513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721 / 512) = 1/(512 / 721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (21394657 / 62500000) (342314513 / 1000000000) (Real.log (721 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (721 / 512) = -Real.log (512 / 721) := by
    rw [show ((721 / 512) : ℝ) = ((512 / 721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (524591819 / 1000000000) ≤ -Real.log (303 / 512) ∧
    -Real.log (303 / 512) ≤ (26229591 / 50000000) := by
  have h := checkLog_sound (w := (209 / 815)) (n := 12)
    (lo := (524591819 / 1000000000)) (hi := (26229591 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 303) = 1/(303 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26229591 / 50000000) (-524591819 / 1000000000) (Real.log (303 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (127630703 / 500000000) ≤ -Real.log (1000000 / 1290799) ∧
    -Real.log (1000000 / 1290799) ≤ (255261407 / 1000000000) := by
  have h := checkLog_sound (w := (290799 / 2290799)) (n := 12)
    (lo := (127630703 / 500000000)) (hi := (255261407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290799 / 1000000) = 1/(1000000 / 1290799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (127630703 / 500000000) (255261407 / 1000000000) (Real.log (1290799 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1290799 / 1000000) = -Real.log (1000000 / 1290799) := by
    rw [show ((1290799 / 1000000) : ℝ) = ((1000000 / 1290799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (171808147 / 500000000) ≤ -Real.log (709201 / 1000000) ∧
    -Real.log (709201 / 1000000) ≤ (68723259 / 200000000) := by
  have h := checkLog_sound (w := (290799 / 1709201)) (n := 12)
    (lo := (171808147 / 500000000)) (hi := (68723259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709201) = 1/(709201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-68723259 / 200000000) (-171808147 / 500000000) (Real.log (709201 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51118121 / 200000000) ≤ -Real.log (125000 / 161403) ∧
    -Real.log (125000 / 161403) ≤ (127795303 / 500000000) := by
  have h := checkLog_sound (w := (36403 / 286403)) (n := 12)
    (lo := (51118121 / 200000000)) (hi := (127795303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161403 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161403 / 125000) = 1/(125000 / 161403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51118121 / 200000000) (127795303 / 500000000) (Real.log (161403 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161403 / 125000) = -Real.log (125000 / 161403) := by
    rw [show ((161403 / 125000) : ℝ) = ((125000 / 161403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (17210787 / 50000000) ≤ -Real.log (88597 / 125000) ∧
    -Real.log (88597 / 125000) ≤ (344215741 / 1000000000) := by
  have h := checkLog_sound (w := (36403 / 213597)) (n := 12)
    (lo := (17210787 / 50000000)) (hi := (344215741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88597) = 1/(88597 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-344215741 / 1000000000) (-17210787 / 50000000) (Real.log (88597 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (95539879 / 500000000) ≤ -Real.log (250000 / 302639) ∧
    -Real.log (250000 / 302639) ≤ (191079759 / 1000000000) := by
  have h := checkLog_sound (w := (52639 / 552639)) (n := 12)
    (lo := (95539879 / 500000000)) (hi := (191079759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302639 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302639 / 250000) = 1/(250000 / 302639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (95539879 / 500000000) (191079759 / 1000000000) (Real.log (302639 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (302639 / 250000) = -Real.log (250000 / 302639) := by
    rw [show ((302639 / 250000) : ℝ) = ((250000 / 302639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (118213189 / 500000000) ≤ -Real.log (197361 / 250000) ∧
    -Real.log (197361 / 250000) ≤ (236426379 / 1000000000) := by
  have h := checkLog_sound (w := (52639 / 447361)) (n := 12)
    (lo := (118213189 / 500000000)) (hi := (236426379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197361) = 1/(197361 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-236426379 / 1000000000) (-118213189 / 500000000) (Real.log (197361 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (95673271 / 500000000) ≤ -Real.log (1000000 / 1210879) ∧
    -Real.log (1000000 / 1210879) ≤ (191346543 / 1000000000) := by
  have h := checkLog_sound (w := (210879 / 2210879)) (n := 12)
    (lo := (95673271 / 500000000)) (hi := (191346543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210879 / 1000000) = 1/(1000000 / 1210879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95673271 / 500000000) (191346543 / 1000000000) (Real.log (1210879 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1210879 / 1000000) = -Real.log (1000000 / 1210879) := by
    rw [show ((1210879 / 1000000) : ℝ) = ((1000000 / 1210879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (236835611 / 1000000000) ≤ -Real.log (789121 / 1000000) ∧
    -Real.log (789121 / 1000000) ≤ (59208903 / 250000000) := by
  have h := checkLog_sound (w := (210879 / 1789121)) (n := 12)
    (lo := (236835611 / 1000000000)) (hi := (59208903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789121) = 1/(789121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-59208903 / 250000000) (-236835611 / 1000000000) (Real.log (789121 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (598877701 / 1000000000) ≤ -Real.log (15625000000 / 28438671653) ∧
    -Real.log (15625000000 / 28438671653) ≤ (299438851 / 500000000) := by
  have h := checkLog_sound (w := (12813671653 / 44063671653)) (n := 12)
    (lo := (598877701 / 1000000000)) (hi := (299438851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28438671653 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28438671653 / 15625000000) = 1/(15625000000 / 28438671653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (598877701 / 1000000000) (299438851 / 500000000) (Real.log (28438671653 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28438671653 / 15625000000) = -Real.log (15625000000 / 28438671653) := by
    rw [show ((28438671653 / 15625000000) : ℝ) = ((15625000000 / 28438671653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (299903173 / 500000000) ≤ -Real.log (500000000000 / 910882987009) ∧
    -Real.log (500000000000 / 910882987009) ≤ (599806347 / 1000000000) := by
  have h := checkLog_sound (w := (410882987009 / 1410882987009)) (n := 12)
    (lo := (299903173 / 500000000)) (hi := (599806347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((910882987009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(910882987009 / 500000000000) = 1/(500000000000 / 910882987009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (299903173 / 500000000) (599806347 / 1000000000) (Real.log (910882987009 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (910882987009 / 500000000000) = -Real.log (500000000000 / 910882987009) := by
    rw [show ((910882987009 / 500000000000) : ℝ) = ((500000000000 / 910882987009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (53438267 / 125000000) ≤ -Real.log (125000000000 / 191678573781) ∧
    -Real.log (125000000000 / 191678573781) ≤ (427506137 / 1000000000) := by
  have h := checkLog_sound (w := (66678573781 / 316678573781)) (n := 12)
    (lo := (53438267 / 125000000)) (hi := (427506137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191678573781 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191678573781 / 125000000000) = 1/(125000000000 / 191678573781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (53438267 / 125000000) (427506137 / 1000000000) (Real.log (191678573781 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (191678573781 / 125000000000) = -Real.log (125000000000 / 191678573781) := by
    rw [show ((191678573781 / 125000000000) : ℝ) = ((125000000000 / 191678573781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (428182153 / 1000000000) ≤ -Real.log (15625000000 / 23976024431) ∧
    -Real.log (15625000000 / 23976024431) ≤ (214091077 / 500000000) := by
  have h := checkLog_sound (w := (8351024431 / 39601024431)) (n := 12)
    (lo := (428182153 / 1000000000)) (hi := (214091077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23976024431 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23976024431 / 15625000000) = 1/(15625000000 / 23976024431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (428182153 / 1000000000) (214091077 / 500000000) (Real.log (23976024431 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23976024431 / 15625000000) = -Real.log (15625000000 / 23976024431) := by
    rw [show ((23976024431 / 15625000000) : ℝ) = ((15625000000 / 23976024431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0459

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0460Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0460
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

theorem reflection_log_1_neg : (185733697 / 1000000000) ≤ -Real.log (1024 / 1233) ∧
    -Real.log (1024 / 1233) ≤ (92866849 / 500000000) := by
  have h := checkLog_sound (w := (209 / 2257)) (n := 12)
    (lo := (185733697 / 1000000000)) (hi := (92866849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 1024) = 1/(1024 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (185733697 / 1000000000) (92866849 / 500000000) (Real.log (1233 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1233 / 1024) = -Real.log (1024 / 1233) := by
    rw [show ((1233 / 1024) : ℝ) = ((1024 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57070923 / 250000000) ≤ -Real.log (815 / 1024) ∧
    -Real.log (815 / 1024) ≤ (228283693 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1839)) (n := 12)
    (lo := (57070923 / 250000000)) (hi := (228283693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 815) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 815) = 1/(815 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-228283693 / 1000000000) (-57070923 / 250000000) (Real.log (815 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (92745179 / 500000000) ≤ -Real.log (10240 / 12327) ∧
    -Real.log (10240 / 12327) ≤ (185490359 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 22567)) (n := 12)
    (lo := (92745179 / 500000000)) (hi := (185490359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12327 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12327 / 10240) = 1/(10240 / 12327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (92745179 / 500000000) (185490359 / 1000000000) (Real.log (12327 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12327 / 10240) = -Real.log (10240 / 12327) := by
    rw [show ((12327 / 10240) : ℝ) = ((10240 / 12327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (227915661 / 1000000000) ≤ -Real.log (8153 / 10240) ∧
    -Real.log (8153 / 10240) ≤ (113957831 / 500000000) := by
  have h := checkLog_sound (w := (2087 / 18393)) (n := 12)
    (lo := (227915661 / 1000000000)) (hi := (113957831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8153) = 1/(8153 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-113957831 / 500000000) (-227915661 / 1000000000) (Real.log (8153 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21394657 / 62500000) ≤ -Real.log (512 / 721) ∧
    -Real.log (512 / 721) ≤ (342314513 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1233)) (n := 12)
    (lo := (21394657 / 62500000)) (hi := (342314513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721 / 512) = 1/(512 / 721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21394657 / 62500000) (342314513 / 1000000000) (Real.log (721 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (721 / 512) = -Real.log (512 / 721) := by
    rw [show ((721 / 512) : ℝ) = ((512 / 721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (524591819 / 1000000000) ≤ -Real.log (303 / 512) ∧
    -Real.log (303 / 512) ≤ (26229591 / 50000000) := by
  have h := checkLog_sound (w := (209 / 815)) (n := 12)
    (lo := (524591819 / 1000000000)) (hi := (26229591 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 303) = 1/(303 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26229591 / 50000000) (-524591819 / 1000000000) (Real.log (303 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10684323 / 31250000) ≤ -Real.log (5120 / 7207) ∧
    -Real.log (5120 / 7207) ≤ (341898337 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 12327)) (n := 12)
    (lo := (10684323 / 31250000)) (hi := (341898337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7207 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7207 / 5120) = 1/(5120 / 7207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10684323 / 31250000) (341898337 / 1000000000) (Real.log (7207 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7207 / 5120) = -Real.log (5120 / 7207) := by
    rw [show ((7207 / 5120) : ℝ) = ((5120 / 7207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (52360221 / 100000000) ≤ -Real.log (3033 / 5120) ∧
    -Real.log (3033 / 5120) ≤ (523602211 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 8153)) (n := 12)
    (lo := (52360221 / 100000000)) (hi := (523602211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3033) = 1/(3033 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-523602211 / 1000000000) (-52360221 / 100000000) (Real.log (3033 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (254932873 / 1000000000) ≤ -Real.log (8000 / 10323) ∧
    -Real.log (8000 / 10323) ≤ (127466437 / 500000000) := by
  have h := checkLog_sound (w := (2323 / 18323)) (n := 12)
    (lo := (254932873 / 1000000000)) (hi := (127466437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10323 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10323 / 8000) = 1/(8000 / 10323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (254932873 / 1000000000) (127466437 / 500000000) (Real.log (10323 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (10323 / 8000) = -Real.log (8000 / 10323) := by
    rw [show ((10323 / 8000) : ℝ) = ((8000 / 10323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (343018617 / 1000000000) ≤ -Real.log (5677 / 8000) ∧
    -Real.log (5677 / 8000) ≤ (171509309 / 500000000) := by
  have h := checkLog_sound (w := (2323 / 13677)) (n := 12)
    (lo := (343018617 / 1000000000)) (hi := (171509309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5677) = 1/(5677 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-171509309 / 500000000) (-343018617 / 1000000000) (Real.log (5677 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (255262181 / 1000000000) ≤ -Real.log (2500 / 3227) ∧
    -Real.log (2500 / 3227) ≤ (127631091 / 500000000) := by
  have h := checkLog_sound (w := (727 / 5727)) (n := 12)
    (lo := (255262181 / 1000000000)) (hi := (127631091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3227 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3227 / 2500) = 1/(2500 / 3227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (255262181 / 1000000000) (127631091 / 500000000) (Real.log (3227 / 2500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3227 / 2500) = -Real.log (2500 / 3227) := by
    rw [show ((3227 / 2500) : ℝ) = ((2500 / 3227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (42952213 / 125000000) ≤ -Real.log (1773 / 2500) ∧
    -Real.log (1773 / 2500) ≤ (68723541 / 200000000) := by
  have h := checkLog_sound (w := (727 / 4273)) (n := 12)
    (lo := (42952213 / 125000000)) (hi := (68723541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1773) = 1/(1773 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-68723541 / 200000000) (-42952213 / 125000000) (Real.log (1773 / 2500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190813729 / 1000000000) ≤ -Real.log (500000 / 605117) ∧
    -Real.log (500000 / 605117) ≤ (19081373 / 100000000) := by
  have h := checkLog_sound (w := (105117 / 1105117)) (n := 12)
    (lo := (190813729 / 1000000000)) (hi := (19081373 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605117 / 500000) = 1/(500000 / 605117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190813729 / 1000000000) (19081373 / 100000000) (Real.log (605117 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (605117 / 500000) = -Real.log (500000 / 605117) := by
    rw [show ((605117 / 500000) : ℝ) = ((500000 / 605117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (236018579 / 1000000000) ≤ -Real.log (394883 / 500000) ∧
    -Real.log (394883 / 500000) ≤ (11800929 / 50000000) := by
  have h := checkLog_sound (w := (105117 / 894883)) (n := 12)
    (lo := (236018579 / 1000000000)) (hi := (11800929 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394883) = 1/(394883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-11800929 / 50000000) (-236018579 / 1000000000) (Real.log (394883 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (23885073 / 125000000) ≤ -Real.log (1000000 / 1210557) ∧
    -Real.log (1000000 / 1210557) ≤ (38216117 / 200000000) := by
  have h := checkLog_sound (w := (210557 / 2210557)) (n := 12)
    (lo := (23885073 / 125000000)) (hi := (38216117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210557 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210557 / 1000000) = 1/(1000000 / 1210557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (23885073 / 125000000) (38216117 / 200000000) (Real.log (1210557 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1210557 / 1000000) = -Real.log (1000000 / 1210557) := by
    rw [show ((1210557 / 1000000) : ℝ) = ((1000000 / 1210557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (47285529 / 200000000) ≤ -Real.log (789443 / 1000000) ∧
    -Real.log (789443 / 1000000) ≤ (118213823 / 500000000) := by
  have h := checkLog_sound (w := (210557 / 1789443)) (n := 12)
    (lo := (47285529 / 200000000)) (hi := (118213823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789443) = 1/(789443 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-118213823 / 500000000) (-47285529 / 200000000) (Real.log (789443 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (597951491 / 1000000000) ≤ -Real.log (500000000000 / 909194997357) ∧
    -Real.log (500000000000 / 909194997357) ≤ (149487873 / 250000000) := by
  have h := checkLog_sound (w := (409194997357 / 1409194997357)) (n := 12)
    (lo := (597951491 / 1000000000)) (hi := (149487873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909194997357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909194997357 / 500000000000) = 1/(500000000000 / 909194997357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (597951491 / 1000000000) (149487873 / 250000000) (Real.log (909194997357 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (909194997357 / 500000000000) = -Real.log (500000000000 / 909194997357) := by
    rw [show ((909194997357 / 500000000000) : ℝ) = ((500000000000 / 909194997357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (119775977 / 200000000) ≤ -Real.log (250000000000 / 455019740553) ∧
    -Real.log (250000000000 / 455019740553) ≤ (299439943 / 500000000) := by
  have h := checkLog_sound (w := (205019740553 / 705019740553)) (n := 12)
    (lo := (119775977 / 200000000)) (hi := (299439943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455019740553 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455019740553 / 250000000000) = 1/(250000000000 / 455019740553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (119775977 / 200000000) (299439943 / 500000000) (Real.log (455019740553 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (455019740553 / 250000000000) = -Real.log (250000000000 / 455019740553) := by
    rw [show ((455019740553 / 250000000000) : ℝ) = ((250000000000 / 455019740553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (426832309 / 1000000000) ≤ -Real.log (250000000000 / 383098917907) ∧
    -Real.log (250000000000 / 383098917907) ≤ (42683231 / 100000000) := by
  have h := checkLog_sound (w := (133098917907 / 633098917907)) (n := 12)
    (lo := (426832309 / 1000000000)) (hi := (42683231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383098917907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383098917907 / 250000000000) = 1/(250000000000 / 383098917907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (426832309 / 1000000000) (42683231 / 100000000) (Real.log (383098917907 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (383098917907 / 250000000000) = -Real.log (250000000000 / 383098917907) := by
    rw [show ((383098917907 / 250000000000) : ℝ) = ((250000000000 / 383098917907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (427508229 / 1000000000) ≤ -Real.log (125000000000 / 191678974923) ∧
    -Real.log (125000000000 / 191678974923) ≤ (42750823 / 100000000) := by
  have h := checkLog_sound (w := (66678974923 / 316678974923)) (n := 12)
    (lo := (427508229 / 1000000000)) (hi := (42750823 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191678974923 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191678974923 / 125000000000) = 1/(125000000000 / 191678974923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (427508229 / 1000000000) (42750823 / 100000000) (Real.log (191678974923 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (191678974923 / 125000000000) = -Real.log (125000000000 / 191678974923) := by
    rw [show ((191678974923 / 125000000000) : ℝ) = ((125000000000 / 191678974923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0460

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0461Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0461
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

theorem reflection_log_1_neg : (92745179 / 500000000) ≤ -Real.log (10240 / 12327) ∧
    -Real.log (10240 / 12327) ≤ (185490359 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 22567)) (n := 12)
    (lo := (92745179 / 500000000)) (hi := (185490359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12327 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12327 / 10240) = 1/(10240 / 12327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (92745179 / 500000000) (185490359 / 1000000000) (Real.log (12327 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12327 / 10240) = -Real.log (10240 / 12327) := by
    rw [show ((12327 / 10240) : ℝ) = ((10240 / 12327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (227915661 / 1000000000) ≤ -Real.log (8153 / 10240) ∧
    -Real.log (8153 / 10240) ≤ (113957831 / 500000000) := by
  have h := checkLog_sound (w := (2087 / 18393)) (n := 12)
    (lo := (227915661 / 1000000000)) (hi := (113957831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8153) = 1/(8153 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113957831 / 500000000) (-227915661 / 1000000000) (Real.log (8153 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (185246961 / 1000000000) ≤ -Real.log (2560 / 3081) ∧
    -Real.log (2560 / 3081) ≤ (92623481 / 500000000) := by
  have h := checkLog_sound (w := (521 / 5641)) (n := 12)
    (lo := (185246961 / 1000000000)) (hi := (92623481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3081 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3081 / 2560) = 1/(2560 / 3081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (185246961 / 1000000000) (92623481 / 500000000) (Real.log (3081 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3081 / 2560) = -Real.log (2560 / 3081) := by
    rw [show ((3081 / 2560) : ℝ) = ((2560 / 3081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (113773883 / 500000000) ≤ -Real.log (2039 / 2560) ∧
    -Real.log (2039 / 2560) ≤ (227547767 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 4599)) (n := 12)
    (lo := (113773883 / 500000000)) (hi := (227547767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2039) = 1/(2039 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-227547767 / 1000000000) (-113773883 / 500000000) (Real.log (2039 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10684323 / 31250000) ≤ -Real.log (5120 / 7207) ∧
    -Real.log (5120 / 7207) ≤ (341898337 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 12327)) (n := 12)
    (lo := (10684323 / 31250000)) (hi := (341898337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7207 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7207 / 5120) = 1/(5120 / 7207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10684323 / 31250000) (341898337 / 1000000000) (Real.log (7207 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7207 / 5120) = -Real.log (5120 / 7207) := by
    rw [show ((7207 / 5120) : ℝ) = ((5120 / 7207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (52360221 / 100000000) ≤ -Real.log (3033 / 5120) ∧
    -Real.log (3033 / 5120) ≤ (523602211 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 8153)) (n := 12)
    (lo := (52360221 / 100000000)) (hi := (523602211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3033) = 1/(3033 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-523602211 / 1000000000) (-52360221 / 100000000) (Real.log (3033 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (85370497 / 250000000) ≤ -Real.log (1280 / 1801) ∧
    -Real.log (1280 / 1801) ≤ (341481989 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 3081)) (n := 12)
    (lo := (85370497 / 250000000)) (hi := (341481989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1801 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1801 / 1280) = 1/(1280 / 1801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (85370497 / 250000000) (341481989 / 1000000000) (Real.log (1801 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1801 / 1280) = -Real.log (1280 / 1801) := by
    rw [show ((1801 / 1280) : ℝ) = ((1280 / 1801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (522613579 / 1000000000) ≤ -Real.log (759 / 1280) ∧
    -Real.log (759 / 1280) ≤ (26130679 / 50000000) := by
  have h := checkLog_sound (w := (521 / 2039)) (n := 12)
    (lo := (522613579 / 1000000000)) (hi := (26130679 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 759) = 1/(759 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26130679 / 50000000) (-522613579 / 1000000000) (Real.log (759 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (254604233 / 1000000000) ≤ -Real.log (1000000 / 1289951) ∧
    -Real.log (1000000 / 1289951) ≤ (127302117 / 500000000) := by
  have h := checkLog_sound (w := (289951 / 2289951)) (n := 12)
    (lo := (254604233 / 1000000000)) (hi := (127302117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289951 / 1000000) = 1/(1000000 / 1289951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (254604233 / 1000000000) (127302117 / 500000000) (Real.log (1289951 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1289951 / 1000000) = -Real.log (1000000 / 1289951) := by
    rw [show ((1289951 / 1000000) : ℝ) = ((1000000 / 1289951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (342421297 / 1000000000) ≤ -Real.log (710049 / 1000000) ∧
    -Real.log (710049 / 1000000) ≤ (171210649 / 500000000) := by
  have h := checkLog_sound (w := (289951 / 1710049)) (n := 12)
    (lo := (342421297 / 1000000000)) (hi := (171210649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 710049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 710049) = 1/(710049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-171210649 / 500000000) (-342421297 / 1000000000) (Real.log (710049 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15933353 / 62500000) ≤ -Real.log (125000 / 161297) ∧
    -Real.log (125000 / 161297) ≤ (254933649 / 1000000000) := by
  have h := checkLog_sound (w := (36297 / 286297)) (n := 12)
    (lo := (15933353 / 62500000)) (hi := (254933649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161297 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161297 / 125000) = 1/(125000 / 161297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15933353 / 62500000) (254933649 / 1000000000) (Real.log (161297 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161297 / 125000) = -Real.log (125000 / 161297) := by
    rw [show ((161297 / 125000) : ℝ) = ((125000 / 161297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (171510013 / 500000000) ≤ -Real.log (88703 / 125000) ∧
    -Real.log (88703 / 125000) ≤ (343020027 / 1000000000) := by
  have h := checkLog_sound (w := (36297 / 213703)) (n := 12)
    (lo := (171510013 / 500000000)) (hi := (343020027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88703) = 1/(88703 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-343020027 / 1000000000) (-171510013 / 500000000) (Real.log (88703 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23818557 / 125000000) ≤ -Real.log (1000000 / 1209913) ∧
    -Real.log (1000000 / 1209913) ≤ (190548457 / 1000000000) := by
  have h := checkLog_sound (w := (209913 / 2209913)) (n := 12)
    (lo := (23818557 / 125000000)) (hi := (190548457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209913 / 1000000) = 1/(1000000 / 1209913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23818557 / 125000000) (190548457 / 1000000000) (Real.log (1209913 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1209913 / 1000000) = -Real.log (1000000 / 1209913) := by
    rw [show ((1209913 / 1000000) : ℝ) = ((1000000 / 1209913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (235612213 / 1000000000) ≤ -Real.log (790087 / 1000000) ∧
    -Real.log (790087 / 1000000) ≤ (117806107 / 500000000) := by
  have h := checkLog_sound (w := (209913 / 1790087)) (n := 12)
    (lo := (235612213 / 1000000000)) (hi := (117806107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790087) = 1/(790087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-117806107 / 500000000) (-235612213 / 1000000000) (Real.log (790087 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38162911 / 200000000) ≤ -Real.log (200000 / 242047) ∧
    -Real.log (200000 / 242047) ≤ (47703639 / 250000000) := by
  have h := checkLog_sound (w := (42047 / 442047)) (n := 12)
    (lo := (38162911 / 200000000)) (hi := (47703639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242047 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242047 / 200000) = 1/(200000 / 242047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38162911 / 200000000) (47703639 / 250000000) (Real.log (242047 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (242047 / 200000) = -Real.log (200000 / 242047) := by
    rw [show ((242047 / 200000) : ℝ) = ((200000 / 242047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (118009923 / 500000000) ≤ -Real.log (157953 / 200000) ∧
    -Real.log (157953 / 200000) ≤ (236019847 / 1000000000) := by
  have h := checkLog_sound (w := (42047 / 357953)) (n := 12)
    (lo := (118009923 / 500000000)) (hi := (236019847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157953) = 1/(157953 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-236019847 / 1000000000) (-118009923 / 500000000) (Real.log (157953 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (59702553 / 100000000) ≤ -Real.log (500000000000 / 908353507997) ∧
    -Real.log (500000000000 / 908353507997) ≤ (597025531 / 1000000000) := by
  have h := checkLog_sound (w := (408353507997 / 1408353507997)) (n := 12)
    (lo := (59702553 / 100000000)) (hi := (597025531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((908353507997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(908353507997 / 500000000000) = 1/(500000000000 / 908353507997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (59702553 / 100000000) (597025531 / 1000000000) (Real.log (908353507997 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (908353507997 / 500000000000) = -Real.log (500000000000 / 908353507997) := by
    rw [show ((908353507997 / 500000000000) : ℝ) = ((500000000000 / 908353507997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (23918147 / 40000000) ≤ -Real.log (62500000000 / 113649622899) ∧
    -Real.log (62500000000 / 113649622899) ≤ (149488419 / 250000000) := by
  have h := checkLog_sound (w := (51149622899 / 176149622899)) (n := 12)
    (lo := (23918147 / 40000000)) (hi := (149488419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113649622899 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113649622899 / 62500000000) = 1/(62500000000 / 113649622899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (23918147 / 40000000) (149488419 / 250000000) (Real.log (113649622899 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (113649622899 / 62500000000) = -Real.log (62500000000 / 113649622899) := by
    rw [show ((113649622899 / 62500000000) : ℝ) = ((62500000000 / 113649622899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (426160669 / 1000000000) ≤ -Real.log (500000000000 / 765683399423) ∧
    -Real.log (500000000000 / 765683399423) ≤ (42616067 / 100000000) := by
  have h := checkLog_sound (w := (265683399423 / 1265683399423)) (n := 12)
    (lo := (426160669 / 1000000000)) (hi := (42616067 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765683399423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765683399423 / 500000000000) = 1/(500000000000 / 765683399423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (426160669 / 1000000000) (42616067 / 100000000) (Real.log (765683399423 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (765683399423 / 500000000000) = -Real.log (500000000000 / 765683399423) := by
    rw [show ((765683399423 / 500000000000) : ℝ) = ((500000000000 / 765683399423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (426834401 / 1000000000) ≤ -Real.log (250000000000 / 383099719537) ∧
    -Real.log (250000000000 / 383099719537) ≤ (213417201 / 500000000) := by
  have h := checkLog_sound (w := (133099719537 / 633099719537)) (n := 12)
    (lo := (426834401 / 1000000000)) (hi := (213417201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383099719537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383099719537 / 250000000000) = 1/(250000000000 / 383099719537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (426834401 / 1000000000) (213417201 / 500000000) (Real.log (383099719537 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (383099719537 / 250000000000) = -Real.log (250000000000 / 383099719537) := by
    rw [show ((383099719537 / 250000000000) : ℝ) = ((250000000000 / 383099719537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0461

end


