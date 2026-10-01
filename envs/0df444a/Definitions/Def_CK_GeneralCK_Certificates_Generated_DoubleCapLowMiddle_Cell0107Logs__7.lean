-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0107Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0107Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:00:37.019999+00:00
-- url     : https://prove2.me/theorems/abb2e2da-4b78-4323-93ba-e9882fe6a04b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0107Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0108Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0107Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0108Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0109Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0110Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0111Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0112Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0113Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0107Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0108Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0109Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0110Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0111Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0112Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0113Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0107Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0108Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0109Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0110Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0111Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0112Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0113Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0107Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0108Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0109Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0110Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0111Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0112Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0113Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0107Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0107
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

theorem reflection_log_1_neg : (335040221 / 500000000) ≤ -Real.log (10240 / 20013) ∧
    -Real.log (10240 / 20013) ≤ (670080443 / 1000000000) := by
  have h := checkLog_sound (w := (9773 / 30253)) (n := 12)
    (lo := (335040221 / 500000000)) (hi := (670080443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20013 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20013 / 10240) = 1/(10240 / 20013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (335040221 / 500000000) (670080443 / 1000000000) (Real.log (20013 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20013 / 10240) = -Real.log (10240 / 20013) := by
    rw [show ((20013 / 10240) : ℝ) = ((10240 / 20013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1543863819 / 500000000) ≤ -Real.log (467 / 10240) ∧
    -Real.log (467 / 10240) ≤ (3087727643 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 467) = 1/(467 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3087727643 / 1000000000) (-1543863819 / 500000000) (Real.log (467 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (167472637 / 250000000) ≤ -Real.log (25600 / 50023) ∧
    -Real.log (25600 / 50023) ≤ (669890549 / 1000000000) := by
  have h := checkLog_sound (w := (24423 / 75623)) (n := 12)
    (lo := (167472637 / 250000000)) (hi := (669890549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50023 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50023 / 25600) = 1/(25600 / 50023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (167472637 / 250000000) (669890549 / 1000000000) (Real.log (50023 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50023 / 25600) = -Real.log (25600 / 50023) := by
    rw [show ((50023 / 25600) : ℝ) = ((25600 / 50023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19247647 / 6250000) ≤ -Real.log (1177 / 25600) ∧
    -Real.log (1177 / 25600) ≤ (123184941 / 40000000) := by
  have h := checkLog_sound (w := (423 / 2777)) (n := 12)
    (lo := (767587 / 2500000)) (hi := (307034801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1177) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1177) = 1/(1177 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-123184941 / 40000000) (-19247647 / 6250000) (Real.log (1177 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (323234521 / 500000000) ≤ -Real.log (5120 / 9773) ∧
    -Real.log (5120 / 9773) ≤ (646469043 / 1000000000) := by
  have h := checkLog_sound (w := (4653 / 14893)) (n := 12)
    (lo := (323234521 / 500000000)) (hi := (646469043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9773 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9773 / 5120) = 1/(5120 / 9773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (323234521 / 500000000) (646469043 / 1000000000) (Real.log (9773 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9773 / 5120) = -Real.log (5120 / 9773) := by
    rw [show ((9773 / 5120) : ℝ) = ((5120 / 9773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1197290229 / 500000000) ≤ -Real.log (467 / 5120) ∧
    -Real.log (467 / 5120) ≤ (1197290231 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 467) = 1/(467 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1197290231 / 500000000) (-1197290229 / 500000000) (Real.log (467 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (32304007 / 50000000) ≤ -Real.log (12800 / 24423) ∧
    -Real.log (12800 / 24423) ≤ (646080141 / 1000000000) := by
  have h := checkLog_sound (w := (11623 / 37223)) (n := 12)
    (lo := (32304007 / 50000000)) (hi := (646080141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24423 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24423 / 12800) = 1/(12800 / 24423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (32304007 / 50000000) (646080141 / 1000000000) (Real.log (24423 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24423 / 12800) = -Real.log (12800 / 24423) := by
    rw [show ((24423 / 12800) : ℝ) = ((12800 / 24423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (119323817 / 50000000) ≤ -Real.log (1177 / 12800) ∧
    -Real.log (1177 / 12800) ≤ (298309543 / 125000000) := by
  have h := checkLog_sound (w := (423 / 2777)) (n := 12)
    (lo := (767587 / 2500000)) (hi := (307034801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1177) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1177) = 1/(1177 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-298309543 / 125000000) (-119323817 / 50000000) (Real.log (1177 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42136851 / 62500000) ≤ -Real.log (500000 / 981221) ∧
    -Real.log (500000 / 981221) ≤ (674189617 / 1000000000) := by
  have h := checkLog_sound (w := (481221 / 1481221)) (n := 12)
    (lo := (42136851 / 62500000)) (hi := (674189617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981221 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981221 / 500000) = 1/(500000 / 981221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42136851 / 62500000) (674189617 / 1000000000) (Real.log (981221 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (981221 / 500000) = -Real.log (500000 / 981221) := by
    rw [show ((981221 / 500000) : ℝ) = ((500000 / 981221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3281868871 / 1000000000) ≤ -Real.log (18779 / 500000) ∧
    -Real.log (18779 / 500000) ≤ (820467219 / 250000000) := by
  have h := checkLog_sound (w := (12471 / 50029)) (n := 12)
    (lo := (509280151 / 1000000000)) (hi := (63660019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18779) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18779) = 1/(18779 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-820467219 / 250000000) (-3281868871 / 1000000000) (Real.log (18779 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (337167671 / 500000000) ≤ -Real.log (125000 / 245341) ∧
    -Real.log (125000 / 245341) ≤ (674335343 / 1000000000) := by
  have h := checkLog_sound (w := (120341 / 370341)) (n := 12)
    (lo := (337167671 / 500000000)) (hi := (674335343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245341 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245341 / 125000) = 1/(125000 / 245341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (337167671 / 500000000) (674335343 / 1000000000) (Real.log (245341 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (245341 / 125000) = -Real.log (125000 / 245341) := by
    rw [show ((245341 / 125000) : ℝ) = ((125000 / 245341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1644756451 / 500000000) ≤ -Real.log (4659 / 125000) ∧
    -Real.log (4659 / 125000) ≤ (3289512907 / 1000000000) := by
  have h := checkLog_sound (w := (6307 / 24943)) (n := 12)
    (lo := (258462091 / 500000000)) (hi := (516924183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9318) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 9318) = 1/(4659 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3289512907 / 1000000000) (-1644756451 / 500000000) (Real.log (4659 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21062103 / 31250000) ≤ -Real.log (200000 / 392409) ∧
    -Real.log (200000 / 392409) ≤ (673987297 / 1000000000) := by
  have h := checkLog_sound (w := (192409 / 592409)) (n := 12)
    (lo := (21062103 / 31250000)) (hi := (673987297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392409 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392409 / 200000) = 1/(200000 / 392409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21062103 / 31250000) (673987297 / 1000000000) (Real.log (392409 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (392409 / 200000) = -Real.log (200000 / 392409) := by
    rw [show ((392409 / 200000) : ℝ) = ((200000 / 392409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3271354029 / 1000000000) ≤ -Real.log (7591 / 200000) ∧
    -Real.log (7591 / 200000) ≤ (1635677017 / 500000000) := by
  have h := checkLog_sound (w := (4909 / 20091)) (n := 12)
    (lo := (498765309 / 1000000000)) (hi := (49876531 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7591) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 7591) = 1/(7591 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1635677017 / 500000000) (-3271354029 / 1000000000) (Real.log (7591 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (674136619 / 1000000000) ≤ -Real.log (500000 / 981169) ∧
    -Real.log (500000 / 981169) ≤ (33706831 / 50000000) := by
  have h := checkLog_sound (w := (481169 / 1481169)) (n := 12)
    (lo := (674136619 / 1000000000)) (hi := (33706831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981169 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981169 / 500000) = 1/(500000 / 981169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (674136619 / 1000000000) (33706831 / 50000000) (Real.log (981169 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (981169 / 500000) = -Real.log (500000 / 981169) := by
    rw [show ((981169 / 500000) : ℝ) = ((500000 / 981169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (102471989 / 31250000) ≤ -Real.log (18831 / 500000) ∧
    -Real.log (18831 / 500000) ≤ (3279103653 / 1000000000) := by
  have h := checkLog_sound (w := (12419 / 50081)) (n := 12)
    (lo := (31657183 / 62500000)) (hi := (506514929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18831) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18831) = 1/(18831 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3279103653 / 1000000000) (-102471989 / 31250000) (Real.log (18831 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3956058487 / 1000000000) ≤ -Real.log (500000000000 / 26125485915117) ∧
    -Real.log (500000000000 / 26125485915117) ≤ (3956058493 / 1000000000) := by
  have h := checkLog_sound (w := (10125485915117 / 42125485915117)) (n := 12)
    (lo := (490322587 / 1000000000)) (hi := (122580647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26125485915117 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26125485915117 / 16000000000000) = 1/(500000000000 / 26125485915117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3956058487 / 1000000000) (3956058493 / 1000000000) (Real.log (26125485915117 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (26125485915117 / 500000000000) = -Real.log (500000000000 / 26125485915117) := by
    rw [show ((26125485915117 / 500000000000) : ℝ) = ((500000000000 / 26125485915117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3963848243 / 1000000000) ≤ -Real.log (31250000000 / 1645611987551) ∧
    -Real.log (31250000000 / 1645611987551) ≤ (3963848249 / 1000000000) := by
  have h := checkLog_sound (w := (645611987551 / 2645611987551)) (n := 12)
    (lo := (498112343 / 1000000000)) (hi := (62264043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1645611987551 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1645611987551 / 1000000000000) = 1/(31250000000 / 1645611987551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3963848243 / 1000000000) (3963848249 / 1000000000) (Real.log (1645611987551 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1645611987551 / 31250000000) = -Real.log (31250000000 / 1645611987551) := by
    rw [show ((1645611987551 / 31250000000) : ℝ) = ((31250000000 / 1645611987551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (157813653 / 40000000) ≤ -Real.log (62500000000 / 3230873732051) ∧
    -Real.log (62500000000 / 3230873732051) ≤ (3945341331 / 1000000000) := by
  have h := checkLog_sound (w := (1230873732051 / 5230873732051)) (n := 12)
    (lo := (19184217 / 40000000)) (hi := (239802713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3230873732051 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3230873732051 / 2000000000000) = 1/(62500000000 / 3230873732051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (157813653 / 40000000) (3945341331 / 1000000000) (Real.log (3230873732051 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3230873732051 / 62500000000) = -Real.log (62500000000 / 3230873732051) := by
    rw [show ((3230873732051 / 62500000000) : ℝ) = ((62500000000 / 3230873732051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3953240267 / 1000000000) ≤ -Real.log (250000000000 / 13025981095003) ∧
    -Real.log (250000000000 / 13025981095003) ≤ (3953240273 / 1000000000) := by
  have h := checkLog_sound (w := (5025981095003 / 21025981095003)) (n := 12)
    (lo := (487504367 / 1000000000)) (hi := (30469023 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13025981095003 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13025981095003 / 8000000000000) = 1/(250000000000 / 13025981095003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3953240267 / 1000000000) (3953240273 / 1000000000) (Real.log (13025981095003 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13025981095003 / 250000000000) = -Real.log (250000000000 / 13025981095003) := by
    rw [show ((13025981095003 / 250000000000) : ℝ) = ((250000000000 / 13025981095003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0107

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0108Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0108
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

theorem reflection_log_1_neg : (167472637 / 250000000) ≤ -Real.log (25600 / 50023) ∧
    -Real.log (25600 / 50023) ≤ (669890549 / 1000000000) := by
  have h := checkLog_sound (w := (24423 / 75623)) (n := 12)
    (lo := (167472637 / 250000000)) (hi := (669890549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50023 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50023 / 25600) = 1/(25600 / 50023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (167472637 / 250000000) (669890549 / 1000000000) (Real.log (50023 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50023 / 25600) = -Real.log (25600 / 50023) := by
    rw [show ((50023 / 25600) : ℝ) = ((25600 / 50023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19247647 / 6250000) ≤ -Real.log (1177 / 25600) ∧
    -Real.log (1177 / 25600) ≤ (123184941 / 40000000) := by
  have h := checkLog_sound (w := (423 / 2777)) (n := 12)
    (lo := (767587 / 2500000)) (hi := (307034801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1177) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1177) = 1/(1177 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-123184941 / 40000000) (-19247647 / 6250000) (Real.log (1177 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (669700617 / 1000000000) ≤ -Real.log (51200 / 100027) ∧
    -Real.log (51200 / 100027) ≤ (334850309 / 500000000) := by
  have h := checkLog_sound (w := (48827 / 151227)) (n := 12)
    (lo := (669700617 / 1000000000)) (hi := (334850309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100027 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100027 / 51200) = 1/(51200 / 100027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (669700617 / 1000000000) (334850309 / 500000000) (Real.log (100027 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100027 / 51200) = -Real.log (51200 / 100027) := by
    rw [show ((100027 / 51200) : ℝ) = ((51200 / 100027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (383948069 / 125000000) ≤ -Real.log (2373 / 51200) ∧
    -Real.log (2373 / 51200) ≤ (3071584557 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 5573)) (n := 12)
    (lo := (37374479 / 125000000)) (hi := (298995833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2373) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2373) = 1/(2373 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3071584557 / 1000000000) (-383948069 / 125000000) (Real.log (2373 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (32304007 / 50000000) ≤ -Real.log (12800 / 24423) ∧
    -Real.log (12800 / 24423) ≤ (646080141 / 1000000000) := by
  have h := checkLog_sound (w := (11623 / 37223)) (n := 12)
    (lo := (32304007 / 50000000)) (hi := (646080141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24423 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24423 / 12800) = 1/(12800 / 24423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (32304007 / 50000000) (646080141 / 1000000000) (Real.log (24423 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24423 / 12800) = -Real.log (12800 / 24423) := by
    rw [show ((24423 / 12800) : ℝ) = ((12800 / 24423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (119323817 / 50000000) ≤ -Real.log (1177 / 12800) ∧
    -Real.log (1177 / 12800) ≤ (298309543 / 125000000) := by
  have h := checkLog_sound (w := (423 / 2777)) (n := 12)
    (lo := (767587 / 2500000)) (hi := (307034801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1177) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1177) = 1/(1177 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-298309543 / 125000000) (-119323817 / 50000000) (Real.log (1177 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (645691087 / 1000000000) ≤ -Real.log (25600 / 48827) ∧
    -Real.log (25600 / 48827) ≤ (40355693 / 62500000) := by
  have h := checkLog_sound (w := (23227 / 74427)) (n := 12)
    (lo := (645691087 / 1000000000)) (hi := (40355693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48827 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48827 / 25600) = 1/(25600 / 48827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (645691087 / 1000000000) (40355693 / 62500000) (Real.log (48827 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48827 / 25600) = -Real.log (25600 / 48827) := by
    rw [show ((48827 / 25600) : ℝ) = ((25600 / 48827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (594609343 / 250000000) ≤ -Real.log (2373 / 25600) ∧
    -Real.log (2373 / 25600) ≤ (9290771 / 3906250) := by
  have h := checkLog_sound (w := (827 / 5573)) (n := 12)
    (lo := (37374479 / 125000000)) (hi := (298995833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2373) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2373) = 1/(2373 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9290771 / 3906250) (-594609343 / 250000000) (Real.log (2373 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (674044887 / 1000000000) ≤ -Real.log (500000 / 981079) ∧
    -Real.log (500000 / 981079) ≤ (84255611 / 125000000) := by
  have h := checkLog_sound (w := (481079 / 1481079)) (n := 12)
    (lo := (674044887 / 1000000000)) (hi := (84255611 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981079 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981079 / 500000) = 1/(500000 / 981079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (674044887 / 1000000000) (84255611 / 125000000) (Real.log (981079 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (981079 / 500000) = -Real.log (500000 / 981079) := by
    rw [show ((981079 / 500000) : ℝ) = ((500000 / 981079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3274335679 / 1000000000) ≤ -Real.log (18921 / 500000) ∧
    -Real.log (18921 / 500000) ≤ (818583921 / 250000000) := by
  have h := checkLog_sound (w := (12329 / 50171)) (n := 12)
    (lo := (501746959 / 1000000000)) (hi := (6271837 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18921) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18921) = 1/(18921 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-818583921 / 250000000) (-3274335679 / 1000000000) (Real.log (18921 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (5393521 / 8000000) ≤ -Real.log (1000000 / 1962443) ∧
    -Real.log (1000000 / 1962443) ≤ (337095063 / 500000000) := by
  have h := checkLog_sound (w := (962443 / 2962443)) (n := 12)
    (lo := (5393521 / 8000000)) (hi := (337095063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962443 / 1000000) = 1/(1000000 / 1962443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (5393521 / 8000000) (337095063 / 500000000) (Real.log (1962443 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1962443 / 1000000) = -Real.log (1000000 / 1962443) := by
    rw [show ((1962443 / 1000000) : ℝ) = ((1000000 / 1962443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3281895497 / 1000000000) ≤ -Real.log (37557 / 1000000) ∧
    -Real.log (37557 / 1000000) ≤ (1640947751 / 500000000) := by
  have h := checkLog_sound (w := (24943 / 100057)) (n := 12)
    (lo := (509306777 / 1000000000)) (hi := (254653389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37557) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37557) = 1/(37557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1640947751 / 500000000) (-3281895497 / 1000000000) (Real.log (37557 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (673838971 / 1000000000) ≤ -Real.log (500000 / 980877) ∧
    -Real.log (500000 / 980877) ≤ (168459743 / 250000000) := by
  have h := checkLog_sound (w := (480877 / 1480877)) (n := 12)
    (lo := (673838971 / 1000000000)) (hi := (168459743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980877 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980877 / 500000) = 1/(500000 / 980877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (673838971 / 1000000000) (168459743 / 250000000) (Real.log (980877 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (980877 / 500000) = -Real.log (500000 / 980877) := by
    rw [show ((980877 / 500000) : ℝ) = ((500000 / 980877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3263716297 / 1000000000) ≤ -Real.log (19123 / 500000) ∧
    -Real.log (19123 / 500000) ≤ (1631858151 / 500000000) := by
  have h := checkLog_sound (w := (12127 / 50373)) (n := 12)
    (lo := (491127577 / 1000000000)) (hi := (245563789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19123) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19123) = 1/(19123 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1631858151 / 500000000) (-3263716297 / 1000000000) (Real.log (19123 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (336993903 / 500000000) ≤ -Real.log (500000 / 981023) ∧
    -Real.log (500000 / 981023) ≤ (673987807 / 1000000000) := by
  have h := checkLog_sound (w := (481023 / 1481023)) (n := 12)
    (lo := (336993903 / 500000000)) (hi := (673987807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981023 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981023 / 500000) = 1/(500000 / 981023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (336993903 / 500000000) (673987807 / 1000000000) (Real.log (981023 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (981023 / 500000) = -Real.log (500000 / 981023) := by
    rw [show ((981023 / 500000) : ℝ) = ((500000 / 981023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (408922547 / 125000000) ≤ -Real.log (18977 / 500000) ∧
    -Real.log (18977 / 500000) ≤ (3271380381 / 1000000000) := by
  have h := checkLog_sound (w := (12273 / 50227)) (n := 12)
    (lo := (62348957 / 125000000)) (hi := (498791657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18977) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18977) = 1/(18977 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3271380381 / 1000000000) (-408922547 / 125000000) (Real.log (18977 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3948380567 / 1000000000) ≤ -Real.log (62500000000 / 3240708075683) ∧
    -Real.log (62500000000 / 3240708075683) ≤ (3948380573 / 1000000000) := by
  have h := checkLog_sound (w := (1240708075683 / 5240708075683)) (n := 12)
    (lo := (482644667 / 1000000000)) (hi := (120661167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3240708075683 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3240708075683 / 2000000000000) = 1/(62500000000 / 3240708075683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3948380567 / 1000000000) (3948380573 / 1000000000) (Real.log (3240708075683 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3240708075683 / 62500000000) = -Real.log (62500000000 / 3240708075683) := by
    rw [show ((3240708075683 / 62500000000) : ℝ) = ((62500000000 / 3240708075683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1978042811 / 500000000) ≤ -Real.log (250000000000 / 13063097425247) ∧
    -Real.log (250000000000 / 13063097425247) ≤ (989021407 / 250000000) := by
  have h := checkLog_sound (w := (5063097425247 / 21063097425247)) (n := 12)
    (lo := (245174861 / 500000000)) (hi := (490349723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13063097425247 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13063097425247 / 8000000000000) = 1/(250000000000 / 13063097425247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1978042811 / 500000000) (989021407 / 250000000) (Real.log (13063097425247 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13063097425247 / 250000000000) = -Real.log (250000000000 / 13063097425247) := by
    rw [show ((13063097425247 / 250000000000) : ℝ) = ((250000000000 / 13063097425247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3937555267 / 1000000000) ≤ -Real.log (50000000000 / 2564652512681) ∧
    -Real.log (50000000000 / 2564652512681) ≤ (3937555273 / 1000000000) := by
  have h := checkLog_sound (w := (964652512681 / 4164652512681)) (n := 12)
    (lo := (471819367 / 1000000000)) (hi := (58977421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2564652512681 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2564652512681 / 1600000000000) = 1/(50000000000 / 2564652512681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3937555267 / 1000000000) (3937555273 / 1000000000) (Real.log (2564652512681 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2564652512681 / 50000000000) = -Real.log (50000000000 / 2564652512681) := by
    rw [show ((2564652512681 / 50000000000) : ℝ) = ((50000000000 / 2564652512681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1972684091 / 500000000) ≤ -Real.log (250000000000 / 12923842019287) ∧
    -Real.log (250000000000 / 12923842019287) ≤ (986342047 / 250000000) := by
  have h := checkLog_sound (w := (4923842019287 / 20923842019287)) (n := 12)
    (lo := (239816141 / 500000000)) (hi := (479632283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12923842019287 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12923842019287 / 8000000000000) = 1/(250000000000 / 12923842019287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1972684091 / 500000000) (986342047 / 250000000) (Real.log (12923842019287 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (12923842019287 / 250000000000) = -Real.log (250000000000 / 12923842019287) := by
    rw [show ((12923842019287 / 250000000000) : ℝ) = ((250000000000 / 12923842019287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0108

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0109Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0109
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

theorem reflection_log_1_neg : (669700617 / 1000000000) ≤ -Real.log (51200 / 100027) ∧
    -Real.log (51200 / 100027) ≤ (334850309 / 500000000) := by
  have h := checkLog_sound (w := (48827 / 151227)) (n := 12)
    (lo := (669700617 / 1000000000)) (hi := (334850309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100027 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100027 / 51200) = 1/(51200 / 100027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (669700617 / 1000000000) (334850309 / 500000000) (Real.log (100027 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100027 / 51200) = -Real.log (51200 / 100027) := by
    rw [show ((100027 / 51200) : ℝ) = ((51200 / 100027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (383948069 / 125000000) ≤ -Real.log (2373 / 51200) ∧
    -Real.log (2373 / 51200) ≤ (3071584557 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 5573)) (n := 12)
    (lo := (37374479 / 125000000)) (hi := (298995833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2373) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2373) = 1/(2373 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3071584557 / 1000000000) (-383948069 / 125000000) (Real.log (2373 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13390213 / 20000000) ≤ -Real.log (6400 / 12501) ∧
    -Real.log (6400 / 12501) ≤ (669510651 / 1000000000) := by
  have h := checkLog_sound (w := (6101 / 18901)) (n := 12)
    (lo := (13390213 / 20000000)) (hi := (669510651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12501 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12501 / 6400) = 1/(6400 / 12501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13390213 / 20000000) (669510651 / 1000000000) (Real.log (12501 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12501 / 6400) = -Real.log (6400 / 12501) := by
    rw [show ((12501 / 6400) : ℝ) = ((6400 / 12501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3063609693 / 1000000000) ≤ -Real.log (299 / 6400) ∧
    -Real.log (299 / 6400) ≤ (1531804849 / 500000000) := by
  have h := checkLog_sound (w := (101 / 699)) (n := 12)
    (lo := (291020973 / 1000000000)) (hi := (145510487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 299) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 299) = 1/(299 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1531804849 / 500000000) (-3063609693 / 1000000000) (Real.log (299 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (645691087 / 1000000000) ≤ -Real.log (25600 / 48827) ∧
    -Real.log (25600 / 48827) ≤ (40355693 / 62500000) := by
  have h := checkLog_sound (w := (23227 / 74427)) (n := 12)
    (lo := (645691087 / 1000000000)) (hi := (40355693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48827 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48827 / 25600) = 1/(25600 / 48827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (645691087 / 1000000000) (40355693 / 62500000) (Real.log (48827 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48827 / 25600) = -Real.log (25600 / 48827) := by
    rw [show ((48827 / 25600) : ℝ) = ((25600 / 48827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (594609343 / 250000000) ≤ -Real.log (2373 / 25600) ∧
    -Real.log (2373 / 25600) ≤ (9290771 / 3906250) := by
  have h := checkLog_sound (w := (827 / 5573)) (n := 12)
    (lo := (37374479 / 125000000)) (hi := (298995833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2373) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2373) = 1/(2373 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-9290771 / 3906250) (-594609343 / 250000000) (Real.log (2373 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (322650941 / 500000000) ≤ -Real.log (3200 / 6101) ∧
    -Real.log (3200 / 6101) ≤ (645301883 / 1000000000) := by
  have h := checkLog_sound (w := (2901 / 9301)) (n := 12)
    (lo := (322650941 / 500000000)) (hi := (645301883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6101 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6101 / 3200) = 1/(3200 / 6101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (322650941 / 500000000) (645301883 / 1000000000) (Real.log (6101 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6101 / 3200) = -Real.log (3200 / 6101) := by
    rw [show ((6101 / 3200) : ℝ) = ((3200 / 6101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2370462513 / 1000000000) ≤ -Real.log (299 / 3200) ∧
    -Real.log (299 / 3200) ≤ (2370462517 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 699)) (n := 12)
    (lo := (291020973 / 1000000000)) (hi := (145510487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 299) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 299) = 1/(299 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2370462517 / 1000000000) (-2370462513 / 1000000000) (Real.log (299 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (336950069 / 500000000) ≤ -Real.log (500000 / 980937) ∧
    -Real.log (500000 / 980937) ≤ (673900139 / 1000000000) := by
  have h := checkLog_sound (w := (480937 / 1480937)) (n := 12)
    (lo := (336950069 / 500000000)) (hi := (673900139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980937 / 500000) = 1/(500000 / 980937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (336950069 / 500000000) (673900139 / 1000000000) (Real.log (980937 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (980937 / 500000) = -Real.log (500000 / 980937) := by
    rw [show ((980937 / 500000) : ℝ) = ((500000 / 980937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (816714703 / 250000000) ≤ -Real.log (19063 / 500000) ∧
    -Real.log (19063 / 500000) ≤ (3266858817 / 1000000000) := by
  have h := checkLog_sound (w := (12187 / 50313)) (n := 12)
    (lo := (123567523 / 250000000)) (hi := (494270093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19063) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19063) = 1/(19063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3266858817 / 1000000000) (-816714703 / 250000000) (Real.log (19063 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (674045397 / 1000000000) ≤ -Real.log (1000000 / 1962159) ∧
    -Real.log (1000000 / 1962159) ≤ (337022699 / 500000000) := by
  have h := checkLog_sound (w := (962159 / 2962159)) (n := 12)
    (lo := (674045397 / 1000000000)) (hi := (337022699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962159 / 1000000) = 1/(1000000 / 1962159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (674045397 / 1000000000) (337022699 / 500000000) (Real.log (1962159 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1962159 / 1000000) = -Real.log (1000000 / 1962159) := by
    rw [show ((1962159 / 1000000) : ℝ) = ((1000000 / 1962159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (654872421 / 200000000) ≤ -Real.log (37841 / 1000000) ∧
    -Real.log (37841 / 1000000) ≤ (327436211 / 100000000) := by
  have h := checkLog_sound (w := (24659 / 100341)) (n := 12)
    (lo := (100354677 / 200000000)) (hi := (250886693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37841) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37841) = 1/(37841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-327436211 / 100000000) (-654872421 / 200000000) (Real.log (37841 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (673690113 / 1000000000) ≤ -Real.log (500000 / 980731) ∧
    -Real.log (500000 / 980731) ≤ (336845057 / 500000000) := by
  have h := checkLog_sound (w := (480731 / 1480731)) (n := 12)
    (lo := (673690113 / 1000000000)) (hi := (336845057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980731 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980731 / 500000) = 1/(500000 / 980731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (673690113 / 1000000000) (336845057 / 500000000) (Real.log (980731 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (980731 / 500000) = -Real.log (500000 / 980731) := by
    rw [show ((980731 / 500000) : ℝ) = ((500000 / 980731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3256110509 / 1000000000) ≤ -Real.log (19269 / 500000) ∧
    -Real.log (19269 / 500000) ≤ (1628055257 / 500000000) := by
  have h := checkLog_sound (w := (11981 / 50519)) (n := 12)
    (lo := (483521789 / 1000000000)) (hi := (48352179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19269) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19269) = 1/(19269 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1628055257 / 500000000) (-3256110509 / 1000000000) (Real.log (19269 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (16845987 / 25000000) ≤ -Real.log (200000 / 392351) ∧
    -Real.log (200000 / 392351) ≤ (673839481 / 1000000000) := by
  have h := checkLog_sound (w := (192351 / 592351)) (n := 12)
    (lo := (16845987 / 25000000)) (hi := (673839481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392351 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392351 / 200000) = 1/(200000 / 392351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (16845987 / 25000000) (673839481 / 1000000000) (Real.log (392351 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (392351 / 200000) = -Real.log (200000 / 392351) := by
    rw [show ((392351 / 200000) : ℝ) = ((200000 / 392351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3263742443 / 1000000000) ≤ -Real.log (7649 / 200000) ∧
    -Real.log (7649 / 200000) ≤ (203983903 / 62500000) := by
  have h := checkLog_sound (w := (4851 / 20149)) (n := 12)
    (lo := (491153723 / 1000000000)) (hi := (122788431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7649) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 7649) = 1/(7649 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-203983903 / 62500000) (-3263742443 / 1000000000) (Real.log (7649 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (78815179 / 20000000) ≤ -Real.log (250000000000 / 12864410113833) ∧
    -Real.log (250000000000 / 12864410113833) ≤ (985189739 / 250000000) := by
  have h := checkLog_sound (w := (4864410113833 / 20864410113833)) (n := 12)
    (lo := (9500461 / 20000000)) (hi := (475023051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12864410113833 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12864410113833 / 8000000000000) = 1/(250000000000 / 12864410113833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (78815179 / 20000000) (985189739 / 250000000) (Real.log (12864410113833 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12864410113833 / 250000000000) = -Real.log (250000000000 / 12864410113833) := by
    rw [show ((12864410113833 / 250000000000) : ℝ) = ((250000000000 / 12864410113833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1974203751 / 500000000) ≤ -Real.log (500000000000 / 25926362939669) ∧
    -Real.log (500000000000 / 25926362939669) ≤ (987101877 / 250000000) := by
  have h := checkLog_sound (w := (9926362939669 / 41926362939669)) (n := 12)
    (lo := (241335801 / 500000000)) (hi := (482671603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25926362939669 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25926362939669 / 16000000000000) = 1/(500000000000 / 25926362939669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1974203751 / 500000000) (987101877 / 250000000) (Real.log (25926362939669 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25926362939669 / 500000000000) = -Real.log (500000000000 / 25926362939669) := by
    rw [show ((25926362939669 / 500000000000) : ℝ) = ((500000000000 / 25926362939669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1964900311 / 500000000) ≤ -Real.log (50000000000 / 2544841455187) ∧
    -Real.log (50000000000 / 2544841455187) ≤ (982450157 / 250000000) := by
  have h := checkLog_sound (w := (944841455187 / 4144841455187)) (n := 12)
    (lo := (232032361 / 500000000)) (hi := (464064723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2544841455187 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2544841455187 / 1600000000000) = 1/(50000000000 / 2544841455187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1964900311 / 500000000) (982450157 / 250000000) (Real.log (2544841455187 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2544841455187 / 50000000000) = -Real.log (50000000000 / 2544841455187) := by
    rw [show ((2544841455187 / 50000000000) : ℝ) = ((50000000000 / 2544841455187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (984395481 / 250000000) ≤ -Real.log (500000000000 / 25647208785463) ∧
    -Real.log (500000000000 / 25647208785463) ≤ (393758193 / 100000000) := by
  have h := checkLog_sound (w := (9647208785463 / 41647208785463)) (n := 12)
    (lo := (58980753 / 125000000)) (hi := (18873841 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25647208785463 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25647208785463 / 16000000000000) = 1/(500000000000 / 25647208785463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (984395481 / 250000000) (393758193 / 100000000) (Real.log (25647208785463 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (25647208785463 / 500000000000) = -Real.log (500000000000 / 25647208785463) := by
    rw [show ((25647208785463 / 500000000000) : ℝ) = ((500000000000 / 25647208785463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0109

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0110Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0110
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

theorem reflection_log_1_neg : (13390213 / 20000000) ≤ -Real.log (6400 / 12501) ∧
    -Real.log (6400 / 12501) ≤ (669510651 / 1000000000) := by
  have h := checkLog_sound (w := (6101 / 18901)) (n := 12)
    (lo := (13390213 / 20000000)) (hi := (669510651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12501 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12501 / 6400) = 1/(6400 / 12501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13390213 / 20000000) (669510651 / 1000000000) (Real.log (12501 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12501 / 6400) = -Real.log (6400 / 12501) := by
    rw [show ((12501 / 6400) : ℝ) = ((6400 / 12501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3063609693 / 1000000000) ≤ -Real.log (299 / 6400) ∧
    -Real.log (299 / 6400) ≤ (1531804849 / 500000000) := by
  have h := checkLog_sound (w := (101 / 699)) (n := 12)
    (lo := (291020973 / 1000000000)) (hi := (145510487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 299) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 299) = 1/(299 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1531804849 / 500000000) (-3063609693 / 1000000000) (Real.log (299 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (669320647 / 1000000000) ≤ -Real.log (51200 / 99989) ∧
    -Real.log (51200 / 99989) ≤ (83665081 / 125000000) := by
  have h := checkLog_sound (w := (48789 / 151189)) (n := 12)
    (lo := (669320647 / 1000000000)) (hi := (83665081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99989 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99989 / 51200) = 1/(51200 / 99989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (669320647 / 1000000000) (83665081 / 125000000) (Real.log (99989 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (99989 / 51200) = -Real.log (51200 / 99989) := by
    rw [show ((99989 / 51200) : ℝ) = ((51200 / 99989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (305569793 / 100000000) ≤ -Real.log (2411 / 51200) ∧
    -Real.log (2411 / 51200) ≤ (611139587 / 200000000) := by
  have h := checkLog_sound (w := (789 / 5611)) (n := 12)
    (lo := (28310921 / 100000000)) (hi := (283109211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2411) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2411) = 1/(2411 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-611139587 / 200000000) (-305569793 / 100000000) (Real.log (2411 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (322650941 / 500000000) ≤ -Real.log (3200 / 6101) ∧
    -Real.log (3200 / 6101) ≤ (645301883 / 1000000000) := by
  have h := checkLog_sound (w := (2901 / 9301)) (n := 12)
    (lo := (322650941 / 500000000)) (hi := (645301883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6101 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6101 / 3200) = 1/(3200 / 6101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (322650941 / 500000000) (645301883 / 1000000000) (Real.log (6101 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6101 / 3200) = -Real.log (3200 / 6101) := by
    rw [show ((6101 / 3200) : ℝ) = ((3200 / 6101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2370462513 / 1000000000) ≤ -Real.log (299 / 3200) ∧
    -Real.log (299 / 3200) ≤ (2370462517 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 699)) (n := 12)
    (lo := (291020973 / 1000000000)) (hi := (145510487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 299) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 299) = 1/(299 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2370462517 / 1000000000) (-2370462513 / 1000000000) (Real.log (299 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (322456263 / 500000000) ≤ -Real.log (25600 / 48789) ∧
    -Real.log (25600 / 48789) ≤ (644912527 / 1000000000) := by
  have h := checkLog_sound (w := (23189 / 74389)) (n := 12)
    (lo := (322456263 / 500000000)) (hi := (644912527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48789 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48789 / 25600) = 1/(25600 / 48789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (322456263 / 500000000) (644912527 / 1000000000) (Real.log (48789 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48789 / 25600) = -Real.log (25600 / 48789) := by
    rw [show ((48789 / 25600) : ℝ) = ((25600 / 48789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9450203 / 4000000) ≤ -Real.log (2411 / 25600) ∧
    -Real.log (2411 / 25600) ≤ (1181275377 / 500000000) := by
  have h := checkLog_sound (w := (789 / 5611)) (n := 12)
    (lo := (28310921 / 100000000)) (hi := (283109211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2411) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2411) = 1/(2411 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1181275377 / 500000000) (-9450203 / 4000000) (Real.log (2411 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (84219421 / 125000000) ≤ -Real.log (100000 / 196159) ∧
    -Real.log (100000 / 196159) ≤ (673755369 / 1000000000) := by
  have h := checkLog_sound (w := (96159 / 296159)) (n := 12)
    (lo := (84219421 / 125000000)) (hi := (673755369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196159 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196159 / 100000) = 1/(100000 / 196159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (84219421 / 125000000) (673755369 / 1000000000) (Real.log (196159 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (196159 / 100000) = -Real.log (100000 / 196159) := by
    rw [show ((196159 / 100000) : ℝ) = ((100000 / 196159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1629718717 / 500000000) ≤ -Real.log (3841 / 100000) ∧
    -Real.log (3841 / 100000) ≤ (3259437439 / 1000000000) := by
  have h := checkLog_sound (w := (2409 / 10091)) (n := 12)
    (lo := (243424357 / 500000000)) (hi := (97369743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3841) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3841) = 1/(3841 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3259437439 / 1000000000) (-1629718717 / 500000000) (Real.log (3841 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84237581 / 125000000) ≤ -Real.log (1600 / 3139) ∧
    -Real.log (1600 / 3139) ≤ (673900649 / 1000000000) := by
  have h := checkLog_sound (w := (1539 / 4739)) (n := 12)
    (lo := (84237581 / 125000000)) (hi := (673900649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3139 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3139 / 1600) = 1/(1600 / 3139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84237581 / 125000000) (673900649 / 1000000000) (Real.log (3139 / 1600)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3139 / 1600) = -Real.log (1600 / 3139) := by
    rw [show ((3139 / 1600) : ℝ) = ((1600 / 3139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3266885041 / 1000000000) ≤ -Real.log (61 / 1600) ∧
    -Real.log (61 / 1600) ≤ (1633442523 / 500000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 61) = 1/(61 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1633442523 / 500000000) (-3266885041 / 1000000000) (Real.log (61 / 1600)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (673541743 / 1000000000) ≤ -Real.log (1000000 / 1961171) ∧
    -Real.log (1000000 / 1961171) ≤ (42096359 / 62500000) := by
  have h := checkLog_sound (w := (961171 / 2961171)) (n := 12)
    (lo := (673541743 / 1000000000)) (hi := (42096359 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961171 / 1000000) = 1/(1000000 / 1961171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (673541743 / 1000000000) (42096359 / 62500000) (Real.log (1961171 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1961171 / 1000000) = -Real.log (1000000 / 1961171) := by
    rw [show ((1961171 / 1000000) : ℝ) = ((1000000 / 1961171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1624293943 / 500000000) ≤ -Real.log (38829 / 1000000) ∧
    -Real.log (38829 / 1000000) ≤ (3248587891 / 1000000000) := by
  have h := checkLog_sound (w := (23671 / 101329)) (n := 12)
    (lo := (237999583 / 500000000)) (hi := (475999167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38829) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 38829) = 1/(38829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3248587891 / 1000000000) (-1624293943 / 500000000) (Real.log (38829 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (673690623 / 1000000000) ≤ -Real.log (1000000 / 1961463) ∧
    -Real.log (1000000 / 1961463) ≤ (1315802 / 1953125) := by
  have h := checkLog_sound (w := (961463 / 2961463)) (n := 12)
    (lo := (673690623 / 1000000000)) (hi := (1315802 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961463 / 1000000) = 1/(1000000 / 1961463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (673690623 / 1000000000) (1315802 / 1953125) (Real.log (1961463 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1961463 / 1000000) = -Real.log (1000000 / 1961463) := by
    rw [show ((1961463 / 1000000) : ℝ) = ((1000000 / 1961463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3256136457 / 1000000000) ≤ -Real.log (38537 / 1000000) ∧
    -Real.log (38537 / 1000000) ≤ (1628068231 / 500000000) := by
  have h := checkLog_sound (w := (23963 / 101037)) (n := 12)
    (lo := (483547737 / 1000000000)) (hi := (241773869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38537) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 38537) = 1/(38537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1628068231 / 500000000) (-3256136457 / 1000000000) (Real.log (38537 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1966596401 / 500000000) ≤ -Real.log (250000000000 / 12767443374121) ∧
    -Real.log (250000000000 / 12767443374121) ≤ (491649101 / 125000000) := by
  have h := checkLog_sound (w := (4767443374121 / 20767443374121)) (n := 12)
    (lo := (233728451 / 500000000)) (hi := (467456903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12767443374121 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12767443374121 / 8000000000000) = 1/(250000000000 / 12767443374121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1966596401 / 500000000) (491649101 / 125000000) (Real.log (12767443374121 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12767443374121 / 250000000000) = -Real.log (250000000000 / 12767443374121) := by
    rw [show ((12767443374121 / 250000000000) : ℝ) = ((250000000000 / 12767443374121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3940785689 / 1000000000) ≤ -Real.log (250000000000 / 12864754098361) ∧
    -Real.log (250000000000 / 12864754098361) ≤ (788157139 / 200000000) := by
  have h := checkLog_sound (w := (4864754098361 / 20864754098361)) (n := 12)
    (lo := (475049789 / 1000000000)) (hi := (47504979 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12864754098361 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12864754098361 / 8000000000000) = 1/(250000000000 / 12864754098361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3940785689 / 1000000000) (788157139 / 200000000) (Real.log (12864754098361 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12864754098361 / 250000000000) = -Real.log (250000000000 / 12864754098361) := by
    rw [show ((12864754098361 / 250000000000) : ℝ) = ((250000000000 / 12864754098361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3922129629 / 1000000000) ≤ -Real.log (100000000000 / 5050789358469) ∧
    -Real.log (100000000000 / 5050789358469) ≤ (784425927 / 200000000) := by
  have h := checkLog_sound (w := (1850789358469 / 8250789358469)) (n := 12)
    (lo := (456393729 / 1000000000)) (hi := (45639373 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5050789358469 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5050789358469 / 3200000000000) = 1/(100000000000 / 5050789358469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3922129629 / 1000000000) (784425927 / 200000000) (Real.log (5050789358469 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5050789358469 / 100000000000) = -Real.log (100000000000 / 5050789358469) := by
    rw [show ((5050789358469 / 100000000000) : ℝ) = ((100000000000 / 5050789358469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (98245677 / 25000000) ≤ -Real.log (500000000000 / 25449087889561) ∧
    -Real.log (500000000000 / 25449087889561) ≤ (1964913543 / 500000000) := by
  have h := checkLog_sound (w := (9449087889561 / 41449087889561)) (n := 12)
    (lo := (23204559 / 50000000)) (hi := (464091181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25449087889561 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25449087889561 / 16000000000000) = 1/(500000000000 / 25449087889561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (98245677 / 25000000) (1964913543 / 500000000) (Real.log (25449087889561 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (25449087889561 / 500000000000) = -Real.log (500000000000 / 25449087889561) := by
    rw [show ((25449087889561 / 500000000000) : ℝ) = ((500000000000 / 25449087889561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0110

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0111Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0111
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

theorem reflection_log_1_neg : (669320647 / 1000000000) ≤ -Real.log (51200 / 99989) ∧
    -Real.log (51200 / 99989) ≤ (83665081 / 125000000) := by
  have h := checkLog_sound (w := (48789 / 151189)) (n := 12)
    (lo := (669320647 / 1000000000)) (hi := (83665081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99989 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99989 / 51200) = 1/(51200 / 99989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (669320647 / 1000000000) (83665081 / 125000000) (Real.log (99989 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (99989 / 51200) = -Real.log (51200 / 99989) := by
    rw [show ((99989 / 51200) : ℝ) = ((51200 / 99989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (305569793 / 100000000) ≤ -Real.log (2411 / 51200) ∧
    -Real.log (2411 / 51200) ≤ (611139587 / 200000000) := by
  have h := checkLog_sound (w := (789 / 5611)) (n := 12)
    (lo := (28310921 / 100000000)) (hi := (283109211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2411) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2411) = 1/(2411 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-611139587 / 200000000) (-305569793 / 100000000) (Real.log (2411 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (41820663 / 62500000) ≤ -Real.log (5120 / 9997) ∧
    -Real.log (5120 / 9997) ≤ (669130609 / 1000000000) := by
  have h := checkLog_sound (w := (4877 / 15117)) (n := 12)
    (lo := (41820663 / 62500000)) (hi := (669130609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9997 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9997 / 5120) = 1/(5120 / 9997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (41820663 / 62500000) (669130609 / 1000000000) (Real.log (9997 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (9997 / 5120) = -Real.log (5120 / 9997) := by
    rw [show ((9997 / 5120) : ℝ) = ((5120 / 9997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (190490517 / 62500000) ≤ -Real.log (243 / 5120) ∧
    -Real.log (243 / 5120) ≤ (3047848277 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 243) = 1/(243 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3047848277 / 1000000000) (-190490517 / 62500000) (Real.log (243 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (322456263 / 500000000) ≤ -Real.log (25600 / 48789) ∧
    -Real.log (25600 / 48789) ≤ (644912527 / 1000000000) := by
  have h := checkLog_sound (w := (23189 / 74389)) (n := 12)
    (lo := (322456263 / 500000000)) (hi := (644912527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48789 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48789 / 25600) = 1/(25600 / 48789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (322456263 / 500000000) (644912527 / 1000000000) (Real.log (48789 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48789 / 25600) = -Real.log (25600 / 48789) := by
    rw [show ((48789 / 25600) : ℝ) = ((25600 / 48789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9450203 / 4000000) ≤ -Real.log (2411 / 25600) ∧
    -Real.log (2411 / 25600) ≤ (1181275377 / 500000000) := by
  have h := checkLog_sound (w := (789 / 5611)) (n := 12)
    (lo := (28310921 / 100000000)) (hi := (283109211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2411) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2411) = 1/(2411 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1181275377 / 500000000) (-9450203 / 4000000) (Real.log (2411 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (322261509 / 500000000) ≤ -Real.log (2560 / 4877) ∧
    -Real.log (2560 / 4877) ≤ (644523019 / 1000000000) := by
  have h := checkLog_sound (w := (2317 / 7437)) (n := 12)
    (lo := (322261509 / 500000000)) (hi := (644523019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4877 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4877 / 2560) = 1/(2560 / 4877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (322261509 / 500000000) (644523019 / 1000000000) (Real.log (4877 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4877 / 2560) = -Real.log (2560 / 4877) := by
    rw [show ((4877 / 2560) : ℝ) = ((2560 / 4877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (588675273 / 250000000) ≤ -Real.log (243 / 2560) ∧
    -Real.log (243 / 2560) ≤ (294337637 / 125000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 243) = 1/(243 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-294337637 / 125000000) (-588675273 / 250000000) (Real.log (243 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (673610577 / 1000000000) ≤ -Real.log (500000 / 980653) ∧
    -Real.log (500000 / 980653) ≤ (336805289 / 500000000) := by
  have h := checkLog_sound (w := (480653 / 1480653)) (n := 12)
    (lo := (673610577 / 1000000000)) (hi := (336805289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980653 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980653 / 500000) = 1/(500000 / 980653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (673610577 / 1000000000) (336805289 / 500000000) (Real.log (980653 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (980653 / 500000) = -Real.log (500000 / 980653) := by
    rw [show ((980653 / 500000) : ℝ) = ((500000 / 980653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3252070727 / 1000000000) ≤ -Real.log (19347 / 500000) ∧
    -Real.log (19347 / 500000) ≤ (813017683 / 250000000) := by
  have h := checkLog_sound (w := (11903 / 50597)) (n := 12)
    (lo := (479482007 / 1000000000)) (hi := (59935251 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19347) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19347) = 1/(19347 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-813017683 / 250000000) (-3252070727 / 1000000000) (Real.log (19347 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (336877939 / 500000000) ≤ -Real.log (1000000 / 1961591) ∧
    -Real.log (1000000 / 1961591) ≤ (673755879 / 1000000000) := by
  have h := checkLog_sound (w := (961591 / 2961591)) (n := 12)
    (lo := (336877939 / 500000000)) (hi := (673755879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961591 / 1000000) = 1/(1000000 / 1961591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (336877939 / 500000000) (673755879 / 1000000000) (Real.log (1961591 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1961591 / 1000000) = -Real.log (1000000 / 1961591) := by
    rw [show ((1961591 / 1000000) : ℝ) = ((1000000 / 1961591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3259463469 / 1000000000) ≤ -Real.log (38409 / 1000000) ∧
    -Real.log (38409 / 1000000) ≤ (1629731737 / 500000000) := by
  have h := checkLog_sound (w := (24091 / 100909)) (n := 12)
    (lo := (486874749 / 1000000000)) (hi := (1947499 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38409) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 38409) = 1/(38409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1629731737 / 500000000) (-3259463469 / 1000000000) (Real.log (38409 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (84174169 / 125000000) ≤ -Real.log (12500 / 24511) ∧
    -Real.log (12500 / 24511) ≤ (673393353 / 1000000000) := by
  have h := checkLog_sound (w := (12011 / 37011)) (n := 12)
    (lo := (84174169 / 125000000)) (hi := (673393353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24511 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24511 / 12500) = 1/(12500 / 24511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (84174169 / 125000000) (673393353 / 1000000000) (Real.log (24511 / 12500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (24511 / 12500) = -Real.log (12500 / 24511) := by
    rw [show ((24511 / 12500) : ℝ) = ((12500 / 24511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3241121431 / 1000000000) ≤ -Real.log (489 / 12500) ∧
    -Real.log (489 / 12500) ≤ (810280359 / 250000000) := by
  have h := checkLog_sound (w := (1169 / 5081)) (n := 12)
    (lo := (468532711 / 1000000000)) (hi := (58566589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1956) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1956) = 1/(489 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-810280359 / 250000000) (-3241121431 / 1000000000) (Real.log (489 / 12500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (673542253 / 1000000000) ≤ -Real.log (250000 / 490293) ∧
    -Real.log (250000 / 490293) ≤ (336771127 / 500000000) := by
  have h := checkLog_sound (w := (240293 / 740293)) (n := 12)
    (lo := (673542253 / 1000000000)) (hi := (336771127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490293 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490293 / 250000) = 1/(250000 / 490293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (673542253 / 1000000000) (336771127 / 500000000) (Real.log (490293 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (490293 / 250000) = -Real.log (250000 / 490293) := by
    rw [show ((490293 / 250000) : ℝ) = ((250000 / 490293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (81215341 / 25000000) ≤ -Real.log (9707 / 250000) ∧
    -Real.log (9707 / 250000) ≤ (649722729 / 200000000) := by
  have h := checkLog_sound (w := (2959 / 12666)) (n := 12)
    (lo := (11900623 / 25000000)) (hi := (476024921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9707) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 9707) = 1/(9707 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-649722729 / 200000000) (-81215341 / 25000000) (Real.log (9707 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (490710163 / 125000000) ≤ -Real.log (250000000000 / 12671900036181) ∧
    -Real.log (250000000000 / 12671900036181) ≤ (392568131 / 100000000) := by
  have h := checkLog_sound (w := (4671900036181 / 20671900036181)) (n := 12)
    (lo := (114986351 / 250000000)) (hi := (91989081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12671900036181 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12671900036181 / 8000000000000) = 1/(250000000000 / 12671900036181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (490710163 / 125000000) (392568131 / 100000000) (Real.log (12671900036181 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12671900036181 / 250000000000) = -Real.log (250000000000 / 12671900036181) := by
    rw [show ((12671900036181 / 250000000000) : ℝ) = ((250000000000 / 12671900036181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3933219347 / 1000000000) ≤ -Real.log (250000000000 / 12767782290609) ∧
    -Real.log (250000000000 / 12767782290609) ≤ (3933219353 / 1000000000) := by
  have h := checkLog_sound (w := (4767782290609 / 20767782290609)) (n := 12)
    (lo := (467483447 / 1000000000)) (hi := (58435431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12767782290609 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12767782290609 / 8000000000000) = 1/(250000000000 / 12767782290609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3933219347 / 1000000000) (3933219353 / 1000000000) (Real.log (12767782290609 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12767782290609 / 250000000000) = -Real.log (250000000000 / 12767782290609) := by
    rw [show ((12767782290609 / 250000000000) : ℝ) = ((250000000000 / 12767782290609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3914514783 / 1000000000) ≤ -Real.log (500000000000 / 25062372188139) ∧
    -Real.log (500000000000 / 25062372188139) ≤ (3914514789 / 1000000000) := by
  have h := checkLog_sound (w := (9062372188139 / 41062372188139)) (n := 12)
    (lo := (448778883 / 1000000000)) (hi := (112194721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25062372188139 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25062372188139 / 16000000000000) = 1/(500000000000 / 25062372188139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3914514783 / 1000000000) (3914514789 / 1000000000) (Real.log (25062372188139 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (25062372188139 / 500000000000) = -Real.log (500000000000 / 25062372188139) := by
    rw [show ((25062372188139 / 500000000000) : ℝ) = ((500000000000 / 25062372188139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1961077947 / 500000000) ≤ -Real.log (125000000000 / 6313652518801) ∧
    -Real.log (125000000000 / 6313652518801) ≤ (39221559 / 10000000) := by
  have h := checkLog_sound (w := (2313652518801 / 10313652518801)) (n := 12)
    (lo := (228209997 / 500000000)) (hi := (91283999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6313652518801 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6313652518801 / 4000000000000) = 1/(125000000000 / 6313652518801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1961077947 / 500000000) (39221559 / 10000000) (Real.log (6313652518801 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6313652518801 / 125000000000) = -Real.log (125000000000 / 6313652518801) := by
    rw [show ((6313652518801 / 125000000000) : ℝ) = ((125000000000 / 6313652518801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0111

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0112Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0112
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

theorem reflection_log_1_neg : (41820663 / 62500000) ≤ -Real.log (5120 / 9997) ∧
    -Real.log (5120 / 9997) ≤ (669130609 / 1000000000) := by
  have h := checkLog_sound (w := (4877 / 15117)) (n := 12)
    (lo := (41820663 / 62500000)) (hi := (669130609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9997 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9997 / 5120) = 1/(5120 / 9997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (41820663 / 62500000) (669130609 / 1000000000) (Real.log (9997 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (9997 / 5120) = -Real.log (5120 / 9997) := by
    rw [show ((9997 / 5120) : ℝ) = ((5120 / 9997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (190490517 / 62500000) ≤ -Real.log (243 / 5120) ∧
    -Real.log (243 / 5120) ≤ (3047848277 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 243) = 1/(243 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3047848277 / 1000000000) (-190490517 / 62500000) (Real.log (243 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (334375211 / 500000000) ≤ -Real.log (12800 / 24983) ∧
    -Real.log (12800 / 24983) ≤ (668750423 / 1000000000) := by
  have h := checkLog_sound (w := (12183 / 37783)) (n := 12)
    (lo := (334375211 / 500000000)) (hi := (668750423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24983 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24983 / 12800) = 1/(12800 / 24983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (334375211 / 500000000) (668750423 / 1000000000) (Real.log (24983 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24983 / 12800) = -Real.log (12800 / 24983) := by
    rw [show ((24983 / 12800) : ℝ) = ((12800 / 24983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3032331423 / 1000000000) ≤ -Real.log (617 / 12800) ∧
    -Real.log (617 / 12800) ≤ (758082857 / 250000000) := by
  have h := checkLog_sound (w := (183 / 1417)) (n := 12)
    (lo := (259742703 / 1000000000)) (hi := (16233919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 617) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 617) = 1/(617 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-758082857 / 250000000) (-3032331423 / 1000000000) (Real.log (617 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (322261509 / 500000000) ≤ -Real.log (2560 / 4877) ∧
    -Real.log (2560 / 4877) ≤ (644523019 / 1000000000) := by
  have h := checkLog_sound (w := (2317 / 7437)) (n := 12)
    (lo := (322261509 / 500000000)) (hi := (644523019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4877 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4877 / 2560) = 1/(2560 / 4877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (322261509 / 500000000) (644523019 / 1000000000) (Real.log (4877 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4877 / 2560) = -Real.log (2560 / 4877) := by
    rw [show ((4877 / 2560) : ℝ) = ((2560 / 4877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (588675273 / 250000000) ≤ -Real.log (243 / 2560) ∧
    -Real.log (243 / 2560) ≤ (294337637 / 125000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 243) = 1/(243 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-294337637 / 125000000) (-588675273 / 250000000) (Real.log (243 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (643743547 / 1000000000) ≤ -Real.log (6400 / 12183) ∧
    -Real.log (6400 / 12183) ≤ (160935887 / 250000000) := by
  have h := checkLog_sound (w := (5783 / 18583)) (n := 12)
    (lo := (643743547 / 1000000000)) (hi := (160935887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12183 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12183 / 6400) = 1/(6400 / 12183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (643743547 / 1000000000) (160935887 / 250000000) (Real.log (12183 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12183 / 6400) = -Real.log (6400 / 12183) := by
    rw [show ((12183 / 6400) : ℝ) = ((6400 / 12183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2339184243 / 1000000000) ≤ -Real.log (617 / 6400) ∧
    -Real.log (617 / 6400) ≤ (2339184247 / 1000000000) := by
  have h := checkLog_sound (w := (183 / 1417)) (n := 12)
    (lo := (259742703 / 1000000000)) (hi := (16233919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 617) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 617) = 1/(617 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2339184247 / 1000000000) (-2339184243 / 1000000000) (Real.log (617 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (673321953 / 1000000000) ≤ -Real.log (50000 / 98037) ∧
    -Real.log (50000 / 98037) ≤ (336660977 / 500000000) := by
  have h := checkLog_sound (w := (48037 / 148037)) (n := 12)
    (lo := (673321953 / 1000000000)) (hi := (336660977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98037 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98037 / 50000) = 1/(50000 / 98037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (673321953 / 1000000000) (336660977 / 500000000) (Real.log (98037 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (98037 / 50000) = -Real.log (50000 / 98037) := by
    rw [show ((98037 / 50000) : ℝ) = ((50000 / 98037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3237549087 / 1000000000) ≤ -Real.log (1963 / 50000) ∧
    -Real.log (1963 / 50000) ≤ (809387273 / 250000000) := by
  have h := checkLog_sound (w := (581 / 2544)) (n := 12)
    (lo := (464960367 / 1000000000)) (hi := (29060023 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1963) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1963) = 1/(1963 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-809387273 / 250000000) (-3237549087 / 1000000000) (Real.log (1963 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (673611087 / 1000000000) ≤ -Real.log (1000000 / 1961307) ∧
    -Real.log (1000000 / 1961307) ≤ (42100693 / 62500000) := by
  have h := checkLog_sound (w := (961307 / 2961307)) (n := 12)
    (lo := (673611087 / 1000000000)) (hi := (42100693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961307 / 1000000) = 1/(1000000 / 1961307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (673611087 / 1000000000) (42100693 / 62500000) (Real.log (1961307 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1961307 / 1000000) = -Real.log (1000000 / 1961307) := by
    rw [show ((1961307 / 1000000) : ℝ) = ((1000000 / 1961307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3252096571 / 1000000000) ≤ -Real.log (38693 / 1000000) ∧
    -Real.log (38693 / 1000000) ≤ (50814009 / 15625000) := by
  have h := checkLog_sound (w := (23807 / 101193)) (n := 12)
    (lo := (479507851 / 1000000000)) (hi := (119876963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38693) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 38693) = 1/(38693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-50814009 / 15625000) (-3252096571 / 1000000000) (Real.log (38693 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (336548251 / 500000000) ≤ -Real.log (500000 / 980149) ∧
    -Real.log (500000 / 980149) ≤ (673096503 / 1000000000) := by
  have h := checkLog_sound (w := (480149 / 1480149)) (n := 12)
    (lo := (336548251 / 500000000)) (hi := (673096503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980149 / 500000) = 1/(500000 / 980149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (336548251 / 500000000) (673096503 / 1000000000) (Real.log (980149 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (980149 / 500000) = -Real.log (500000 / 980149) := by
    rw [show ((980149 / 500000) : ℝ) = ((500000 / 980149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (201647107 / 62500000) ≤ -Real.log (19851 / 500000) ∧
    -Real.log (19851 / 500000) ≤ (3226353717 / 1000000000) := by
  have h := checkLog_sound (w := (11399 / 51101)) (n := 12)
    (lo := (3545039 / 7812500)) (hi := (453764993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19851) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19851) = 1/(19851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3226353717 / 1000000000) (-201647107 / 62500000) (Real.log (19851 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (336696931 / 500000000) ≤ -Real.log (1000000 / 1960881) ∧
    -Real.log (1000000 / 1960881) ≤ (673393863 / 1000000000) := by
  have h := checkLog_sound (w := (960881 / 2960881)) (n := 12)
    (lo := (336696931 / 500000000)) (hi := (673393863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960881 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1960881 / 1000000) = 1/(1000000 / 1960881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (336696931 / 500000000) (673393863 / 1000000000) (Real.log (1960881 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1960881 / 1000000) = -Real.log (1000000 / 1960881) := by
    rw [show ((1960881 / 1000000) : ℝ) = ((1000000 / 1960881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1620573497 / 500000000) ≤ -Real.log (39119 / 1000000) ∧
    -Real.log (39119 / 1000000) ≤ (3241146999 / 1000000000) := by
  have h := checkLog_sound (w := (23381 / 101619)) (n := 12)
    (lo := (234279137 / 500000000)) (hi := (18742331 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39119) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 39119) = 1/(39119 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3241146999 / 1000000000) (-1620573497 / 500000000) (Real.log (39119 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1527684 / 390625) ≤ -Real.log (500000000000 / 24971217524197) ∧
    -Real.log (500000000000 / 24971217524197) ≤ (1955435523 / 500000000) := by
  have h := checkLog_sound (w := (8971217524197 / 40971217524197)) (n := 12)
    (lo := (22256757 / 50000000)) (hi := (445135141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24971217524197 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24971217524197 / 16000000000000) = 1/(500000000000 / 24971217524197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1527684 / 390625) (1955435523 / 500000000) (Real.log (24971217524197 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (24971217524197 / 500000000000) = -Real.log (500000000000 / 24971217524197) := by
    rw [show ((24971217524197 / 500000000000) : ℝ) = ((500000000000 / 24971217524197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1962853829 / 500000000) ≤ -Real.log (500000000000 / 25344467991627) ∧
    -Real.log (500000000000 / 25344467991627) ≤ (245356729 / 62500000) := by
  have h := checkLog_sound (w := (9344467991627 / 41344467991627)) (n := 12)
    (lo := (229985879 / 500000000)) (hi := (459971759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25344467991627 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25344467991627 / 16000000000000) = 1/(500000000000 / 25344467991627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1962853829 / 500000000) (245356729 / 62500000) (Real.log (25344467991627 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25344467991627 / 500000000000) = -Real.log (500000000000 / 25344467991627) := by
    rw [show ((25344467991627 / 500000000000) : ℝ) = ((500000000000 / 25344467991627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1949725107 / 500000000) ≤ -Real.log (500000000000 / 24687647977431) ∧
    -Real.log (500000000000 / 24687647977431) ≤ (194972511 / 50000000) := by
  have h := checkLog_sound (w := (8687647977431 / 40687647977431)) (n := 12)
    (lo := (216857157 / 500000000)) (hi := (86742863 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24687647977431 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24687647977431 / 16000000000000) = 1/(500000000000 / 24687647977431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1949725107 / 500000000) (194972511 / 50000000) (Real.log (24687647977431 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (24687647977431 / 500000000000) = -Real.log (500000000000 / 24687647977431) := by
    rw [show ((24687647977431 / 500000000000) : ℝ) = ((500000000000 / 24687647977431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (782908171 / 200000000) ≤ -Real.log (100000000000 / 5012605127943) ∧
    -Real.log (100000000000 / 5012605127943) ≤ (3914540861 / 1000000000) := by
  have h := checkLog_sound (w := (1812605127943 / 8212605127943)) (n := 12)
    (lo := (89760991 / 200000000)) (hi := (112201239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5012605127943 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5012605127943 / 3200000000000) = 1/(100000000000 / 5012605127943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (782908171 / 200000000) (3914540861 / 1000000000) (Real.log (5012605127943 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5012605127943 / 100000000000) = -Real.log (100000000000 / 5012605127943) := by
    rw [show ((5012605127943 / 100000000000) : ℝ) = ((100000000000 / 5012605127943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0112

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0113Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0113
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

theorem reflection_log_1_neg : (334375211 / 500000000) ≤ -Real.log (12800 / 24983) ∧
    -Real.log (12800 / 24983) ≤ (668750423 / 1000000000) := by
  have h := checkLog_sound (w := (12183 / 37783)) (n := 12)
    (lo := (334375211 / 500000000)) (hi := (668750423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24983 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24983 / 12800) = 1/(12800 / 24983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (334375211 / 500000000) (668750423 / 1000000000) (Real.log (24983 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24983 / 12800) = -Real.log (12800 / 24983) := by
    rw [show ((24983 / 12800) : ℝ) = ((12800 / 24983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3032331423 / 1000000000) ≤ -Real.log (617 / 12800) ∧
    -Real.log (617 / 12800) ≤ (758082857 / 250000000) := by
  have h := checkLog_sound (w := (183 / 1417)) (n := 12)
    (lo := (259742703 / 1000000000)) (hi := (16233919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 617) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 617) = 1/(617 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-758082857 / 250000000) (-3032331423 / 1000000000) (Real.log (617 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (668370091 / 1000000000) ≤ -Real.log (25600 / 49947) ∧
    -Real.log (25600 / 49947) ≤ (167092523 / 250000000) := by
  have h := checkLog_sound (w := (24347 / 75547)) (n := 12)
    (lo := (668370091 / 1000000000)) (hi := (167092523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49947 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49947 / 25600) = 1/(25600 / 49947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (668370091 / 1000000000) (167092523 / 250000000) (Real.log (49947 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49947 / 25600) = -Real.log (25600 / 49947) := by
    rw [show ((49947 / 25600) : ℝ) = ((25600 / 49947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3017051673 / 1000000000) ≤ -Real.log (1253 / 25600) ∧
    -Real.log (1253 / 25600) ≤ (1508525839 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2853)) (n := 12)
    (lo := (244462953 / 1000000000)) (hi := (122231477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1253) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1253) = 1/(1253 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1508525839 / 500000000) (-3017051673 / 1000000000) (Real.log (1253 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (643743547 / 1000000000) ≤ -Real.log (6400 / 12183) ∧
    -Real.log (6400 / 12183) ≤ (160935887 / 250000000) := by
  have h := checkLog_sound (w := (5783 / 18583)) (n := 12)
    (lo := (643743547 / 1000000000)) (hi := (160935887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12183 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12183 / 6400) = 1/(6400 / 12183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (643743547 / 1000000000) (160935887 / 250000000) (Real.log (12183 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12183 / 6400) = -Real.log (6400 / 12183) := by
    rw [show ((12183 / 6400) : ℝ) = ((6400 / 12183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2339184243 / 1000000000) ≤ -Real.log (617 / 6400) ∧
    -Real.log (617 / 6400) ≤ (2339184247 / 1000000000) := by
  have h := checkLog_sound (w := (183 / 1417)) (n := 12)
    (lo := (259742703 / 1000000000)) (hi := (16233919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 617) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 617) = 1/(617 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2339184247 / 1000000000) (-2339184243 / 1000000000) (Real.log (617 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (642963467 / 1000000000) ≤ -Real.log (12800 / 24347) ∧
    -Real.log (12800 / 24347) ≤ (160740867 / 250000000) := by
  have h := checkLog_sound (w := (11547 / 37147)) (n := 12)
    (lo := (642963467 / 1000000000)) (hi := (160740867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24347 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24347 / 12800) = 1/(12800 / 24347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (642963467 / 1000000000) (160740867 / 250000000) (Real.log (24347 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24347 / 12800) = -Real.log (12800 / 24347) := by
    rw [show ((24347 / 12800) : ℝ) = ((12800 / 24347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2323904493 / 1000000000) ≤ -Real.log (1253 / 12800) ∧
    -Real.log (1253 / 12800) ≤ (2323904497 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2853)) (n := 12)
    (lo := (244462953 / 1000000000)) (hi := (122231477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1253) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1253) = 1/(1253 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2323904497 / 1000000000) (-2323904493 / 1000000000) (Real.log (1253 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168258311 / 250000000) ≤ -Real.log (500000 / 980087) ∧
    -Real.log (500000 / 980087) ≤ (134606649 / 200000000) := by
  have h := checkLog_sound (w := (480087 / 1480087)) (n := 12)
    (lo := (168258311 / 250000000)) (hi := (134606649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980087 / 500000) = 1/(500000 / 980087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168258311 / 250000000) (134606649 / 200000000) (Real.log (980087 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (980087 / 500000) = -Real.log (500000 / 980087) := by
    rw [show ((980087 / 500000) : ℝ) = ((500000 / 980087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3223235311 / 1000000000) ≤ -Real.log (19913 / 500000) ∧
    -Real.log (19913 / 500000) ≤ (805808829 / 250000000) := by
  have h := checkLog_sound (w := (11337 / 51163)) (n := 12)
    (lo := (450646591 / 1000000000)) (hi := (7041353 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19913) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19913) = 1/(19913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-805808829 / 250000000) (-3223235311 / 1000000000) (Real.log (19913 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (673322463 / 1000000000) ≤ -Real.log (1000000 / 1960741) ∧
    -Real.log (1000000 / 1960741) ≤ (21041327 / 31250000) := by
  have h := checkLog_sound (w := (960741 / 2960741)) (n := 12)
    (lo := (673322463 / 1000000000)) (hi := (21041327 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1960741 / 1000000) = 1/(1000000 / 1960741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (673322463 / 1000000000) (21041327 / 31250000) (Real.log (1960741 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1960741 / 1000000) = -Real.log (1000000 / 1960741) := by
    rw [show ((1960741 / 1000000) : ℝ) = ((1000000 / 1960741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3237574559 / 1000000000) ≤ -Real.log (39259 / 1000000) ∧
    -Real.log (39259 / 1000000) ≤ (809393641 / 250000000) := by
  have h := checkLog_sound (w := (23241 / 101759)) (n := 12)
    (lo := (464985839 / 1000000000)) (hi := (5812323 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39259) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 39259) = 1/(39259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-809393641 / 250000000) (-3237574559 / 1000000000) (Real.log (39259 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26912003 / 40000000) ≤ -Real.log (1000000 / 1959717) ∧
    -Real.log (1000000 / 1959717) ≤ (168200019 / 250000000) := by
  have h := checkLog_sound (w := (959717 / 2959717)) (n := 12)
    (lo := (26912003 / 40000000)) (hi := (168200019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959717 / 1000000) = 1/(1000000 / 1959717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26912003 / 40000000) (168200019 / 250000000) (Real.log (1959717 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1959717 / 1000000) = -Real.log (1000000 / 1959717) := by
    rw [show ((1959717 / 1000000) : ℝ) = ((1000000 / 1959717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3211825733 / 1000000000) ≤ -Real.log (40283 / 1000000) ∧
    -Real.log (40283 / 1000000) ≤ (1605912869 / 500000000) := by
  have h := checkLog_sound (w := (22217 / 102783)) (n := 12)
    (lo := (439237013 / 1000000000)) (hi := (219618507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40283) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 40283) = 1/(40283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1605912869 / 500000000) (-3211825733 / 1000000000) (Real.log (40283 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (168274253 / 250000000) ≤ -Real.log (1000000 / 1960299) ∧
    -Real.log (1000000 / 1960299) ≤ (673097013 / 1000000000) := by
  have h := checkLog_sound (w := (960299 / 2960299)) (n := 12)
    (lo := (168274253 / 250000000)) (hi := (673097013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1960299 / 1000000) = 1/(1000000 / 1960299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (168274253 / 250000000) (673097013 / 1000000000) (Real.log (1960299 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1960299 / 1000000) = -Real.log (1000000 / 1960299) := by
    rw [show ((1960299 / 1000000) : ℝ) = ((1000000 / 1960299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (32263789 / 10000000) ≤ -Real.log (39701 / 1000000) ∧
    -Real.log (39701 / 1000000) ≤ (645275781 / 200000000) := by
  have h := checkLog_sound (w := (22799 / 102201)) (n := 12)
    (lo := (22689509 / 50000000)) (hi := (453790181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39701) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 39701) = 1/(39701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-645275781 / 200000000) (-32263789 / 10000000) (Real.log (39701 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (779253711 / 200000000) ≤ -Real.log (15625000000 / 769038285291) ∧
    -Real.log (15625000000 / 769038285291) ≤ (3896268561 / 1000000000) := by
  have h := checkLog_sound (w := (269038285291 / 1269038285291)) (n := 12)
    (lo := (86106531 / 200000000)) (hi := (26908291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769038285291 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(769038285291 / 500000000000) = 1/(15625000000 / 769038285291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (779253711 / 200000000) (3896268561 / 1000000000) (Real.log (769038285291 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (769038285291 / 15625000000) = -Real.log (15625000000 / 769038285291) := by
    rw [show ((769038285291 / 15625000000) : ℝ) = ((15625000000 / 769038285291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3910897021 / 1000000000) ≤ -Real.log (250000000000 / 12485933161823) ∧
    -Real.log (250000000000 / 12485933161823) ≤ (3910897027 / 1000000000) := by
  have h := checkLog_sound (w := (4485933161823 / 20485933161823)) (n := 12)
    (lo := (445161121 / 1000000000)) (hi := (222580561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12485933161823 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12485933161823 / 8000000000000) = 1/(250000000000 / 12485933161823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3910897021 / 1000000000) (3910897027 / 1000000000) (Real.log (12485933161823 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12485933161823 / 250000000000) = -Real.log (250000000000 / 12485933161823) := by
    rw [show ((12485933161823 / 250000000000) : ℝ) = ((250000000000 / 12485933161823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3884625807 / 1000000000) ≤ -Real.log (100000000000 / 4864873519847) ∧
    -Real.log (100000000000 / 4864873519847) ≤ (3884625813 / 1000000000) := by
  have h := checkLog_sound (w := (1664873519847 / 8064873519847)) (n := 12)
    (lo := (418889907 / 1000000000)) (hi := (104722477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4864873519847 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4864873519847 / 3200000000000) = 1/(100000000000 / 4864873519847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3884625807 / 1000000000) (3884625813 / 1000000000) (Real.log (4864873519847 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4864873519847 / 100000000000) = -Real.log (100000000000 / 4864873519847) := by
    rw [show ((4864873519847 / 100000000000) : ℝ) = ((100000000000 / 4864873519847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (487434489 / 125000000) ≤ -Real.log (500000000000 / 24688282411023) ∧
    -Real.log (500000000000 / 24688282411023) ≤ (1949737959 / 500000000) := by
  have h := checkLog_sound (w := (8688282411023 / 40688282411023)) (n := 12)
    (lo := (108435003 / 250000000)) (hi := (433740013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24688282411023 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24688282411023 / 16000000000000) = 1/(500000000000 / 24688282411023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (487434489 / 125000000) (1949737959 / 500000000) (Real.log (24688282411023 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24688282411023 / 500000000000) = -Real.log (500000000000 / 24688282411023) := by
    rw [show ((24688282411023 / 500000000000) : ℝ) = ((500000000000 / 24688282411023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0113

end


