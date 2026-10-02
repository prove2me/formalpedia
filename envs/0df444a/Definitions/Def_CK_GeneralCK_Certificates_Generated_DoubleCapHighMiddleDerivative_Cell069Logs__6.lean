-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell069Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell069Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:53:50.259013+00:00
-- url     : https://prove2.me/theorems/e92431d0-56e9-4929-9591-70c7e1714004
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell069Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell070…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell069Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell070Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell071Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell072Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell073Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell074Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell069Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell070Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell071Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell072Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell073Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell074Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell069Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell070Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell071Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell072Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell073Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell074Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell069Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell070Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell071Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell072Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell073Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell074Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell069Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell069
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (127714607 / 500000000) ≤ -Real.log (512 / 661) ∧
    -Real.log (512 / 661) ≤ (51085843 / 200000000) := by
  have h := checkLog_sound (w := (149 / 1173)) (n := 12)
    (lo := (127714607 / 500000000)) (hi := (51085843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661 / 512) = 1/(512 / 661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (127714607 / 500000000) (51085843 / 200000000) (Real.log (661 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (661 / 512) = -Real.log (512 / 661) := by
    rw [show ((661 / 512) : ℝ) = ((512 / 661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (34392179 / 100000000) ≤ -Real.log (363 / 512) ∧
    -Real.log (363 / 512) ≤ (343921791 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 875)) (n := 12)
    (lo := (34392179 / 100000000)) (hi := (343921791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 363) = 1/(363 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-343921791 / 1000000000) (-34392179 / 100000000) (Real.log (363 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (254975253 / 1000000000) ≤ -Real.log (5120 / 6607) ∧
    -Real.log (5120 / 6607) ≤ (127487627 / 500000000) := by
  have h := checkLog_sound (w := (1487 / 11727)) (n := 12)
    (lo := (254975253 / 1000000000)) (hi := (127487627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6607 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6607 / 5120) = 1/(5120 / 6607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (254975253 / 1000000000) (127487627 / 500000000) (Real.log (6607 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6607 / 5120) = -Real.log (5120 / 6607) := by
    rw [show ((6607 / 5120) : ℝ) = ((5120 / 6607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (68619137 / 200000000) ≤ -Real.log (3633 / 5120) ∧
    -Real.log (3633 / 5120) ≤ (171547843 / 500000000) := by
  have h := checkLog_sound (w := (1487 / 8753)) (n := 12)
    (lo := (68619137 / 200000000)) (hi := (171547843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3633) = 1/(3633 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-171547843 / 500000000) (-68619137 / 200000000) (Real.log (3633 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (93700981 / 500000000) ≤ -Real.log (31250 / 37691) ∧
    -Real.log (31250 / 37691) ≤ (187401963 / 1000000000) := by
  have h := checkLog_sound (w := (6441 / 68941)) (n := 12)
    (lo := (93700981 / 500000000)) (hi := (187401963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37691 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37691 / 31250) = 1/(31250 / 37691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (93700981 / 500000000) (187401963 / 1000000000) (Real.log (37691 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37691 / 31250) = -Real.log (31250 / 37691) := by
    rw [show ((37691 / 31250) : ℝ) = ((31250 / 37691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (46162577 / 200000000) ≤ -Real.log (24809 / 31250) ∧
    -Real.log (24809 / 31250) ≤ (115406443 / 500000000) := by
  have h := checkLog_sound (w := (6441 / 56059)) (n := 12)
    (lo := (46162577 / 200000000)) (hi := (115406443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24809) = 1/(24809 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-115406443 / 500000000) (-46162577 / 200000000) (Real.log (24809 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (11734383 / 62500000) ≤ -Real.log (250000 / 301633) ∧
    -Real.log (250000 / 301633) ≤ (187750129 / 1000000000) := by
  have h := checkLog_sound (w := (51633 / 551633)) (n := 12)
    (lo := (11734383 / 62500000)) (hi := (187750129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301633 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301633 / 250000) = 1/(250000 / 301633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (11734383 / 62500000) (187750129 / 1000000000) (Real.log (301633 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (301633 / 250000) = -Real.log (250000 / 301633) := by
    rw [show ((301633 / 250000) : ℝ) = ((250000 / 301633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (231342067 / 1000000000) ≤ -Real.log (198367 / 250000) ∧
    -Real.log (198367 / 250000) ≤ (57835517 / 250000000) := by
  have h := checkLog_sound (w := (51633 / 448367)) (n := 12)
    (lo := (231342067 / 1000000000)) (hi := (57835517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198367) = 1/(198367 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-57835517 / 250000000) (-231342067 / 1000000000) (Real.log (198367 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137568233 / 1000000000) ≤ -Real.log (25000 / 28687) ∧
    -Real.log (25000 / 28687) ≤ (68784117 / 500000000) := by
  have h := checkLog_sound (w := (3687 / 53687)) (n := 12)
    (lo := (137568233 / 1000000000)) (hi := (68784117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28687 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28687 / 25000) = 1/(25000 / 28687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137568233 / 1000000000) (68784117 / 500000000) (Real.log (28687 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (28687 / 25000) = -Real.log (25000 / 28687) := by
    rw [show ((28687 / 25000) : ℝ) = ((25000 / 28687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (159558609 / 1000000000) ≤ -Real.log (21313 / 25000) ∧
    -Real.log (21313 / 25000) ≤ (15955861 / 100000000) := by
  have h := checkLog_sound (w := (3687 / 46313)) (n := 12)
    (lo := (159558609 / 1000000000)) (hi := (15955861 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21313) = 1/(21313 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-15955861 / 100000000) (-159558609 / 1000000000) (Real.log (21313 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (137836611 / 1000000000) ≤ -Real.log (250000 / 286947) ∧
    -Real.log (250000 / 286947) ≤ (34459153 / 250000000) := by
  have h := checkLog_sound (w := (36947 / 536947)) (n := 12)
    (lo := (137836611 / 1000000000)) (hi := (34459153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286947 / 250000) = 1/(250000 / 286947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (137836611 / 1000000000) (34459153 / 250000000) (Real.log (286947 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (286947 / 250000) = -Real.log (250000 / 286947) := by
    rw [show ((286947 / 250000) : ℝ) = ((250000 / 286947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (39979989 / 250000000) ≤ -Real.log (213053 / 250000) ∧
    -Real.log (213053 / 250000) ≤ (159919957 / 1000000000) := by
  have h := checkLog_sound (w := (36947 / 463053)) (n := 12)
    (lo := (39979989 / 250000000)) (hi := (159919957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 213053) = 1/(213053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-159919957 / 1000000000) (-39979989 / 250000000) (Real.log (213053 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (598070939 / 1000000000) ≤ -Real.log (100000000000 / 181860721167) ∧
    -Real.log (100000000000 / 181860721167) ≤ (29903547 / 50000000) := by
  have h := checkLog_sound (w := (81860721167 / 281860721167)) (n := 12)
    (lo := (598070939 / 1000000000)) (hi := (29903547 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181860721167 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181860721167 / 100000000000) = 1/(100000000000 / 181860721167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (598070939 / 1000000000) (29903547 / 50000000) (Real.log (181860721167 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (181860721167 / 100000000000) = -Real.log (100000000000 / 181860721167) := by
    rw [show ((181860721167 / 100000000000) : ℝ) = ((100000000000 / 181860721167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (119870201 / 200000000) ≤ -Real.log (12500000000 / 22761707989) ∧
    -Real.log (12500000000 / 22761707989) ≤ (299675503 / 500000000) := by
  have h := checkLog_sound (w := (10261707989 / 35261707989)) (n := 12)
    (lo := (119870201 / 200000000)) (hi := (299675503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22761707989 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22761707989 / 12500000000) = 1/(12500000000 / 22761707989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (119870201 / 200000000) (299675503 / 500000000) (Real.log (22761707989 / 12500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (22761707989 / 12500000000) = -Real.log (12500000000 / 22761707989) := by
    rw [show ((22761707989 / 12500000000) : ℝ) = ((12500000000 / 22761707989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (6534607 / 15625000) ≤ -Real.log (500000000000 / 759623523721) ∧
    -Real.log (500000000000 / 759623523721) ≤ (418214849 / 1000000000) := by
  have h := checkLog_sound (w := (259623523721 / 1259623523721)) (n := 12)
    (lo := (6534607 / 15625000)) (hi := (418214849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759623523721 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759623523721 / 500000000000) = 1/(500000000000 / 759623523721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6534607 / 15625000) (418214849 / 1000000000) (Real.log (759623523721 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (759623523721 / 500000000000) = -Real.log (500000000000 / 759623523721) := by
    rw [show ((759623523721 / 500000000000) : ℝ) = ((500000000000 / 759623523721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (104773049 / 250000000) ≤ -Real.log (100000000000 / 152058054011) ∧
    -Real.log (100000000000 / 152058054011) ≤ (419092197 / 1000000000) := by
  have h := checkLog_sound (w := (52058054011 / 252058054011)) (n := 12)
    (lo := (104773049 / 250000000)) (hi := (419092197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152058054011 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152058054011 / 100000000000) = 1/(100000000000 / 152058054011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (104773049 / 250000000) (419092197 / 1000000000) (Real.log (152058054011 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (152058054011 / 100000000000) = -Real.log (100000000000 / 152058054011) := by
    rw [show ((152058054011 / 100000000000) : ℝ) = ((100000000000 / 152058054011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (297126843 / 1000000000) ≤ -Real.log (500000000000 / 672993008961) ∧
    -Real.log (500000000000 / 672993008961) ≤ (74281711 / 250000000) := by
  have h := checkLog_sound (w := (172993008961 / 1172993008961)) (n := 12)
    (lo := (297126843 / 1000000000)) (hi := (74281711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672993008961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(672993008961 / 500000000000) = 1/(500000000000 / 672993008961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (297126843 / 1000000000) (74281711 / 250000000) (Real.log (672993008961 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (672993008961 / 500000000000) = -Real.log (500000000000 / 672993008961) := by
    rw [show ((672993008961 / 500000000000) : ℝ) = ((500000000000 / 672993008961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (37219571 / 125000000) ≤ -Real.log (250000000000 / 336708471601) ∧
    -Real.log (250000000000 / 336708471601) ≤ (297756569 / 1000000000) := by
  have h := checkLog_sound (w := (86708471601 / 586708471601)) (n := 12)
    (lo := (37219571 / 125000000)) (hi := (297756569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336708471601 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336708471601 / 250000000000) = 1/(250000000000 / 336708471601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (37219571 / 125000000) (297756569 / 1000000000) (Real.log (336708471601 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (336708471601 / 250000000000) = -Real.log (250000000000 / 336708471601) := by
    rw [show ((336708471601 / 250000000000) : ℝ) = ((250000000000 / 336708471601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1380209 / 62500000) ≤ -Real.log (61134919191 / 62500000000) ∧
    -Real.log (61134919191 / 62500000000) ≤ (4416669 / 200000000) := by
  have h := checkLog_sound (w := (1365080809 / 123634919191)) (n := 12)
    (lo := (1380209 / 62500000)) (hi := (4416669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61134919191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61134919191) = 1/(61134919191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4416669 / 200000000) (-1380209 / 62500000) (Real.log (61134919191 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2748797 / 125000000) ≤ -Real.log (611406031 / 625000000) ∧
    -Real.log (611406031 / 625000000) ≤ (21990377 / 1000000000) := by
  have h := checkLog_sound (w := (13593969 / 1236406031)) (n := 12)
    (lo := (2748797 / 125000000)) (hi := (21990377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 611406031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 611406031) = 1/(611406031 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21990377 / 1000000000) (-2748797 / 125000000) (Real.log (611406031 / 625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell069

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell070Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell070
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (255882969 / 1000000000) ≤ -Real.log (5120 / 6613) ∧
    -Real.log (5120 / 6613) ≤ (25588297 / 100000000) := by
  have h := checkLog_sound (w := (1493 / 11733)) (n := 12)
    (lo := (255882969 / 1000000000)) (hi := (25588297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6613 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6613 / 5120) = 1/(5120 / 6613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (255882969 / 1000000000) (25588297 / 100000000) (Real.log (6613 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6613 / 5120) = -Real.log (5120 / 6613) := by
    rw [show ((6613 / 5120) : ℝ) = ((5120 / 6613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (172374289 / 500000000) ≤ -Real.log (3627 / 5120) ∧
    -Real.log (3627 / 5120) ≤ (344748579 / 1000000000) := by
  have h := checkLog_sound (w := (1493 / 8747)) (n := 12)
    (lo := (172374289 / 500000000)) (hi := (344748579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3627) = 1/(3627 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-344748579 / 1000000000) (-172374289 / 500000000) (Real.log (3627 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (127714607 / 500000000) ≤ -Real.log (512 / 661) ∧
    -Real.log (512 / 661) ≤ (51085843 / 200000000) := by
  have h := checkLog_sound (w := (149 / 1173)) (n := 12)
    (lo := (127714607 / 500000000)) (hi := (51085843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661 / 512) = 1/(512 / 661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (127714607 / 500000000) (51085843 / 200000000) (Real.log (661 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (661 / 512) = -Real.log (512 / 661) := by
    rw [show ((661 / 512) : ℝ) = ((512 / 661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (34392179 / 100000000) ≤ -Real.log (363 / 512) ∧
    -Real.log (363 / 512) ≤ (343921791 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 875)) (n := 12)
    (lo := (34392179 / 100000000)) (hi := (343921791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 363) = 1/(363 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-343921791 / 1000000000) (-34392179 / 100000000) (Real.log (363 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (187749299 / 1000000000) ≤ -Real.log (1000000 / 1206531) ∧
    -Real.log (1000000 / 1206531) ≤ (1877493 / 10000000) := by
  have h := checkLog_sound (w := (206531 / 2206531)) (n := 12)
    (lo := (187749299 / 1000000000)) (hi := (1877493 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206531 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206531 / 1000000) = 1/(1000000 / 1206531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (187749299 / 1000000000) (1877493 / 10000000) (Real.log (1206531 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1206531 / 1000000) = -Real.log (1000000 / 1206531) := by
    rw [show ((1206531 / 1000000) : ℝ) = ((1000000 / 1206531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (231340807 / 1000000000) ≤ -Real.log (793469 / 1000000) ∧
    -Real.log (793469 / 1000000) ≤ (28917601 / 125000000) := by
  have h := checkLog_sound (w := (206531 / 1793469)) (n := 12)
    (lo := (231340807 / 1000000000)) (hi := (28917601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793469) = 1/(793469 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-28917601 / 125000000) (-231340807 / 1000000000) (Real.log (793469 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2939021 / 15625000) ≤ -Real.log (1000000 / 1206951) ∧
    -Real.log (1000000 / 1206951) ≤ (37619469 / 200000000) := by
  have h := checkLog_sound (w := (206951 / 2206951)) (n := 12)
    (lo := (2939021 / 15625000)) (hi := (37619469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206951 / 1000000) = 1/(1000000 / 1206951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2939021 / 15625000) (37619469 / 200000000) (Real.log (1206951 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1206951 / 1000000) = -Real.log (1000000 / 1206951) := by
    rw [show ((1206951 / 1000000) : ℝ) = ((1000000 / 1206951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (57967567 / 250000000) ≤ -Real.log (793049 / 1000000) ∧
    -Real.log (793049 / 1000000) ≤ (231870269 / 1000000000) := by
  have h := checkLog_sound (w := (206951 / 1793049)) (n := 12)
    (lo := (57967567 / 250000000)) (hi := (231870269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793049) = 1/(793049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-231870269 / 1000000000) (-57967567 / 250000000) (Real.log (793049 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6891787 / 50000000) ≤ -Real.log (1000000 / 1147787) ∧
    -Real.log (1000000 / 1147787) ≤ (137835741 / 1000000000) := by
  have h := checkLog_sound (w := (147787 / 2147787)) (n := 12)
    (lo := (6891787 / 50000000)) (hi := (137835741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147787 / 1000000) = 1/(1000000 / 1147787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6891787 / 50000000) (137835741 / 1000000000) (Real.log (1147787 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1147787 / 1000000) = -Real.log (1000000 / 1147787) := by
    rw [show ((1147787 / 1000000) : ℝ) = ((1000000 / 1147787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (159918783 / 1000000000) ≤ -Real.log (852213 / 1000000) ∧
    -Real.log (852213 / 1000000) ≤ (2498731 / 15625000) := by
  have h := checkLog_sound (w := (147787 / 1852213)) (n := 12)
    (lo := (159918783 / 1000000000)) (hi := (2498731 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852213) = 1/(852213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2498731 / 15625000) (-159918783 / 1000000000) (Real.log (852213 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138104047 / 1000000000) ≤ -Real.log (200000 / 229619) ∧
    -Real.log (200000 / 229619) ≤ (8631503 / 62500000) := by
  have h := checkLog_sound (w := (29619 / 429619)) (n := 12)
    (lo := (138104047 / 1000000000)) (hi := (8631503 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229619 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229619 / 200000) = 1/(200000 / 229619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138104047 / 1000000000) (8631503 / 62500000) (Real.log (229619 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (229619 / 200000) = -Real.log (200000 / 229619) := by
    rw [show ((229619 / 200000) : ℝ) = ((200000 / 229619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (8014013 / 50000000) ≤ -Real.log (170381 / 200000) ∧
    -Real.log (170381 / 200000) ≤ (160280261 / 1000000000) := by
  have h := checkLog_sound (w := (29619 / 370381)) (n := 12)
    (lo := (8014013 / 50000000)) (hi := (160280261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 170381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 170381) = 1/(170381 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-160280261 / 1000000000) (-8014013 / 50000000) (Real.log (170381 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (119870201 / 200000000) ≤ -Real.log (500000000000 / 910468319559) ∧
    -Real.log (500000000000 / 910468319559) ≤ (299675503 / 500000000) := by
  have h := checkLog_sound (w := (410468319559 / 1410468319559)) (n := 12)
    (lo := (119870201 / 200000000)) (hi := (299675503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((910468319559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(910468319559 / 500000000000) = 1/(500000000000 / 910468319559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (119870201 / 200000000) (299675503 / 500000000) (Real.log (910468319559 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (910468319559 / 500000000000) = -Real.log (500000000000 / 910468319559) := by
    rw [show ((910468319559 / 500000000000) : ℝ) = ((500000000000 / 910468319559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150157887 / 250000000) ≤ -Real.log (500000000000 / 911634960023) ∧
    -Real.log (500000000000 / 911634960023) ≤ (600631549 / 1000000000) := by
  have h := checkLog_sound (w := (411634960023 / 1411634960023)) (n := 12)
    (lo := (150157887 / 250000000)) (hi := (600631549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911634960023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911634960023 / 500000000000) = 1/(500000000000 / 911634960023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (150157887 / 250000000) (600631549 / 1000000000) (Real.log (911634960023 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (911634960023 / 500000000000) = -Real.log (500000000000 / 911634960023) := by
    rw [show ((911634960023 / 500000000000) : ℝ) = ((500000000000 / 911634960023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (419090107 / 1000000000) ≤ -Real.log (20000000000 / 30411547269) ∧
    -Real.log (20000000000 / 30411547269) ≤ (104772527 / 250000000) := by
  have h := checkLog_sound (w := (10411547269 / 50411547269)) (n := 12)
    (lo := (419090107 / 1000000000)) (hi := (104772527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30411547269 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30411547269 / 20000000000) = 1/(20000000000 / 30411547269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (419090107 / 1000000000) (104772527 / 250000000) (Real.log (30411547269 / 20000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30411547269 / 20000000000) = -Real.log (20000000000 / 30411547269) := by
    rw [show ((30411547269 / 20000000000) : ℝ) = ((20000000000 / 30411547269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (419967613 / 1000000000) ≤ -Real.log (250000000000 / 380478066299) ∧
    -Real.log (250000000000 / 380478066299) ≤ (209983807 / 500000000) := by
  have h := checkLog_sound (w := (130478066299 / 630478066299)) (n := 12)
    (lo := (419967613 / 1000000000)) (hi := (209983807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380478066299 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380478066299 / 250000000000) = 1/(250000000000 / 380478066299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (419967613 / 1000000000) (209983807 / 500000000) (Real.log (380478066299 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (380478066299 / 250000000000) = -Real.log (250000000000 / 380478066299) := by
    rw [show ((380478066299 / 250000000000) : ℝ) = ((250000000000 / 380478066299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (74438631 / 250000000) ≤ -Real.log (62500000000 / 84176945787) ∧
    -Real.log (62500000000 / 84176945787) ≤ (11910181 / 40000000) := by
  have h := checkLog_sound (w := (21676945787 / 146676945787)) (n := 12)
    (lo := (74438631 / 250000000)) (hi := (11910181 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84176945787 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84176945787 / 62500000000) = 1/(62500000000 / 84176945787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (74438631 / 250000000) (11910181 / 40000000) (Real.log (84176945787 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (84176945787 / 62500000000) = -Real.log (62500000000 / 84176945787) := by
    rw [show ((84176945787 / 62500000000) : ℝ) = ((62500000000 / 84176945787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (298384307 / 1000000000) ≤ -Real.log (250000000000 / 336919903041) ∧
    -Real.log (250000000000 / 336919903041) ≤ (74596077 / 250000000) := by
  have h := checkLog_sound (w := (86919903041 / 586919903041)) (n := 12)
    (lo := (298384307 / 1000000000)) (hi := (74596077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336919903041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336919903041 / 250000000000) = 1/(250000000000 / 336919903041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (298384307 / 1000000000) (74596077 / 250000000) (Real.log (336919903041 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (336919903041 / 250000000000) = -Real.log (250000000000 / 336919903041) := by
    rw [show ((336919903041 / 250000000000) : ℝ) = ((250000000000 / 336919903041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22176213 / 1000000000) ≤ -Real.log (39122714839 / 40000000000) ∧
    -Real.log (39122714839 / 40000000000) ≤ (11088107 / 500000000) := by
  have h := checkLog_sound (w := (877285161 / 79122714839)) (n := 12)
    (lo := (22176213 / 1000000000)) (hi := (11088107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39122714839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39122714839) = 1/(39122714839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-11088107 / 500000000) (-22176213 / 1000000000) (Real.log (39122714839 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (11041521 / 500000000) ≤ -Real.log (978159002631 / 1000000000000) ∧
    -Real.log (978159002631 / 1000000000000) ≤ (22083043 / 1000000000) := by
  have h := checkLog_sound (w := (21840997369 / 1978159002631)) (n := 12)
    (lo := (11041521 / 500000000)) (hi := (22083043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978159002631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978159002631) = 1/(978159002631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22083043 / 1000000000) (-11041521 / 500000000) (Real.log (978159002631 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell070

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell071Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell071
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (128168259 / 500000000) ≤ -Real.log (640 / 827) ∧
    -Real.log (640 / 827) ≤ (256336519 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1467)) (n := 12)
    (lo := (128168259 / 500000000)) (hi := (256336519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827 / 640) = 1/(640 / 827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128168259 / 500000000) (256336519 / 1000000000) (Real.log (827 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (827 / 640) = -Real.log (640 / 827) := by
    rw [show ((827 / 640) : ℝ) = ((640 / 827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6911521 / 20000000) ≤ -Real.log (453 / 640) ∧
    -Real.log (453 / 640) ≤ (345576051 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1093)) (n := 12)
    (lo := (6911521 / 20000000)) (hi := (345576051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 453) = 1/(453 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-345576051 / 1000000000) (-6911521 / 20000000) (Real.log (453 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (255882969 / 1000000000) ≤ -Real.log (5120 / 6613) ∧
    -Real.log (5120 / 6613) ≤ (25588297 / 100000000) := by
  have h := checkLog_sound (w := (1493 / 11733)) (n := 12)
    (lo := (255882969 / 1000000000)) (hi := (25588297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6613 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6613 / 5120) = 1/(5120 / 6613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (255882969 / 1000000000) (25588297 / 100000000) (Real.log (6613 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6613 / 5120) = -Real.log (5120 / 6613) := by
    rw [show ((6613 / 5120) : ℝ) = ((5120 / 6613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (172374289 / 500000000) ≤ -Real.log (3627 / 5120) ∧
    -Real.log (3627 / 5120) ≤ (344748579 / 1000000000) := by
  have h := checkLog_sound (w := (1493 / 8747)) (n := 12)
    (lo := (172374289 / 500000000)) (hi := (344748579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3627) = 1/(3627 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-344748579 / 1000000000) (-172374289 / 500000000) (Real.log (3627 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47024129 / 250000000) ≤ -Real.log (20000 / 24139) ∧
    -Real.log (20000 / 24139) ≤ (188096517 / 1000000000) := by
  have h := checkLog_sound (w := (4139 / 44139)) (n := 12)
    (lo := (47024129 / 250000000)) (hi := (188096517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24139 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24139 / 20000) = 1/(20000 / 24139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47024129 / 250000000) (188096517 / 1000000000) (Real.log (24139 / 20000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24139 / 20000) = -Real.log (20000 / 24139) := by
    rw [show ((24139 / 20000) : ℝ) = ((20000 / 24139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (231869007 / 1000000000) ≤ -Real.log (15861 / 20000) ∧
    -Real.log (15861 / 20000) ≤ (14491813 / 62500000) := by
  have h := checkLog_sound (w := (4139 / 35861)) (n := 12)
    (lo := (231869007 / 1000000000)) (hi := (14491813 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15861) = 1/(15861 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-14491813 / 62500000) (-231869007 / 1000000000) (Real.log (15861 / 20000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (4711111 / 25000000) ≤ -Real.log (100000 / 120737) ∧
    -Real.log (100000 / 120737) ≤ (188444441 / 1000000000) := by
  have h := checkLog_sound (w := (20737 / 220737)) (n := 12)
    (lo := (4711111 / 25000000)) (hi := (188444441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120737 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120737 / 100000) = 1/(100000 / 120737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (4711111 / 25000000) (188444441 / 1000000000) (Real.log (120737 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (120737 / 100000) = -Real.log (100000 / 120737) := by
    rw [show ((120737 / 100000) : ℝ) = ((100000 / 120737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58099687 / 250000000) ≤ -Real.log (79263 / 100000) ∧
    -Real.log (79263 / 100000) ≤ (232398749 / 1000000000) := by
  have h := checkLog_sound (w := (20737 / 179263)) (n := 12)
    (lo := (58099687 / 250000000)) (hi := (232398749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 79263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 79263) = 1/(79263 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-232398749 / 1000000000) (-58099687 / 250000000) (Real.log (79263 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17262897 / 125000000) ≤ -Real.log (500000 / 574047) ∧
    -Real.log (500000 / 574047) ≤ (138103177 / 1000000000) := by
  have h := checkLog_sound (w := (74047 / 1074047)) (n := 12)
    (lo := (17262897 / 125000000)) (hi := (138103177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574047 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574047 / 500000) = 1/(500000 / 574047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17262897 / 125000000) (138103177 / 1000000000) (Real.log (574047 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (574047 / 500000) = -Real.log (500000 / 574047) := by
    rw [show ((574047 / 500000) : ℝ) = ((500000 / 574047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (80139543 / 500000000) ≤ -Real.log (425953 / 500000) ∧
    -Real.log (425953 / 500000) ≤ (160279087 / 1000000000) := by
  have h := checkLog_sound (w := (74047 / 925953)) (n := 12)
    (lo := (80139543 / 500000000)) (hi := (160279087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425953) = 1/(425953 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-160279087 / 1000000000) (-80139543 / 500000000) (Real.log (425953 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13837141 / 100000000) ≤ -Real.log (500000 / 574201) ∧
    -Real.log (500000 / 574201) ≤ (138371411 / 1000000000) := by
  have h := checkLog_sound (w := (74201 / 1074201)) (n := 12)
    (lo := (13837141 / 100000000)) (hi := (138371411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574201 / 500000) = 1/(500000 / 574201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13837141 / 100000000) (138371411 / 1000000000) (Real.log (574201 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (574201 / 500000) = -Real.log (500000 / 574201) := by
    rw [show ((574201 / 500000) : ℝ) = ((500000 / 574201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (80320347 / 500000000) ≤ -Real.log (425799 / 500000) ∧
    -Real.log (425799 / 500000) ≤ (32128139 / 200000000) := by
  have h := checkLog_sound (w := (74201 / 925799)) (n := 12)
    (lo := (80320347 / 500000000)) (hi := (32128139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425799) = 1/(425799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-32128139 / 200000000) (-80320347 / 500000000) (Real.log (425799 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150157887 / 250000000) ≤ -Real.log (250000000000 / 455817480011) ∧
    -Real.log (250000000000 / 455817480011) ≤ (600631549 / 1000000000) := by
  have h := checkLog_sound (w := (205817480011 / 705817480011)) (n := 12)
    (lo := (150157887 / 250000000)) (hi := (600631549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455817480011 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455817480011 / 250000000000) = 1/(250000000000 / 455817480011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150157887 / 250000000) (600631549 / 1000000000) (Real.log (455817480011 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (455817480011 / 250000000000) = -Real.log (250000000000 / 455817480011) := by
    rw [show ((455817480011 / 250000000000) : ℝ) = ((250000000000 / 455817480011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (601912569 / 1000000000) ≤ -Real.log (500000000000 / 912803532009) ∧
    -Real.log (500000000000 / 912803532009) ≤ (60191257 / 100000000) := by
  have h := checkLog_sound (w := (412803532009 / 1412803532009)) (n := 12)
    (lo := (601912569 / 1000000000)) (hi := (60191257 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((912803532009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(912803532009 / 500000000000) = 1/(500000000000 / 912803532009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (601912569 / 1000000000) (60191257 / 100000000) (Real.log (912803532009 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (912803532009 / 500000000000) = -Real.log (500000000000 / 912803532009) := by
    rw [show ((912803532009 / 500000000000) : ℝ) = ((500000000000 / 912803532009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (419965523 / 1000000000) ≤ -Real.log (125000000000 / 190238635647) ∧
    -Real.log (125000000000 / 190238635647) ≤ (104991381 / 250000000) := by
  have h := checkLog_sound (w := (65238635647 / 315238635647)) (n := 12)
    (lo := (419965523 / 1000000000)) (hi := (104991381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190238635647 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190238635647 / 125000000000) = 1/(125000000000 / 190238635647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (419965523 / 1000000000) (104991381 / 250000000) (Real.log (190238635647 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (190238635647 / 125000000000) = -Real.log (125000000000 / 190238635647) := by
    rw [show ((190238635647 / 125000000000) : ℝ) = ((125000000000 / 190238635647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (420843189 / 1000000000) ≤ -Real.log (125000000000 / 190405674779) ∧
    -Real.log (125000000000 / 190405674779) ≤ (42084319 / 100000000) := by
  have h := checkLog_sound (w := (65405674779 / 315405674779)) (n := 12)
    (lo := (420843189 / 1000000000)) (hi := (42084319 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190405674779 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190405674779 / 125000000000) = 1/(125000000000 / 190405674779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (420843189 / 1000000000) (42084319 / 100000000) (Real.log (190405674779 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (190405674779 / 125000000000) = -Real.log (125000000000 / 190405674779) := by
    rw [show ((190405674779 / 125000000000) : ℝ) = ((125000000000 / 190405674779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (149191131 / 500000000) ≤ -Real.log (500000000000 / 673838428183) ∧
    -Real.log (500000000000 / 673838428183) ≤ (298382263 / 1000000000) := by
  have h := checkLog_sound (w := (173838428183 / 1173838428183)) (n := 12)
    (lo := (149191131 / 500000000)) (hi := (298382263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673838428183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673838428183 / 500000000000) = 1/(500000000000 / 673838428183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (149191131 / 500000000) (298382263 / 1000000000) (Real.log (673838428183 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (673838428183 / 500000000000) = -Real.log (500000000000 / 673838428183) := by
    rw [show ((673838428183 / 500000000000) : ℝ) = ((500000000000 / 673838428183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (59802421 / 200000000) ≤ -Real.log (100000000000 / 134852594769) ∧
    -Real.log (100000000000 / 134852594769) ≤ (149506053 / 500000000) := by
  have h := checkLog_sound (w := (34852594769 / 234852594769)) (n := 12)
    (lo := (59802421 / 200000000)) (hi := (149506053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134852594769 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134852594769 / 100000000000) = 1/(100000000000 / 134852594769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (59802421 / 200000000) (149506053 / 500000000) (Real.log (134852594769 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (134852594769 / 100000000000) = -Real.log (100000000000 / 134852594769) := by
    rw [show ((134852594769 / 100000000000) : ℝ) = ((100000000000 / 134852594769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22269283 / 1000000000) ≤ -Real.log (244494211599 / 250000000000) ∧
    -Real.log (244494211599 / 250000000000) ≤ (5567321 / 250000000) := by
  have h := checkLog_sound (w := (5505788401 / 494494211599)) (n := 12)
    (lo := (22269283 / 1000000000)) (hi := (5567321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244494211599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244494211599) = 1/(244494211599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5567321 / 250000000) (-22269283 / 1000000000) (Real.log (244494211599 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2217591 / 100000000) ≤ -Real.log (244517041791 / 250000000000) ∧
    -Real.log (244517041791 / 250000000000) ≤ (22175911 / 1000000000) := by
  have h := checkLog_sound (w := (5482958209 / 494517041791)) (n := 12)
    (lo := (2217591 / 100000000)) (hi := (22175911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244517041791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244517041791) = 1/(244517041791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22175911 / 1000000000) (-2217591 / 100000000) (Real.log (244517041791 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell071

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell072Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell072
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (128394931 / 500000000) ≤ -Real.log (5120 / 6619) ∧
    -Real.log (5120 / 6619) ≤ (256789863 / 1000000000) := by
  have h := checkLog_sound (w := (1499 / 11739)) (n := 12)
    (lo := (128394931 / 500000000)) (hi := (256789863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6619 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6619 / 5120) = 1/(5120 / 6619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128394931 / 500000000) (256789863 / 1000000000) (Real.log (6619 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6619 / 5120) = -Real.log (5120 / 6619) := by
    rw [show ((6619 / 5120) : ℝ) = ((5120 / 6619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (21650263 / 62500000) ≤ -Real.log (3621 / 5120) ∧
    -Real.log (3621 / 5120) ≤ (346404209 / 1000000000) := by
  have h := checkLog_sound (w := (1499 / 8741)) (n := 12)
    (lo := (21650263 / 62500000)) (hi := (346404209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3621) = 1/(3621 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-346404209 / 1000000000) (-21650263 / 62500000) (Real.log (3621 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128168259 / 500000000) ≤ -Real.log (640 / 827) ∧
    -Real.log (640 / 827) ≤ (256336519 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1467)) (n := 12)
    (lo := (128168259 / 500000000)) (hi := (256336519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827 / 640) = 1/(640 / 827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128168259 / 500000000) (256336519 / 1000000000) (Real.log (827 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (827 / 640) = -Real.log (640 / 827) := by
    rw [show ((827 / 640) : ℝ) = ((640 / 827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6911521 / 20000000) ≤ -Real.log (453 / 640) ∧
    -Real.log (453 / 640) ≤ (345576051 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1093)) (n := 12)
    (lo := (6911521 / 20000000)) (hi := (345576051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 453) = 1/(453 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-345576051 / 1000000000) (-6911521 / 20000000) (Real.log (453 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47110903 / 250000000) ≤ -Real.log (1000000 / 1207369) ∧
    -Real.log (1000000 / 1207369) ≤ (188443613 / 1000000000) := by
  have h := checkLog_sound (w := (207369 / 2207369)) (n := 12)
    (lo := (47110903 / 250000000)) (hi := (188443613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207369 / 1000000) = 1/(1000000 / 1207369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47110903 / 250000000) (188443613 / 1000000000) (Real.log (1207369 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1207369 / 1000000) = -Real.log (1000000 / 1207369) := by
    rw [show ((1207369 / 1000000) : ℝ) = ((1000000 / 1207369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (232397487 / 1000000000) ≤ -Real.log (792631 / 1000000) ∧
    -Real.log (792631 / 1000000) ≤ (14524843 / 62500000) := by
  have h := checkLog_sound (w := (207369 / 1792631)) (n := 12)
    (lo := (232397487 / 1000000000)) (hi := (14524843 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792631) = 1/(792631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-14524843 / 62500000) (-232397487 / 1000000000) (Real.log (792631 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (37758283 / 200000000) ≤ -Real.log (1000000 / 1207789) ∧
    -Real.log (1000000 / 1207789) ≤ (23598927 / 125000000) := by
  have h := checkLog_sound (w := (207789 / 2207789)) (n := 12)
    (lo := (37758283 / 200000000)) (hi := (23598927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207789 / 1000000) = 1/(1000000 / 1207789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (37758283 / 200000000) (23598927 / 125000000) (Real.log (1207789 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1207789 / 1000000) = -Real.log (1000000 / 1207789) := by
    rw [show ((1207789 / 1000000) : ℝ) = ((1000000 / 1207789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58231877 / 250000000) ≤ -Real.log (792211 / 1000000) ∧
    -Real.log (792211 / 1000000) ≤ (232927509 / 1000000000) := by
  have h := checkLog_sound (w := (207789 / 1792211)) (n := 12)
    (lo := (58231877 / 250000000)) (hi := (232927509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792211) = 1/(792211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-232927509 / 1000000000) (-58231877 / 250000000) (Real.log (792211 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6918527 / 50000000) ≤ -Real.log (1000000 / 1148401) ∧
    -Real.log (1000000 / 1148401) ≤ (138370541 / 1000000000) := by
  have h := checkLog_sound (w := (148401 / 2148401)) (n := 12)
    (lo := (6918527 / 50000000)) (hi := (138370541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148401 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148401 / 1000000) = 1/(1000000 / 1148401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6918527 / 50000000) (138370541 / 1000000000) (Real.log (1148401 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1148401 / 1000000) = -Real.log (1000000 / 1148401) := by
    rw [show ((1148401 / 1000000) : ℝ) = ((1000000 / 1148401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1003997 / 6250000) ≤ -Real.log (851599 / 1000000) ∧
    -Real.log (851599 / 1000000) ≤ (160639521 / 1000000000) := by
  have h := checkLog_sound (w := (148401 / 1851599)) (n := 12)
    (lo := (1003997 / 6250000)) (hi := (160639521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851599) = 1/(851599 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-160639521 / 1000000000) (-1003997 / 6250000) (Real.log (851599 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138638703 / 1000000000) ≤ -Real.log (1000000 / 1148709) ∧
    -Real.log (1000000 / 1148709) ≤ (8664919 / 62500000) := by
  have h := checkLog_sound (w := (148709 / 2148709)) (n := 12)
    (lo := (138638703 / 1000000000)) (hi := (8664919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148709 / 1000000) = 1/(1000000 / 1148709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138638703 / 1000000000) (8664919 / 62500000) (Real.log (1148709 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1148709 / 1000000) = -Real.log (1000000 / 1148709) := by
    rw [show ((1148709 / 1000000) : ℝ) = ((1000000 / 1148709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (80500629 / 500000000) ≤ -Real.log (851291 / 1000000) ∧
    -Real.log (851291 / 1000000) ≤ (161001259 / 1000000000) := by
  have h := checkLog_sound (w := (148709 / 1851291)) (n := 12)
    (lo := (80500629 / 500000000)) (hi := (161001259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851291) = 1/(851291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-161001259 / 1000000000) (-80500629 / 500000000) (Real.log (851291 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (601912569 / 1000000000) ≤ -Real.log (62500000000 / 114100441501) ∧
    -Real.log (62500000000 / 114100441501) ≤ (60191257 / 100000000) := by
  have h := checkLog_sound (w := (51600441501 / 176600441501)) (n := 12)
    (lo := (601912569 / 1000000000)) (hi := (60191257 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114100441501 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114100441501 / 62500000000) = 1/(62500000000 / 114100441501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (601912569 / 1000000000) (60191257 / 100000000) (Real.log (114100441501 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (114100441501 / 62500000000) = -Real.log (62500000000 / 114100441501) := by
    rw [show ((114100441501 / 62500000000) : ℝ) = ((62500000000 / 114100441501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (60319407 / 100000000) ≤ -Real.log (500000000000 / 913974040321) ∧
    -Real.log (500000000000 / 913974040321) ≤ (603194071 / 1000000000) := by
  have h := checkLog_sound (w := (413974040321 / 1413974040321)) (n := 12)
    (lo := (60319407 / 100000000)) (hi := (603194071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913974040321 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(913974040321 / 500000000000) = 1/(500000000000 / 913974040321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (60319407 / 100000000) (603194071 / 1000000000) (Real.log (913974040321 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (913974040321 / 500000000000) = -Real.log (500000000000 / 913974040321) := by
    rw [show ((913974040321 / 500000000000) : ℝ) = ((500000000000 / 913974040321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (420841099 / 1000000000) ≤ -Real.log (20000000000 / 30464844297) ∧
    -Real.log (20000000000 / 30464844297) ≤ (4208411 / 10000000) := by
  have h := checkLog_sound (w := (10464844297 / 50464844297)) (n := 12)
    (lo := (420841099 / 1000000000)) (hi := (4208411 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30464844297 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30464844297 / 20000000000) = 1/(20000000000 / 30464844297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (420841099 / 1000000000) (4208411 / 10000000) (Real.log (30464844297 / 20000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30464844297 / 20000000000) = -Real.log (20000000000 / 30464844297) := by
    rw [show ((30464844297 / 20000000000) : ℝ) = ((20000000000 / 30464844297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (421718923 / 1000000000) ≤ -Real.log (62500000000 / 95286246341) ∧
    -Real.log (62500000000 / 95286246341) ≤ (105429731 / 250000000) := by
  have h := checkLog_sound (w := (32786246341 / 157786246341)) (n := 12)
    (lo := (421718923 / 1000000000)) (hi := (105429731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95286246341 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95286246341 / 62500000000) = 1/(62500000000 / 95286246341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (421718923 / 1000000000) (105429731 / 250000000) (Real.log (95286246341 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (95286246341 / 62500000000) = -Real.log (62500000000 / 95286246341) := by
    rw [show ((95286246341 / 62500000000) : ℝ) = ((62500000000 / 95286246341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14950503 / 50000000) ≤ -Real.log (62500000000 / 84282699369) ∧
    -Real.log (62500000000 / 84282699369) ≤ (299010061 / 1000000000) := by
  have h := checkLog_sound (w := (21782699369 / 146782699369)) (n := 12)
    (lo := (14950503 / 50000000)) (hi := (299010061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84282699369 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84282699369 / 62500000000) = 1/(62500000000 / 84282699369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14950503 / 50000000) (299010061 / 1000000000) (Real.log (84282699369 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (84282699369 / 62500000000) = -Real.log (62500000000 / 84282699369) := by
    rw [show ((84282699369 / 62500000000) : ℝ) = ((62500000000 / 84282699369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (299639961 / 1000000000) ≤ -Real.log (500000000000 / 674686446821) ∧
    -Real.log (500000000000 / 674686446821) ≤ (149819981 / 500000000) := by
  have h := checkLog_sound (w := (174686446821 / 1174686446821)) (n := 12)
    (lo := (299639961 / 1000000000)) (hi := (149819981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674686446821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674686446821 / 500000000000) = 1/(500000000000 / 674686446821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (299639961 / 1000000000) (149819981 / 500000000) (Real.log (674686446821 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (674686446821 / 500000000000) = -Real.log (500000000000 / 674686446821) := by
    rw [show ((674686446821 / 500000000000) : ℝ) = ((500000000000 / 674686446821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4472511 / 200000000) ≤ -Real.log (977885633319 / 1000000000000) ∧
    -Real.log (977885633319 / 1000000000000) ≤ (5590639 / 250000000) := by
  have h := checkLog_sound (w := (22114366681 / 1977885633319)) (n := 12)
    (lo := (4472511 / 200000000)) (hi := (5590639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977885633319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977885633319) = 1/(977885633319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5590639 / 250000000) (-4472511 / 200000000) (Real.log (977885633319 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1113449 / 50000000) ≤ -Real.log (977977143199 / 1000000000000) ∧
    -Real.log (977977143199 / 1000000000000) ≤ (22268981 / 1000000000) := by
  have h := checkLog_sound (w := (22022856801 / 1977977143199)) (n := 12)
    (lo := (1113449 / 50000000)) (hi := (22268981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977977143199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977977143199) = 1/(977977143199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22268981 / 1000000000) (-1113449 / 50000000) (Real.log (977977143199 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell072

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell073Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell073
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (257243 / 1000000) ≤ -Real.log (2560 / 3311) ∧
    -Real.log (2560 / 3311) ≤ (257243001 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 5871)) (n := 12)
    (lo := (257243 / 1000000)) (hi := (257243001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3311 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3311 / 2560) = 1/(2560 / 3311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (257243 / 1000000) (257243001 / 1000000000) (Real.log (3311 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3311 / 2560) = -Real.log (2560 / 3311) := by
    rw [show ((3311 / 2560) : ℝ) = ((2560 / 3311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86808263 / 250000000) ≤ -Real.log (1809 / 2560) ∧
    -Real.log (1809 / 2560) ≤ (347233053 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 4369)) (n := 12)
    (lo := (86808263 / 250000000)) (hi := (347233053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1809) = 1/(1809 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-347233053 / 1000000000) (-86808263 / 250000000) (Real.log (1809 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128394931 / 500000000) ≤ -Real.log (5120 / 6619) ∧
    -Real.log (5120 / 6619) ≤ (256789863 / 1000000000) := by
  have h := checkLog_sound (w := (1499 / 11739)) (n := 12)
    (lo := (128394931 / 500000000)) (hi := (256789863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6619 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6619 / 5120) = 1/(5120 / 6619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128394931 / 500000000) (256789863 / 1000000000) (Real.log (6619 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6619 / 5120) = -Real.log (5120 / 6619) := by
    rw [show ((6619 / 5120) : ℝ) = ((5120 / 6619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (21650263 / 62500000) ≤ -Real.log (3621 / 5120) ∧
    -Real.log (3621 / 5120) ≤ (346404209 / 1000000000) := by
  have h := checkLog_sound (w := (1499 / 8741)) (n := 12)
    (lo := (21650263 / 62500000)) (hi := (346404209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3621) = 1/(3621 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-346404209 / 1000000000) (-21650263 / 62500000) (Real.log (3621 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (188790587 / 1000000000) ≤ -Real.log (250000 / 301947) ∧
    -Real.log (250000 / 301947) ≤ (47197647 / 250000000) := by
  have h := checkLog_sound (w := (51947 / 551947)) (n := 12)
    (lo := (188790587 / 1000000000)) (hi := (47197647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301947 / 250000) = 1/(250000 / 301947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (188790587 / 1000000000) (47197647 / 250000000) (Real.log (301947 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (301947 / 250000) = -Real.log (250000 / 301947) := by
    rw [show ((301947 / 250000) : ℝ) = ((250000 / 301947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (116463123 / 500000000) ≤ -Real.log (198053 / 250000) ∧
    -Real.log (198053 / 250000) ≤ (232926247 / 1000000000) := by
  have h := checkLog_sound (w := (51947 / 448053)) (n := 12)
    (lo := (116463123 / 500000000)) (hi := (232926247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198053) = 1/(198053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-232926247 / 1000000000) (-116463123 / 500000000) (Real.log (198053 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18913827 / 100000000) ≤ -Real.log (62500 / 75513) ∧
    -Real.log (62500 / 75513) ≤ (189138271 / 1000000000) := by
  have h := checkLog_sound (w := (13013 / 138013)) (n := 12)
    (lo := (18913827 / 100000000)) (hi := (189138271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75513 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75513 / 62500) = 1/(62500 / 75513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18913827 / 100000000) (189138271 / 1000000000) (Real.log (75513 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (75513 / 62500) = -Real.log (62500 / 75513) := by
    rw [show ((75513 / 62500) : ℝ) = ((62500 / 75513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (233456547 / 1000000000) ≤ -Real.log (49487 / 62500) ∧
    -Real.log (49487 / 62500) ≤ (58364137 / 250000000) := by
  have h := checkLog_sound (w := (13013 / 111987)) (n := 12)
    (lo := (233456547 / 1000000000)) (hi := (58364137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49487) = 1/(49487 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-58364137 / 250000000) (-233456547 / 1000000000) (Real.log (49487 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17329729 / 125000000) ≤ -Real.log (250000 / 287177) ∧
    -Real.log (250000 / 287177) ≤ (138637833 / 1000000000) := by
  have h := checkLog_sound (w := (37177 / 537177)) (n := 12)
    (lo := (17329729 / 125000000)) (hi := (138637833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287177 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287177 / 250000) = 1/(250000 / 287177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17329729 / 125000000) (138637833 / 1000000000) (Real.log (287177 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (287177 / 250000) = -Real.log (250000 / 287177) := by
    rw [show ((287177 / 250000) : ℝ) = ((250000 / 287177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (161000083 / 1000000000) ≤ -Real.log (212823 / 250000) ∧
    -Real.log (212823 / 250000) ≤ (40250021 / 250000000) := by
  have h := checkLog_sound (w := (37177 / 462823)) (n := 12)
    (lo := (161000083 / 1000000000)) (hi := (40250021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212823) = 1/(212823 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-40250021 / 250000000) (-161000083 / 1000000000) (Real.log (212823 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138905923 / 1000000000) ≤ -Real.log (125000 / 143627) ∧
    -Real.log (125000 / 143627) ≤ (34726481 / 250000000) := by
  have h := checkLog_sound (w := (18627 / 268627)) (n := 12)
    (lo := (138905923 / 1000000000)) (hi := (34726481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143627 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143627 / 125000) = 1/(125000 / 143627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138905923 / 1000000000) (34726481 / 250000000) (Real.log (143627 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (143627 / 125000) = -Real.log (125000 / 143627) := by
    rw [show ((143627 / 125000) : ℝ) = ((125000 / 143627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (161361951 / 1000000000) ≤ -Real.log (106373 / 125000) ∧
    -Real.log (106373 / 125000) ≤ (5042561 / 31250000) := by
  have h := checkLog_sound (w := (18627 / 231373)) (n := 12)
    (lo := (161361951 / 1000000000)) (hi := (5042561 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106373) = 1/(106373 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5042561 / 31250000) (-161361951 / 1000000000) (Real.log (106373 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (60319407 / 100000000) ≤ -Real.log (390625000 / 714042219) ∧
    -Real.log (390625000 / 714042219) ≤ (603194071 / 1000000000) := by
  have h := checkLog_sound (w := (323417219 / 1104667219)) (n := 12)
    (lo := (60319407 / 100000000)) (hi := (603194071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714042219 / 390625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714042219 / 390625000) = 1/(390625000 / 714042219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (60319407 / 100000000) (603194071 / 1000000000) (Real.log (714042219 / 390625000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (714042219 / 390625000) = -Real.log (390625000 / 714042219) := by
    rw [show ((714042219 / 390625000) : ℝ) = ((390625000 / 714042219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (151119013 / 250000000) ≤ -Real.log (250000000000 / 457573244887) ∧
    -Real.log (250000000000 / 457573244887) ≤ (604476053 / 1000000000) := by
  have h := checkLog_sound (w := (207573244887 / 707573244887)) (n := 12)
    (lo := (151119013 / 250000000)) (hi := (604476053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457573244887 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457573244887 / 250000000000) = 1/(250000000000 / 457573244887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (151119013 / 250000000) (604476053 / 1000000000) (Real.log (457573244887 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (457573244887 / 250000000000) = -Real.log (250000000000 / 457573244887) := by
    rw [show ((457573244887 / 250000000000) : ℝ) = ((250000000000 / 457573244887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (421716833 / 1000000000) ≤ -Real.log (500000000000 / 762288377353) ∧
    -Real.log (500000000000 / 762288377353) ≤ (210858417 / 500000000) := by
  have h := checkLog_sound (w := (262288377353 / 1262288377353)) (n := 12)
    (lo := (421716833 / 1000000000)) (hi := (210858417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762288377353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762288377353 / 500000000000) = 1/(500000000000 / 762288377353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (421716833 / 1000000000) (210858417 / 500000000) (Real.log (762288377353 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (762288377353 / 500000000000) = -Real.log (500000000000 / 762288377353) := by
    rw [show ((762288377353 / 500000000000) : ℝ) = ((500000000000 / 762288377353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (211297409 / 500000000) ≤ -Real.log (500000000000 / 762957948553) ∧
    -Real.log (500000000000 / 762957948553) ≤ (422594819 / 1000000000) := by
  have h := checkLog_sound (w := (262957948553 / 1262957948553)) (n := 12)
    (lo := (211297409 / 500000000)) (hi := (422594819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762957948553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762957948553 / 500000000000) = 1/(500000000000 / 762957948553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (211297409 / 500000000) (422594819 / 1000000000) (Real.log (762957948553 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (762957948553 / 500000000000) = -Real.log (500000000000 / 762957948553) := by
    rw [show ((762957948553 / 500000000000) : ℝ) = ((500000000000 / 762957948553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (74909479 / 250000000) ≤ -Real.log (500000000000 / 674685066933) ∧
    -Real.log (500000000000 / 674685066933) ≤ (299637917 / 1000000000) := by
  have h := checkLog_sound (w := (174685066933 / 1174685066933)) (n := 12)
    (lo := (74909479 / 250000000)) (hi := (299637917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674685066933 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674685066933 / 500000000000) = 1/(500000000000 / 674685066933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (74909479 / 250000000) (299637917 / 1000000000) (Real.log (674685066933 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (674685066933 / 500000000000) = -Real.log (500000000000 / 674685066933) := by
    rw [show ((674685066933 / 500000000000) : ℝ) = ((500000000000 / 674685066933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2402143 / 8000000) ≤ -Real.log (25000000000 / 33755511267) ∧
    -Real.log (25000000000 / 33755511267) ≤ (75066969 / 250000000) := by
  have h := checkLog_sound (w := (8755511267 / 58755511267)) (n := 12)
    (lo := (2402143 / 8000000)) (hi := (75066969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33755511267 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33755511267 / 25000000000) = 1/(25000000000 / 33755511267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2402143 / 8000000) (75066969 / 250000000) (Real.log (33755511267 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (33755511267 / 25000000000) = -Real.log (25000000000 / 33755511267) := by
    rw [show ((33755511267 / 25000000000) : ℝ) = ((25000000000 / 33755511267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5614007 / 250000000) ≤ -Real.log (15278034871 / 15625000000) ∧
    -Real.log (15278034871 / 15625000000) ≤ (22456029 / 1000000000) := by
  have h := checkLog_sound (w := (346965129 / 30903034871)) (n := 12)
    (lo := (5614007 / 250000000)) (hi := (22456029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15278034871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15278034871) = 1/(15278034871 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-22456029 / 1000000000) (-5614007 / 250000000) (Real.log (15278034871 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (89449 / 4000000) ≤ -Real.log (61117870671 / 62500000000) ∧
    -Real.log (61117870671 / 62500000000) ≤ (22362251 / 1000000000) := by
  have h := checkLog_sound (w := (1382129329 / 123617870671)) (n := 12)
    (lo := (89449 / 4000000)) (hi := (22362251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61117870671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61117870671) = 1/(61117870671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22362251 / 1000000000) (-89449 / 4000000) (Real.log (61117870671 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell073

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell074Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell074
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (64423983 / 250000000) ≤ -Real.log (1024 / 1325) ∧
    -Real.log (1024 / 1325) ≤ (257695933 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 2349)) (n := 12)
    (lo := (64423983 / 250000000)) (hi := (257695933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325 / 1024) = 1/(1024 / 1325) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (64423983 / 250000000) (257695933 / 1000000000) (Real.log (1325 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1325 / 1024) = -Real.log (1024 / 1325) := by
    rw [show ((1325 / 1024) : ℝ) = ((1024 / 1325) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (348062583 / 1000000000) ≤ -Real.log (723 / 1024) ∧
    -Real.log (723 / 1024) ≤ (43507823 / 125000000) := by
  have h := checkLog_sound (w := (301 / 1747)) (n := 12)
    (lo := (348062583 / 1000000000)) (hi := (43507823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 723) = 1/(723 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-43507823 / 125000000) (-348062583 / 1000000000) (Real.log (723 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (257243 / 1000000) ≤ -Real.log (2560 / 3311) ∧
    -Real.log (2560 / 3311) ≤ (257243001 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 5871)) (n := 12)
    (lo := (257243 / 1000000)) (hi := (257243001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3311 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3311 / 2560) = 1/(2560 / 3311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (257243 / 1000000) (257243001 / 1000000000) (Real.log (3311 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3311 / 2560) = -Real.log (2560 / 3311) := by
    rw [show ((3311 / 2560) : ℝ) = ((2560 / 3311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86808263 / 250000000) ≤ -Real.log (1809 / 2560) ∧
    -Real.log (1809 / 2560) ≤ (347233053 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 4369)) (n := 12)
    (lo := (86808263 / 250000000)) (hi := (347233053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1809) = 1/(1809 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-347233053 / 1000000000) (-86808263 / 250000000) (Real.log (1809 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (94568721 / 500000000) ≤ -Real.log (1000000 / 1208207) ∧
    -Real.log (1000000 / 1208207) ≤ (189137443 / 1000000000) := by
  have h := checkLog_sound (w := (208207 / 2208207)) (n := 12)
    (lo := (94568721 / 500000000)) (hi := (189137443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208207 / 1000000) = 1/(1000000 / 1208207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (94568721 / 500000000) (189137443 / 1000000000) (Real.log (1208207 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1208207 / 1000000) = -Real.log (1000000 / 1208207) := by
    rw [show ((1208207 / 1000000) : ℝ) = ((1000000 / 1208207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58363821 / 250000000) ≤ -Real.log (791793 / 1000000) ∧
    -Real.log (791793 / 1000000) ≤ (46691057 / 200000000) := by
  have h := checkLog_sound (w := (208207 / 1791793)) (n := 12)
    (lo := (58363821 / 250000000)) (hi := (46691057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791793) = 1/(791793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-46691057 / 200000000) (-58363821 / 250000000) (Real.log (791793 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (189485831 / 1000000000) ≤ -Real.log (250000 / 302157) ∧
    -Real.log (250000 / 302157) ≤ (23685729 / 125000000) := by
  have h := checkLog_sound (w := (52157 / 552157)) (n := 12)
    (lo := (189485831 / 1000000000)) (hi := (23685729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302157 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302157 / 250000) = 1/(250000 / 302157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (189485831 / 1000000000) (23685729 / 125000000) (Real.log (302157 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (302157 / 250000) = -Real.log (250000 / 302157) := by
    rw [show ((302157 / 250000) : ℝ) = ((250000 / 302157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (23398713 / 100000000) ≤ -Real.log (197843 / 250000) ∧
    -Real.log (197843 / 250000) ≤ (233987131 / 1000000000) := by
  have h := checkLog_sound (w := (52157 / 447843)) (n := 12)
    (lo := (23398713 / 100000000)) (hi := (233987131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197843) = 1/(197843 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-233987131 / 1000000000) (-23398713 / 100000000) (Real.log (197843 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (138905053 / 1000000000) ≤ -Real.log (200000 / 229803) ∧
    -Real.log (200000 / 229803) ≤ (69452527 / 500000000) := by
  have h := checkLog_sound (w := (29803 / 429803)) (n := 12)
    (lo := (138905053 / 1000000000)) (hi := (69452527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229803 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229803 / 200000) = 1/(200000 / 229803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (138905053 / 1000000000) (69452527 / 500000000) (Real.log (229803 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (229803 / 200000) = -Real.log (200000 / 229803) := by
    rw [show ((229803 / 200000) : ℝ) = ((200000 / 229803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (20170097 / 125000000) ≤ -Real.log (170197 / 200000) ∧
    -Real.log (170197 / 200000) ≤ (161360777 / 1000000000) := by
  have h := checkLog_sound (w := (29803 / 370197)) (n := 12)
    (lo := (20170097 / 125000000)) (hi := (161360777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 170197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 170197) = 1/(170197 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-161360777 / 1000000000) (-20170097 / 125000000) (Real.log (170197 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139173073 / 1000000000) ≤ -Real.log (1000000 / 1149323) ∧
    -Real.log (1000000 / 1149323) ≤ (69586537 / 500000000) := by
  have h := checkLog_sound (w := (149323 / 2149323)) (n := 12)
    (lo := (139173073 / 1000000000)) (hi := (69586537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149323 / 1000000) = 1/(1000000 / 1149323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139173073 / 1000000000) (69586537 / 500000000) (Real.log (1149323 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1149323 / 1000000) = -Real.log (1000000 / 1149323) := by
    rw [show ((1149323 / 1000000) : ℝ) = ((1000000 / 1149323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6468911 / 40000000) ≤ -Real.log (850677 / 1000000) ∧
    -Real.log (850677 / 1000000) ≤ (20215347 / 125000000) := by
  have h := checkLog_sound (w := (149323 / 1850677)) (n := 12)
    (lo := (6468911 / 40000000)) (hi := (20215347 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850677) = 1/(850677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-20215347 / 125000000) (-6468911 / 40000000) (Real.log (850677 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (151119013 / 250000000) ≤ -Real.log (500000000000 / 915146489773) ∧
    -Real.log (500000000000 / 915146489773) ≤ (604476053 / 1000000000) := by
  have h := checkLog_sound (w := (415146489773 / 1415146489773)) (n := 12)
    (lo := (151119013 / 250000000)) (hi := (604476053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915146489773 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915146489773 / 500000000000) = 1/(500000000000 / 915146489773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (151119013 / 250000000) (604476053 / 1000000000) (Real.log (915146489773 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (915146489773 / 500000000000) = -Real.log (500000000000 / 915146489773) := by
    rw [show ((915146489773 / 500000000000) : ℝ) = ((500000000000 / 915146489773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (151439629 / 250000000) ≤ -Real.log (500000000000 / 916320885201) ∧
    -Real.log (500000000000 / 916320885201) ≤ (605758517 / 1000000000) := by
  have h := checkLog_sound (w := (416320885201 / 1416320885201)) (n := 12)
    (lo := (151439629 / 250000000)) (hi := (605758517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((916320885201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(916320885201 / 500000000000) = 1/(500000000000 / 916320885201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (151439629 / 250000000) (605758517 / 1000000000) (Real.log (916320885201 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (916320885201 / 500000000000) = -Real.log (500000000000 / 916320885201) := by
    rw [show ((916320885201 / 500000000000) : ℝ) = ((500000000000 / 916320885201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (422592727 / 1000000000) ≤ -Real.log (500000000000 / 762956353491) ∧
    -Real.log (500000000000 / 762956353491) ≤ (52824091 / 125000000) := by
  have h := checkLog_sound (w := (262956353491 / 1262956353491)) (n := 12)
    (lo := (422592727 / 1000000000)) (hi := (52824091 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762956353491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762956353491 / 500000000000) = 1/(500000000000 / 762956353491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (422592727 / 1000000000) (52824091 / 125000000) (Real.log (762956353491 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (762956353491 / 500000000000) = -Real.log (500000000000 / 762956353491) := by
    rw [show ((762956353491 / 500000000000) : ℝ) = ((500000000000 / 762956353491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (211736481 / 500000000) ≤ -Real.log (250000000000 / 381814115233) ∧
    -Real.log (250000000000 / 381814115233) ≤ (423472963 / 1000000000) := by
  have h := checkLog_sound (w := (131814115233 / 631814115233)) (n := 12)
    (lo := (211736481 / 500000000)) (hi := (423472963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381814115233 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381814115233 / 250000000000) = 1/(250000000000 / 381814115233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (211736481 / 500000000) (423472963 / 1000000000) (Real.log (381814115233 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (381814115233 / 250000000000) = -Real.log (250000000000 / 381814115233) := by
    rw [show ((381814115233 / 250000000000) : ℝ) = ((250000000000 / 381814115233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (30026583 / 100000000) ≤ -Real.log (62500000000 / 84388605557) ∧
    -Real.log (62500000000 / 84388605557) ≤ (300265831 / 1000000000) := by
  have h := checkLog_sound (w := (21888605557 / 146888605557)) (n := 12)
    (lo := (30026583 / 100000000)) (hi := (300265831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84388605557 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84388605557 / 62500000000) = 1/(62500000000 / 84388605557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (30026583 / 100000000) (300265831 / 1000000000) (Real.log (84388605557 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (84388605557 / 62500000000) = -Real.log (62500000000 / 84388605557) := by
    rw [show ((84388605557 / 62500000000) : ℝ) = ((62500000000 / 84388605557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (300895849 / 1000000000) ≤ -Real.log (500000000000 / 675534309733) ∧
    -Real.log (500000000000 / 675534309733) ≤ (6017917 / 20000000) := by
  have h := checkLog_sound (w := (175534309733 / 1175534309733)) (n := 12)
    (lo := (300895849 / 1000000000)) (hi := (6017917 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675534309733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675534309733 / 500000000000) = 1/(500000000000 / 675534309733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (300895849 / 1000000000) (6017917 / 20000000) (Real.log (675534309733 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (675534309733 / 500000000000) = -Real.log (500000000000 / 675534309733) := by
    rw [show ((675534309733 / 500000000000) : ℝ) = ((500000000000 / 675534309733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (11274851 / 500000000) ≤ -Real.log (977702641671 / 1000000000000) ∧
    -Real.log (977702641671 / 1000000000000) ≤ (22549703 / 1000000000) := by
  have h := checkLog_sound (w := (22297358329 / 1977702641671)) (n := 12)
    (lo := (11274851 / 500000000)) (hi := (22549703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977702641671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977702641671) = 1/(977702641671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-22549703 / 1000000000) (-11274851 / 500000000) (Real.log (977702641671 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (22455723 / 1000000000) ≤ -Real.log (39111781191 / 40000000000) ∧
    -Real.log (39111781191 / 40000000000) ≤ (5613931 / 250000000) := by
  have h := checkLog_sound (w := (888218809 / 79111781191)) (n := 12)
    (lo := (22455723 / 1000000000)) (hi := (5613931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39111781191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39111781191) = 1/(39111781191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5613931 / 250000000) (-22455723 / 1000000000) (Real.log (39111781191 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell074

end


