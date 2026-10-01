-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0135Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0135Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:34:33.656703+00:00
-- url     : https://prove2.me/theorems/8ecfa6a2-94ce-4c63-bb11-4a31cbbc32ca
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0135Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0136Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0135Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0136Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0137Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0138Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0139Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0140Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0135Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0136Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0137Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0138Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0139Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0140Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0135Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0136Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0137Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0138Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0139Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0140Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0135Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0136Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0137Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0138Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0139Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0140Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0135Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0135
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

theorem reflection_log_1_neg : (758927 / 2500000) ≤ -Real.log (640 / 867) ∧
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


theorem reflection_log_1 : Bounds (758927 / 2500000) (303570801 / 1000000000) (Real.log (867 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (867 / 640) = -Real.log (640 / 867) := by
    rw [show ((867 / 640) : ℝ) = ((640 / 867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (438020583 / 1000000000) ≤ -Real.log (413 / 640) ∧
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


theorem reflection_log_2 : Bounds (-54752573 / 125000000) (-438020583 / 1000000000) (Real.log (413 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (151352687 / 500000000) ≤ -Real.log (512 / 693) ∧
    -Real.log (512 / 693) ≤ (2421643 / 8000000) := by
  have h := checkLog_sound (w := (181 / 1205)) (n := 12)
    (lo := (151352687 / 500000000)) (hi := (2421643 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693 / 512) = 1/(512 / 693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (151352687 / 500000000) (2421643 / 8000000) (Real.log (693 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (693 / 512) = -Real.log (512 / 693) := by
    rw [show ((693 / 512) : ℝ) = ((512 / 693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (436206249 / 1000000000) ≤ -Real.log (331 / 512) ∧
    -Real.log (331 / 512) ≤ (69793 / 160000) := by
  have h := checkLog_sound (w := (181 / 843)) (n := 12)
    (lo := (436206249 / 1000000000)) (hi := (69793 / 160000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 331) = 1/(331 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-69793 / 160000) (-436206249 / 1000000000) (Real.log (331 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (268063903 / 500000000) ≤ -Real.log (320 / 547) ∧
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


theorem reflection_log_5 : Bounds (268063903 / 500000000) (536127807 / 1000000000) (Real.log (547 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (547 / 320) = -Real.log (320 / 547) := by
    rw [show ((547 / 320) : ℝ) = ((320 / 547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (617860751 / 500000000) ≤ -Real.log (93 / 320) ∧
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


theorem reflection_log_6 : Bounds (-38616297 / 31250000) (-617860751 / 500000000) (Real.log (93 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2139023 / 4000000) ≤ -Real.log (256 / 437) ∧
    -Real.log (256 / 437) ≤ (534755751 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 693)) (n := 12)
    (lo := (2139023 / 4000000)) (hi := (534755751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437 / 256) = 1/(256 / 437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2139023 / 4000000) (534755751 / 1000000000) (Real.log (437 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (437 / 256) = -Real.log (256 / 437) := by
    rw [show ((437 / 256) : ℝ) = ((256 / 437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (122768933 / 100000000) ≤ -Real.log (75 / 256) ∧
    -Real.log (75 / 256) ≤ (306922333 / 250000000) := by
  have h := checkLog_sound (w := (53 / 203)) (n := 12)
    (lo := (10690843 / 20000000)) (hi := (534542151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 75) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 75) = 1/(75 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-306922333 / 250000000) (-122768933 / 100000000) (Real.log (75 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (414357453 / 1000000000) ≤ -Real.log (500000 / 756699) ∧
    -Real.log (500000 / 756699) ≤ (207178727 / 500000000) := by
  have h := checkLog_sound (w := (256699 / 1256699)) (n := 12)
    (lo := (414357453 / 1000000000)) (hi := (207178727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((756699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(756699 / 500000) = 1/(500000 / 756699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (414357453 / 1000000000) (207178727 / 500000000) (Real.log (756699 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (756699 / 500000) = -Real.log (500000 / 756699) := by
    rw [show ((756699 / 500000) : ℝ) = ((500000 / 756699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (720308737 / 1000000000) ≤ -Real.log (243301 / 500000) ∧
    -Real.log (243301 / 500000) ≤ (720308739 / 1000000000) := by
  have h := checkLog_sound (w := (6699 / 493301)) (n := 12)
    (lo := (27161557 / 1000000000)) (hi := (13580779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 243301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 243301) = 1/(243301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-720308739 / 1000000000) (-720308737 / 1000000000) (Real.log (243301 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (207780651 / 500000000) ≤ -Real.log (1000000 / 1515221) ∧
    -Real.log (1000000 / 1515221) ≤ (415561303 / 1000000000) := by
  have h := checkLog_sound (w := (515221 / 2515221)) (n := 12)
    (lo := (207780651 / 500000000)) (hi := (415561303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1515221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1515221 / 1000000) = 1/(1000000 / 1515221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (207780651 / 500000000) (415561303 / 1000000000) (Real.log (1515221 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1515221 / 1000000) = -Real.log (1000000 / 1515221) := by
    rw [show ((1515221 / 1000000) : ℝ) = ((1000000 / 1515221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (724062161 / 1000000000) ≤ -Real.log (484779 / 1000000) ∧
    -Real.log (484779 / 1000000) ≤ (724062163 / 1000000000) := by
  have h := checkLog_sound (w := (15221 / 984779)) (n := 12)
    (lo := (30914981 / 1000000000)) (hi := (15457491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 484779) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 484779) = 1/(484779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-724062163 / 1000000000) (-724062161 / 1000000000) (Real.log (484779 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10323863 / 31250000) ≤ -Real.log (500000 / 695737) ∧
    -Real.log (500000 / 695737) ≤ (330363617 / 1000000000) := by
  have h := checkLog_sound (w := (195737 / 1195737)) (n := 12)
    (lo := (10323863 / 31250000)) (hi := (330363617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695737 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695737 / 500000) = 1/(500000 / 695737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10323863 / 31250000) (330363617 / 1000000000) (Real.log (695737 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (695737 / 500000) = -Real.log (500000 / 695737) := by
    rw [show ((695737 / 500000) : ℝ) = ((500000 / 695737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (496715639 / 1000000000) ≤ -Real.log (304263 / 500000) ∧
    -Real.log (304263 / 500000) ≤ (12417891 / 25000000) := by
  have h := checkLog_sound (w := (195737 / 804263)) (n := 12)
    (lo := (496715639 / 1000000000)) (hi := (12417891 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 304263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 304263) = 1/(304263 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-12417891 / 25000000) (-496715639 / 1000000000) (Real.log (304263 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4143973 / 12500000) ≤ -Real.log (1000000 / 1393081) ∧
    -Real.log (1000000 / 1393081) ≤ (331517841 / 1000000000) := by
  have h := checkLog_sound (w := (393081 / 2393081)) (n := 12)
    (lo := (4143973 / 12500000)) (hi := (331517841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393081 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1393081 / 1000000) = 1/(1000000 / 1393081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4143973 / 12500000) (331517841 / 1000000000) (Real.log (1393081 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1393081 / 1000000) = -Real.log (1000000 / 1393081) := by
    rw [show ((1393081 / 1000000) : ℝ) = ((1000000 / 1393081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (499359939 / 1000000000) ≤ -Real.log (606919 / 1000000) ∧
    -Real.log (606919 / 1000000) ≤ (24967997 / 50000000) := by
  have h := checkLog_sound (w := (393081 / 1606919)) (n := 12)
    (lo := (499359939 / 1000000000)) (hi := (24967997 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 606919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 606919) = 1/(606919 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-24967997 / 50000000) (-499359939 / 1000000000) (Real.log (606919 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1134666191 / 1000000000) ≤ -Real.log (500000000000 / 1555067591173) ∧
    -Real.log (500000000000 / 1555067591173) ≤ (1134666193 / 1000000000) := by
  have h := checkLog_sound (w := (555067591173 / 2555067591173)) (n := 12)
    (lo := (441519011 / 1000000000)) (hi := (110379753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1555067591173 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1555067591173 / 1000000000000) = 1/(500000000000 / 1555067591173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1134666191 / 1000000000) (1134666193 / 1000000000) (Real.log (1555067591173 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1555067591173 / 500000000000) = -Real.log (500000000000 / 1555067591173) := by
    rw [show ((1555067591173 / 500000000000) : ℝ) = ((500000000000 / 1555067591173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (142452933 / 125000000) ≤ -Real.log (250000000000 / 781397812199) ∧
    -Real.log (250000000000 / 781397812199) ≤ (569811733 / 500000000) := by
  have h := checkLog_sound (w := (281397812199 / 1281397812199)) (n := 12)
    (lo := (111619071 / 250000000)) (hi := (89295257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781397812199 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(781397812199 / 500000000000) = 1/(250000000000 / 781397812199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (142452933 / 125000000) (569811733 / 500000000) (Real.log (781397812199 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (781397812199 / 250000000000) = -Real.log (250000000000 / 781397812199) := by
    rw [show ((781397812199 / 250000000000) : ℝ) = ((250000000000 / 781397812199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (165415851 / 200000000) ≤ -Real.log (500000000000 / 1143315158267) ∧
    -Real.log (500000000000 / 1143315158267) ≤ (827079257 / 1000000000) := by
  have h := checkLog_sound (w := (143315158267 / 2143315158267)) (n := 12)
    (lo := (5357283 / 40000000)) (hi := (33483019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143315158267 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1143315158267 / 1000000000000) = 1/(500000000000 / 1143315158267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (165415851 / 200000000) (827079257 / 1000000000) (Real.log (1143315158267 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1143315158267 / 500000000000) = -Real.log (500000000000 / 1143315158267) := by
    rw [show ((1143315158267 / 500000000000) : ℝ) = ((500000000000 / 1143315158267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (41543889 / 50000000) ≤ -Real.log (500000000000 / 1147666327797) ∧
    -Real.log (500000000000 / 1147666327797) ≤ (415438891 / 500000000) := by
  have h := checkLog_sound (w := (147666327797 / 2147666327797)) (n := 12)
    (lo := (688653 / 5000000)) (hi := (137730601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147666327797 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1147666327797 / 1000000000000) = 1/(500000000000 / 1147666327797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (41543889 / 50000000) (415438891 / 500000000) (Real.log (1147666327797 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1147666327797 / 500000000000) = -Real.log (500000000000 / 1147666327797) := by
    rw [show ((1147666327797 / 500000000000) : ℝ) = ((500000000000 / 1147666327797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0135

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0136Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0136
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

theorem reflection_log_1_neg : (151352687 / 500000000) ≤ -Real.log (512 / 693) ∧
    -Real.log (512 / 693) ≤ (2421643 / 8000000) := by
  have h := checkLog_sound (w := (181 / 1205)) (n := 12)
    (lo := (151352687 / 500000000)) (hi := (2421643 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693 / 512) = 1/(512 / 693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (151352687 / 500000000) (2421643 / 8000000) (Real.log (693 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (693 / 512) = -Real.log (512 / 693) := by
    rw [show ((693 / 512) : ℝ) = ((512 / 693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (436206249 / 1000000000) ≤ -Real.log (331 / 512) ∧
    -Real.log (331 / 512) ≤ (69793 / 160000) := by
  have h := checkLog_sound (w := (181 / 843)) (n := 12)
    (lo := (436206249 / 1000000000)) (hi := (69793 / 160000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 331) = 1/(331 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-69793 / 160000) (-436206249 / 1000000000) (Real.log (331 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (150919599 / 500000000) ≤ -Real.log (1280 / 1731) ∧
    -Real.log (1280 / 1731) ≤ (301839199 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 3011)) (n := 12)
    (lo := (150919599 / 500000000)) (hi := (301839199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1731 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1731 / 1280) = 1/(1280 / 1731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (150919599 / 500000000) (301839199 / 1000000000) (Real.log (1731 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1731 / 1280) = -Real.log (1280 / 1731) := by
    rw [show ((1731 / 1280) : ℝ) = ((1280 / 1731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (434395201 / 1000000000) ≤ -Real.log (829 / 1280) ∧
    -Real.log (829 / 1280) ≤ (217197601 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2109)) (n := 12)
    (lo := (434395201 / 1000000000)) (hi := (217197601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 829) = 1/(829 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-217197601 / 500000000) (-434395201 / 1000000000) (Real.log (829 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2139023 / 4000000) ≤ -Real.log (256 / 437) ∧
    -Real.log (256 / 437) ≤ (534755751 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 693)) (n := 12)
    (lo := (2139023 / 4000000)) (hi := (534755751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437 / 256) = 1/(256 / 437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2139023 / 4000000) (534755751 / 1000000000) (Real.log (437 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (437 / 256) = -Real.log (256 / 437) := by
    rw [show ((437 / 256) : ℝ) = ((256 / 437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (122768933 / 100000000) ≤ -Real.log (75 / 256) ∧
    -Real.log (75 / 256) ≤ (306922333 / 250000000) := by
  have h := checkLog_sound (w := (53 / 203)) (n := 12)
    (lo := (10690843 / 20000000)) (hi := (534542151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 75) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 75) = 1/(75 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-306922333 / 250000000) (-122768933 / 100000000) (Real.log (75 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (533381809 / 1000000000) ≤ -Real.log (640 / 1091) ∧
    -Real.log (640 / 1091) ≤ (53338181 / 100000000) := by
  have h := checkLog_sound (w := (451 / 1731)) (n := 12)
    (lo := (533381809 / 1000000000)) (hi := (53338181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091 / 640) = 1/(640 / 1091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (533381809 / 1000000000) (53338181 / 100000000) (Real.log (1091 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1091 / 640) = -Real.log (640 / 1091) := by
    rw [show ((1091 / 640) : ℝ) = ((640 / 1091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (30493029 / 25000000) ≤ -Real.log (189 / 640) ∧
    -Real.log (189 / 640) ≤ (609860581 / 500000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 189) = 1/(189 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-609860581 / 500000000) (-30493029 / 25000000) (Real.log (189 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (413154799 / 1000000000) ≤ -Real.log (1000000 / 1511579) ∧
    -Real.log (1000000 / 1511579) ≤ (1032887 / 2500000) := by
  have h := checkLog_sound (w := (511579 / 2511579)) (n := 12)
    (lo := (413154799 / 1000000000)) (hi := (1032887 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511579 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511579 / 1000000) = 1/(1000000 / 1511579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (413154799 / 1000000000) (1032887 / 2500000) (Real.log (1511579 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1511579 / 1000000) = -Real.log (1000000 / 1511579) := by
    rw [show ((1511579 / 1000000) : ℝ) = ((1000000 / 1511579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (716577539 / 1000000000) ≤ -Real.log (488421 / 1000000) ∧
    -Real.log (488421 / 1000000) ≤ (716577541 / 1000000000) := by
  have h := checkLog_sound (w := (11579 / 988421)) (n := 12)
    (lo := (23430359 / 1000000000)) (hi := (585759 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 488421) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 488421) = 1/(488421 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-716577541 / 1000000000) (-716577539 / 1000000000) (Real.log (488421 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (207179057 / 500000000) ≤ -Real.log (1000000 / 1513399) ∧
    -Real.log (1000000 / 1513399) ≤ (82871623 / 200000000) := by
  have h := checkLog_sound (w := (513399 / 2513399)) (n := 12)
    (lo := (207179057 / 500000000)) (hi := (82871623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1513399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1513399 / 1000000) = 1/(1000000 / 1513399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (207179057 / 500000000) (82871623 / 200000000) (Real.log (1513399 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1513399 / 1000000) = -Real.log (1000000 / 1513399) := by
    rw [show ((1513399 / 1000000) : ℝ) = ((1000000 / 1513399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90038849 / 125000000) ≤ -Real.log (486601 / 1000000) ∧
    -Real.log (486601 / 1000000) ≤ (360155397 / 500000000) := by
  have h := checkLog_sound (w := (13399 / 986601)) (n := 12)
    (lo := (6790903 / 250000000)) (hi := (27163613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 486601) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 486601) = 1/(486601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-360155397 / 500000000) (-90038849 / 125000000) (Real.log (486601 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (41151547 / 125000000) ≤ -Real.log (1000000 / 1389873) ∧
    -Real.log (1000000 / 1389873) ≤ (329212377 / 1000000000) := by
  have h := checkLog_sound (w := (389873 / 2389873)) (n := 12)
    (lo := (41151547 / 125000000)) (hi := (329212377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1389873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1389873 / 1000000) = 1/(1000000 / 1389873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (41151547 / 125000000) (329212377 / 1000000000) (Real.log (1389873 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1389873 / 1000000) = -Real.log (1000000 / 1389873) := by
    rw [show ((1389873 / 1000000) : ℝ) = ((1000000 / 1389873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (247044073 / 500000000) ≤ -Real.log (610127 / 1000000) ∧
    -Real.log (610127 / 1000000) ≤ (494088147 / 1000000000) := by
  have h := checkLog_sound (w := (389873 / 1610127)) (n := 12)
    (lo := (247044073 / 500000000)) (hi := (494088147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 610127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 610127) = 1/(610127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-494088147 / 1000000000) (-247044073 / 500000000) (Real.log (610127 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (66072867 / 200000000) ≤ -Real.log (40000 / 55659) ∧
    -Real.log (40000 / 55659) ≤ (20647771 / 62500000) := by
  have h := checkLog_sound (w := (15659 / 95659)) (n := 12)
    (lo := (66072867 / 200000000)) (hi := (20647771 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55659 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55659 / 40000) = 1/(40000 / 55659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (66072867 / 200000000) (20647771 / 62500000) (Real.log (55659 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (55659 / 40000) = -Real.log (40000 / 55659) := by
    rw [show ((55659 / 40000) : ℝ) = ((40000 / 55659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (248358641 / 500000000) ≤ -Real.log (24341 / 40000) ∧
    -Real.log (24341 / 40000) ≤ (496717283 / 1000000000) := by
  have h := checkLog_sound (w := (15659 / 64341)) (n := 12)
    (lo := (248358641 / 500000000)) (hi := (496717283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 24341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 24341) = 1/(24341 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-496717283 / 1000000000) (-248358641 / 500000000) (Real.log (24341 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1129732339 / 1000000000) ≤ -Real.log (500000000000 / 1547414013729) ∧
    -Real.log (500000000000 / 1547414013729) ≤ (1129732341 / 1000000000) := by
  have h := checkLog_sound (w := (547414013729 / 2547414013729)) (n := 12)
    (lo := (436585159 / 1000000000)) (hi := (10914629 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547414013729 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1547414013729 / 1000000000000) = 1/(500000000000 / 1547414013729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1129732339 / 1000000000) (1129732341 / 1000000000) (Real.log (1547414013729 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1547414013729 / 500000000000) = -Real.log (500000000000 / 1547414013729) := by
    rw [show ((1547414013729 / 500000000000) : ℝ) = ((500000000000 / 1547414013729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1134668907 / 1000000000) ≤ -Real.log (100000000000 / 311014362897) ∧
    -Real.log (100000000000 / 311014362897) ≤ (1134668909 / 1000000000) := by
  have h := checkLog_sound (w := (111014362897 / 511014362897)) (n := 12)
    (lo := (441521727 / 1000000000)) (hi := (6898777 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311014362897 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(311014362897 / 200000000000) = 1/(100000000000 / 311014362897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1134668907 / 1000000000) (1134668909 / 1000000000) (Real.log (311014362897 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (311014362897 / 100000000000) = -Real.log (100000000000 / 311014362897) := by
    rw [show ((311014362897 / 100000000000) : ℝ) = ((100000000000 / 311014362897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (411650261 / 500000000) ≤ -Real.log (250000000000 / 569501513619) ∧
    -Real.log (250000000000 / 569501513619) ≤ (205825131 / 250000000) := by
  have h := checkLog_sound (w := (69501513619 / 1069501513619)) (n := 12)
    (lo := (65076671 / 500000000)) (hi := (130153343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569501513619 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(569501513619 / 500000000000) = 1/(250000000000 / 569501513619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (411650261 / 500000000) (205825131 / 250000000) (Real.log (569501513619 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (569501513619 / 250000000000) = -Real.log (250000000000 / 569501513619) := by
    rw [show ((569501513619 / 250000000000) : ℝ) = ((250000000000 / 569501513619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (827081617 / 1000000000) ≤ -Real.log (500000000000 / 1143317858757) ∧
    -Real.log (500000000000 / 1143317858757) ≤ (827081619 / 1000000000) := by
  have h := checkLog_sound (w := (143317858757 / 2143317858757)) (n := 12)
    (lo := (133934437 / 1000000000)) (hi := (66967219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143317858757 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1143317858757 / 1000000000000) = 1/(500000000000 / 1143317858757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (827081617 / 1000000000) (827081619 / 1000000000) (Real.log (1143317858757 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1143317858757 / 500000000000) = -Real.log (500000000000 / 1143317858757) := by
    rw [show ((1143317858757 / 500000000000) : ℝ) = ((500000000000 / 1143317858757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0136

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0137Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0137
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

theorem reflection_log_1_neg : (150919599 / 500000000) ≤ -Real.log (1280 / 1731) ∧
    -Real.log (1280 / 1731) ≤ (301839199 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 3011)) (n := 12)
    (lo := (150919599 / 500000000)) (hi := (301839199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1731 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1731 / 1280) = 1/(1280 / 1731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (150919599 / 500000000) (301839199 / 1000000000) (Real.log (1731 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1731 / 1280) = -Real.log (1280 / 1731) := by
    rw [show ((1731 / 1280) : ℝ) = ((1280 / 1731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (434395201 / 1000000000) ≤ -Real.log (829 / 1280) ∧
    -Real.log (829 / 1280) ≤ (217197601 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2109)) (n := 12)
    (lo := (434395201 / 1000000000)) (hi := (217197601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 829) = 1/(829 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-217197601 / 500000000) (-434395201 / 1000000000) (Real.log (829 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (300972271 / 1000000000) ≤ -Real.log (2560 / 3459) ∧
    -Real.log (2560 / 3459) ≤ (18810767 / 62500000) := by
  have h := checkLog_sound (w := (899 / 6019)) (n := 12)
    (lo := (300972271 / 1000000000)) (hi := (18810767 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3459 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3459 / 2560) = 1/(2560 / 3459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (300972271 / 1000000000) (18810767 / 62500000) (Real.log (3459 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3459 / 2560) = -Real.log (2560 / 3459) := by
    rw [show ((3459 / 2560) : ℝ) = ((2560 / 3459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (432587427 / 1000000000) ≤ -Real.log (1661 / 2560) ∧
    -Real.log (1661 / 2560) ≤ (108146857 / 250000000) := by
  have h := checkLog_sound (w := (899 / 4221)) (n := 12)
    (lo := (432587427 / 1000000000)) (hi := (108146857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1661) = 1/(1661 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-108146857 / 250000000) (-432587427 / 1000000000) (Real.log (1661 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (533381809 / 1000000000) ≤ -Real.log (640 / 1091) ∧
    -Real.log (640 / 1091) ≤ (53338181 / 100000000) := by
  have h := checkLog_sound (w := (451 / 1731)) (n := 12)
    (lo := (533381809 / 1000000000)) (hi := (53338181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091 / 640) = 1/(640 / 1091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (533381809 / 1000000000) (53338181 / 100000000) (Real.log (1091 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1091 / 640) = -Real.log (640 / 1091) := by
    rw [show ((1091 / 640) : ℝ) = ((640 / 1091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (30493029 / 25000000) ≤ -Real.log (189 / 640) ∧
    -Real.log (189 / 640) ≤ (609860581 / 500000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 189) = 1/(189 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-609860581 / 500000000) (-30493029 / 25000000) (Real.log (189 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (266002989 / 500000000) ≤ -Real.log (1280 / 2179) ∧
    -Real.log (1280 / 2179) ≤ (532005979 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 3459)) (n := 12)
    (lo := (266002989 / 500000000)) (hi := (532005979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2179 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2179 / 1280) = 1/(1280 / 2179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (266002989 / 500000000) (532005979 / 1000000000) (Real.log (2179 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2179 / 1280) = -Real.log (1280 / 2179) := by
    rw [show ((2179 / 1280) : ℝ) = ((1280 / 2179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1211815981 / 1000000000) ≤ -Real.log (381 / 1280) ∧
    -Real.log (381 / 1280) ≤ (1211815983 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1021)) (n := 12)
    (lo := (518668801 / 1000000000)) (hi := (259334401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 381) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 381) = 1/(381 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1211815983 / 1000000000) (-1211815981 / 1000000000) (Real.log (381 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (321837 / 781250) ≤ -Real.log (1000000 / 1509761) ∧
    -Real.log (1000000 / 1509761) ≤ (411951361 / 1000000000) := by
  have h := checkLog_sound (w := (509761 / 2509761)) (n := 12)
    (lo := (321837 / 781250)) (hi := (411951361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1509761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1509761 / 1000000) = 1/(1000000 / 1509761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (321837 / 781250) (411951361 / 1000000000) (Real.log (1509761 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1509761 / 1000000) = -Real.log (1000000 / 1509761) := by
    rw [show ((1509761 / 1000000) : ℝ) = ((1000000 / 1509761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (712862251 / 1000000000) ≤ -Real.log (490239 / 1000000) ∧
    -Real.log (490239 / 1000000) ≤ (712862253 / 1000000000) := by
  have h := checkLog_sound (w := (9761 / 990239)) (n := 12)
    (lo := (19715071 / 1000000000)) (hi := (38506 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 490239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 490239) = 1/(490239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-712862253 / 1000000000) (-712862251 / 1000000000) (Real.log (490239 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (413155461 / 1000000000) ≤ -Real.log (50000 / 75579) ∧
    -Real.log (50000 / 75579) ≤ (206577731 / 500000000) := by
  have h := checkLog_sound (w := (25579 / 125579)) (n := 12)
    (lo := (413155461 / 1000000000)) (hi := (206577731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75579 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75579 / 50000) = 1/(50000 / 75579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (413155461 / 1000000000) (206577731 / 500000000) (Real.log (75579 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (75579 / 50000) = -Real.log (50000 / 75579) := by
    rw [show ((75579 / 50000) : ℝ) = ((50000 / 75579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (358289793 / 500000000) ≤ -Real.log (24421 / 50000) ∧
    -Real.log (24421 / 50000) ≤ (179144897 / 250000000) := by
  have h := checkLog_sound (w := (579 / 49421)) (n := 12)
    (lo := (11716203 / 500000000)) (hi := (23432407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24421) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 24421) = 1/(24421 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-179144897 / 250000000) (-358289793 / 500000000) (Real.log (24421 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (328061969 / 1000000000) ≤ -Real.log (40000 / 55531) ∧
    -Real.log (40000 / 55531) ≤ (32806197 / 100000000) := by
  have h := checkLog_sound (w := (15531 / 95531)) (n := 12)
    (lo := (328061969 / 1000000000)) (hi := (32806197 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55531 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55531 / 40000) = 1/(40000 / 55531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (328061969 / 1000000000) (32806197 / 100000000) (Real.log (55531 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (55531 / 40000) = -Real.log (40000 / 55531) := by
    rw [show ((55531 / 40000) : ℝ) = ((40000 / 55531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (491472443 / 1000000000) ≤ -Real.log (24469 / 40000) ∧
    -Real.log (24469 / 40000) ≤ (122868111 / 250000000) := by
  have h := checkLog_sound (w := (15531 / 64469)) (n := 12)
    (lo := (491472443 / 1000000000)) (hi := (122868111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 24469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 24469) = 1/(24469 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-122868111 / 250000000) (-491472443 / 1000000000) (Real.log (24469 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (65842619 / 200000000) ≤ -Real.log (500000 / 694937) ∧
    -Real.log (500000 / 694937) ≤ (41151637 / 125000000) := by
  have h := checkLog_sound (w := (194937 / 1194937)) (n := 12)
    (lo := (65842619 / 200000000)) (hi := (41151637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694937 / 500000) = 1/(500000 / 694937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (65842619 / 200000000) (41151637 / 125000000) (Real.log (694937 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (694937 / 500000) = -Real.log (500000 / 694937) := by
    rw [show ((694937 / 500000) : ℝ) = ((500000 / 694937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (98817957 / 200000000) ≤ -Real.log (305063 / 500000) ∧
    -Real.log (305063 / 500000) ≤ (247044893 / 500000000) := by
  have h := checkLog_sound (w := (194937 / 805063)) (n := 12)
    (lo := (98817957 / 200000000)) (hi := (247044893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 305063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 305063) = 1/(305063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-247044893 / 500000000) (-98817957 / 200000000) (Real.log (305063 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1124813611 / 1000000000) ≤ -Real.log (250000000000 / 769910696619) ∧
    -Real.log (250000000000 / 769910696619) ≤ (1124813613 / 1000000000) := by
  have h := checkLog_sound (w := (269910696619 / 1269910696619)) (n := 12)
    (lo := (431666431 / 1000000000)) (hi := (1686197 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769910696619 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(769910696619 / 500000000000) = 1/(250000000000 / 769910696619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1124813611 / 1000000000) (1124813613 / 1000000000) (Real.log (769910696619 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (769910696619 / 250000000000) = -Real.log (250000000000 / 769910696619) := by
    rw [show ((769910696619 / 250000000000) : ℝ) = ((250000000000 / 769910696619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (141216881 / 125000000) ≤ -Real.log (500000000000 / 1547418205643) ∧
    -Real.log (500000000000 / 1547418205643) ≤ (22594701 / 20000000) := by
  have h := checkLog_sound (w := (547418205643 / 2547418205643)) (n := 12)
    (lo := (109146967 / 250000000)) (hi := (436587869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547418205643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1547418205643 / 1000000000000) = 1/(500000000000 / 1547418205643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (141216881 / 125000000) (22594701 / 20000000) (Real.log (1547418205643 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1547418205643 / 500000000000) = -Real.log (500000000000 / 1547418205643) := by
    rw [show ((1547418205643 / 500000000000) : ℝ) = ((500000000000 / 1547418205643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (204883603 / 250000000) ≤ -Real.log (500000000000 / 1134721484327) ∧
    -Real.log (500000000000 / 1134721484327) ≤ (409767207 / 500000000) := by
  have h := checkLog_sound (w := (134721484327 / 2134721484327)) (n := 12)
    (lo := (3949601 / 31250000)) (hi := (126387233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134721484327 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1134721484327 / 1000000000000) = 1/(500000000000 / 1134721484327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (204883603 / 250000000) (409767207 / 500000000) (Real.log (1134721484327 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1134721484327 / 500000000000) = -Real.log (500000000000 / 1134721484327) := by
    rw [show ((1134721484327 / 500000000000) : ℝ) = ((500000000000 / 1134721484327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (5145643 / 6250000) ≤ -Real.log (250000000000 / 569502856787) ∧
    -Real.log (250000000000 / 569502856787) ≤ (411651441 / 500000000) := by
  have h := checkLog_sound (w := (69502856787 / 1069502856787)) (n := 12)
    (lo := (1301557 / 10000000)) (hi := (130155701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569502856787 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(569502856787 / 500000000000) = 1/(250000000000 / 569502856787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (5145643 / 6250000) (411651441 / 500000000) (Real.log (569502856787 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (569502856787 / 250000000000) = -Real.log (250000000000 / 569502856787) := by
    rw [show ((569502856787 / 250000000000) : ℝ) = ((250000000000 / 569502856787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0137

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0138Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0138
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

theorem reflection_log_1_neg : (300972271 / 1000000000) ≤ -Real.log (2560 / 3459) ∧
    -Real.log (2560 / 3459) ≤ (18810767 / 62500000) := by
  have h := checkLog_sound (w := (899 / 6019)) (n := 12)
    (lo := (300972271 / 1000000000)) (hi := (18810767 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3459 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3459 / 2560) = 1/(2560 / 3459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (300972271 / 1000000000) (18810767 / 62500000) (Real.log (3459 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3459 / 2560) = -Real.log (2560 / 3459) := by
    rw [show ((3459 / 2560) : ℝ) = ((2560 / 3459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (432587427 / 1000000000) ≤ -Real.log (1661 / 2560) ∧
    -Real.log (1661 / 2560) ≤ (108146857 / 250000000) := by
  have h := checkLog_sound (w := (899 / 4221)) (n := 12)
    (lo := (432587427 / 1000000000)) (hi := (108146857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1661) = 1/(1661 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-108146857 / 250000000) (-432587427 / 1000000000) (Real.log (1661 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (18756537 / 62500000) ≤ -Real.log (20 / 27) ∧
    -Real.log (20 / 27) ≤ (300104593 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 47)) (n := 12)
    (lo := (18756537 / 62500000)) (hi := (300104593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27 / 20) = 1/(20 / 27) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (18756537 / 62500000) (300104593 / 1000000000) (Real.log (27 / 20)) := by
  have h := reflection_log_3_neg
  have he : Real.log (27 / 20) = -Real.log (20 / 27) := by
    rw [show ((27 / 20) : ℝ) = ((20 / 27) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (107695729 / 250000000) ≤ -Real.log (13 / 20) ∧
    -Real.log (13 / 20) ≤ (430782917 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 13) = 1/(13 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-430782917 / 1000000000) (-107695729 / 250000000) (Real.log (13 / 20)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (266002989 / 500000000) ≤ -Real.log (1280 / 2179) ∧
    -Real.log (1280 / 2179) ≤ (532005979 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 3459)) (n := 12)
    (lo := (266002989 / 500000000)) (hi := (532005979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2179 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2179 / 1280) = 1/(1280 / 2179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (266002989 / 500000000) (532005979 / 1000000000) (Real.log (2179 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2179 / 1280) = -Real.log (1280 / 2179) := by
    rw [show ((2179 / 1280) : ℝ) = ((1280 / 2179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1211815981 / 1000000000) ≤ -Real.log (381 / 1280) ∧
    -Real.log (381 / 1280) ≤ (1211815983 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1021)) (n := 12)
    (lo := (518668801 / 1000000000)) (hi := (259334401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 381) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 381) = 1/(381 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1211815983 / 1000000000) (-1211815981 / 1000000000) (Real.log (381 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (530628251 / 1000000000) ≤ -Real.log (10 / 17) ∧
    -Real.log (10 / 17) ≤ (132657063 / 250000000) := by
  have h := checkLog_sound (w := (7 / 27)) (n := 12)
    (lo := (530628251 / 1000000000)) (hi := (132657063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17 / 10) = 1/(10 / 17) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (530628251 / 1000000000) (132657063 / 250000000) (Real.log (17 / 10)) := by
  have h := reflection_log_7_neg
  have he : Real.log (17 / 10) = -Real.log (10 / 17) := by
    rw [show ((17 / 10) : ℝ) = ((10 / 17) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1203972803 / 1000000000) ≤ -Real.log (3 / 10) ∧
    -Real.log (3 / 10) ≤ (240794561 / 200000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5 / 3) = 1/(3 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-240794561 / 200000000) (-1203972803 / 1000000000) (Real.log (3 / 10)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (102686949 / 250000000) ≤ -Real.log (200000 / 301589) ∧
    -Real.log (200000 / 301589) ≤ (410747797 / 1000000000) := by
  have h := checkLog_sound (w := (101589 / 501589)) (n := 12)
    (lo := (102686949 / 250000000)) (hi := (410747797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301589 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301589 / 200000) = 1/(200000 / 301589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (102686949 / 250000000) (410747797 / 1000000000) (Real.log (301589 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (301589 / 200000) = -Real.log (200000 / 301589) := by
    rw [show ((301589 / 200000) : ℝ) = ((200000 / 301589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (709164779 / 1000000000) ≤ -Real.log (98411 / 200000) ∧
    -Real.log (98411 / 200000) ≤ (709164781 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 198411)) (n := 12)
    (lo := (16017599 / 1000000000)) (hi := (10011 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 98411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 98411) = 1/(98411 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-709164781 / 1000000000) (-709164779 / 1000000000) (Real.log (98411 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (205976011 / 500000000) ≤ -Real.log (500000 / 754881) ∧
    -Real.log (500000 / 754881) ≤ (411952023 / 1000000000) := by
  have h := checkLog_sound (w := (254881 / 1254881)) (n := 12)
    (lo := (205976011 / 500000000)) (hi := (411952023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754881 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754881 / 500000) = 1/(500000 / 754881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (205976011 / 500000000) (411952023 / 1000000000) (Real.log (754881 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (754881 / 500000) = -Real.log (500000 / 754881) := by
    rw [show ((754881 / 500000) : ℝ) = ((500000 / 754881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (71286429 / 100000000) ≤ -Real.log (245119 / 500000) ∧
    -Real.log (245119 / 500000) ≤ (178216073 / 250000000) := by
  have h := checkLog_sound (w := (4881 / 495119)) (n := 12)
    (lo := (1971711 / 100000000)) (hi := (19717111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 245119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 245119) = 1/(245119 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-178216073 / 250000000) (-71286429 / 100000000) (Real.log (245119 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (163456561 / 500000000) ≤ -Real.log (1000000 / 1386681) ∧
    -Real.log (1000000 / 1386681) ≤ (326913123 / 1000000000) := by
  have h := checkLog_sound (w := (386681 / 2386681)) (n := 12)
    (lo := (163456561 / 500000000)) (hi := (326913123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1386681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1386681 / 1000000) = 1/(1000000 / 1386681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (163456561 / 500000000) (326913123 / 1000000000) (Real.log (1386681 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1386681 / 1000000) = -Real.log (1000000 / 1386681) := by
    rw [show ((1386681 / 1000000) : ℝ) = ((1000000 / 1386681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (244435043 / 500000000) ≤ -Real.log (613319 / 1000000) ∧
    -Real.log (613319 / 1000000) ≤ (488870087 / 1000000000) := by
  have h := checkLog_sound (w := (386681 / 1613319)) (n := 12)
    (lo := (244435043 / 500000000)) (hi := (488870087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 613319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 613319) = 1/(613319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-488870087 / 1000000000) (-244435043 / 500000000) (Real.log (613319 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (328062689 / 1000000000) ≤ -Real.log (250000 / 347069) ∧
    -Real.log (250000 / 347069) ≤ (32806269 / 100000000) := by
  have h := checkLog_sound (w := (97069 / 597069)) (n := 12)
    (lo := (328062689 / 1000000000)) (hi := (32806269 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347069 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347069 / 250000) = 1/(250000 / 347069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (328062689 / 1000000000) (32806269 / 100000000) (Real.log (347069 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (347069 / 250000) = -Real.log (250000 / 347069) := by
    rw [show ((347069 / 250000) : ℝ) = ((250000 / 347069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (245737039 / 500000000) ≤ -Real.log (152931 / 250000) ∧
    -Real.log (152931 / 250000) ≤ (491474079 / 1000000000) := by
  have h := checkLog_sound (w := (97069 / 402931)) (n := 12)
    (lo := (245737039 / 500000000)) (hi := (491474079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 152931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 152931) = 1/(152931 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-491474079 / 1000000000) (-245737039 / 500000000) (Real.log (152931 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (8749317 / 7812500) ≤ -Real.log (250000000000 / 766146568981) ∧
    -Real.log (250000000000 / 766146568981) ≤ (559956289 / 500000000) := by
  have h := checkLog_sound (w := (266146568981 / 1266146568981)) (n := 12)
    (lo := (106691349 / 250000000)) (hi := (426765397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766146568981 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(766146568981 / 500000000000) = 1/(250000000000 / 766146568981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (8749317 / 7812500) (559956289 / 500000000) (Real.log (766146568981 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (766146568981 / 250000000000) = -Real.log (250000000000 / 766146568981) := by
    rw [show ((766146568981 / 250000000000) : ℝ) = ((250000000000 / 766146568981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1124816313 / 1000000000) ≤ -Real.log (500000000000 / 1539825554119) ∧
    -Real.log (500000000000 / 1539825554119) ≤ (224963263 / 200000000) := by
  have h := checkLog_sound (w := (539825554119 / 2539825554119)) (n := 12)
    (lo := (431669133 / 1000000000)) (hi := (215834567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539825554119 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1539825554119 / 1000000000000) = 1/(500000000000 / 1539825554119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1124816313 / 1000000000) (224963263 / 200000000) (Real.log (1539825554119 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1539825554119 / 500000000000) = -Real.log (500000000000 / 1539825554119) := by
    rw [show ((1539825554119 / 500000000000) : ℝ) = ((500000000000 / 1539825554119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (101972901 / 125000000) ≤ -Real.log (500000000000 / 1130472886051) ∧
    -Real.log (500000000000 / 1130472886051) ≤ (81578321 / 100000000) := by
  have h := checkLog_sound (w := (130472886051 / 2130472886051)) (n := 12)
    (lo := (30659007 / 250000000)) (hi := (122636029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130472886051 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1130472886051 / 1000000000000) = 1/(500000000000 / 1130472886051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (101972901 / 125000000) (81578321 / 100000000) (Real.log (1130472886051 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1130472886051 / 500000000000) = -Real.log (500000000000 / 1130472886051) := by
    rw [show ((1130472886051 / 500000000000) : ℝ) = ((500000000000 / 1130472886051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (819536767 / 1000000000) ≤ -Real.log (250000000000 / 567362078323) ∧
    -Real.log (250000000000 / 567362078323) ≤ (819536769 / 1000000000) := by
  have h := checkLog_sound (w := (67362078323 / 1067362078323)) (n := 12)
    (lo := (126389587 / 1000000000)) (hi := (31597397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567362078323 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(567362078323 / 500000000000) = 1/(250000000000 / 567362078323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (819536767 / 1000000000) (819536769 / 1000000000) (Real.log (567362078323 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (567362078323 / 250000000000) = -Real.log (250000000000 / 567362078323) := by
    rw [show ((567362078323 / 250000000000) : ℝ) = ((250000000000 / 567362078323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0138

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0139Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0139
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

theorem reflection_log_1_neg : (18756537 / 62500000) ≤ -Real.log (20 / 27) ∧
    -Real.log (20 / 27) ≤ (300104593 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 47)) (n := 12)
    (lo := (18756537 / 62500000)) (hi := (300104593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27 / 20) = 1/(20 / 27) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (18756537 / 62500000) (300104593 / 1000000000) (Real.log (27 / 20)) := by
  have h := reflection_log_1_neg
  have he : Real.log (27 / 20) = -Real.log (20 / 27) := by
    rw [show ((27 / 20) : ℝ) = ((20 / 27) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (107695729 / 250000000) ≤ -Real.log (13 / 20) ∧
    -Real.log (13 / 20) ≤ (430782917 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 13) = 1/(13 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-430782917 / 1000000000) (-107695729 / 250000000) (Real.log (13 / 20)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (299236159 / 1000000000) ≤ -Real.log (2560 / 3453) ∧
    -Real.log (2560 / 3453) ≤ (935113 / 3125000) := by
  have h := checkLog_sound (w := (893 / 6013)) (n := 12)
    (lo := (299236159 / 1000000000)) (hi := (935113 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3453 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3453 / 2560) = 1/(2560 / 3453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (299236159 / 1000000000) (935113 / 3125000) (Real.log (3453 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3453 / 2560) = -Real.log (2560 / 3453) := by
    rw [show ((3453 / 2560) : ℝ) = ((2560 / 3453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (214490827 / 500000000) ≤ -Real.log (1667 / 2560) ∧
    -Real.log (1667 / 2560) ≤ (85796331 / 200000000) := by
  have h := checkLog_sound (w := (893 / 4227)) (n := 12)
    (lo := (214490827 / 500000000)) (hi := (85796331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1667) = 1/(1667 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-85796331 / 200000000) (-214490827 / 500000000) (Real.log (1667 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (530628251 / 1000000000) ≤ -Real.log (10 / 17) ∧
    -Real.log (10 / 17) ≤ (132657063 / 250000000) := by
  have h := checkLog_sound (w := (7 / 27)) (n := 12)
    (lo := (530628251 / 1000000000)) (hi := (132657063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17 / 10) = 1/(10 / 17) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (530628251 / 1000000000) (132657063 / 250000000) (Real.log (17 / 10)) := by
  have h := reflection_log_5_neg
  have he : Real.log (17 / 10) = -Real.log (10 / 17) := by
    rw [show ((17 / 10) : ℝ) = ((10 / 17) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1203972803 / 1000000000) ≤ -Real.log (3 / 10) ∧
    -Real.log (3 / 10) ≤ (240794561 / 200000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5 / 3) = 1/(3 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-240794561 / 200000000) (-1203972803 / 1000000000) (Real.log (3 / 10)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (529248623 / 1000000000) ≤ -Real.log (1280 / 2173) ∧
    -Real.log (1280 / 2173) ≤ (33078039 / 62500000) := by
  have h := checkLog_sound (w := (893 / 3453)) (n := 12)
    (lo := (529248623 / 1000000000)) (hi := (33078039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2173 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2173 / 1280) = 1/(1280 / 2173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (529248623 / 1000000000) (33078039 / 62500000) (Real.log (2173 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2173 / 1280) = -Real.log (1280 / 2173) := by
    rw [show ((2173 / 1280) : ℝ) = ((1280 / 2173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1196190663 / 1000000000) ≤ -Real.log (387 / 1280) ∧
    -Real.log (387 / 1280) ≤ (239238133 / 200000000) := by
  have h := checkLog_sound (w := (253 / 1027)) (n := 12)
    (lo := (503043483 / 1000000000)) (hi := (125760871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 387) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 387) = 1/(387 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-239238133 / 200000000) (-1196190663 / 1000000000) (Real.log (387 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40954411 / 100000000) ≤ -Real.log (1000000 / 1506131) ∧
    -Real.log (1000000 / 1506131) ≤ (409544111 / 1000000000) := by
  have h := checkLog_sound (w := (506131 / 2506131)) (n := 12)
    (lo := (40954411 / 100000000)) (hi := (409544111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1506131 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1506131 / 1000000) = 1/(1000000 / 1506131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40954411 / 100000000) (409544111 / 1000000000) (Real.log (1506131 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1506131 / 1000000) = -Real.log (1000000 / 1506131) := by
    rw [show ((1506131 / 1000000) : ℝ) = ((1000000 / 1506131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (352742489 / 500000000) ≤ -Real.log (493869 / 1000000) ∧
    -Real.log (493869 / 1000000) ≤ (35274249 / 50000000) := by
  have h := checkLog_sound (w := (6131 / 993869)) (n := 12)
    (lo := (6168899 / 500000000)) (hi := (12337799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 493869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 493869) = 1/(493869 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-35274249 / 50000000) (-352742489 / 500000000) (Real.log (493869 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (410748459 / 1000000000) ≤ -Real.log (500000 / 753973) ∧
    -Real.log (500000 / 753973) ≤ (20537423 / 50000000) := by
  have h := checkLog_sound (w := (253973 / 1253973)) (n := 12)
    (lo := (410748459 / 1000000000)) (hi := (20537423 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753973 / 500000) = 1/(500000 / 753973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (410748459 / 1000000000) (20537423 / 50000000) (Real.log (753973 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (753973 / 500000) = -Real.log (500000 / 753973) := by
    rw [show ((753973 / 500000) : ℝ) = ((500000 / 753973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (709166811 / 1000000000) ≤ -Real.log (246027 / 500000) ∧
    -Real.log (246027 / 500000) ≤ (709166813 / 1000000000) := by
  have h := checkLog_sound (w := (3973 / 496027)) (n := 12)
    (lo := (16019631 / 1000000000)) (hi := (1001227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 246027) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 246027) = 1/(246027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-709166813 / 1000000000) (-709166811 / 1000000000) (Real.log (246027 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (325765841 / 1000000000) ≤ -Real.log (1000000 / 1385091) ∧
    -Real.log (1000000 / 1385091) ≤ (162882921 / 500000000) := by
  have h := checkLog_sound (w := (385091 / 2385091)) (n := 12)
    (lo := (325765841 / 1000000000)) (hi := (162882921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385091 / 1000000) = 1/(1000000 / 1385091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (325765841 / 1000000000) (162882921 / 500000000) (Real.log (1385091 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1385091 / 1000000) = -Real.log (1000000 / 1385091) := by
    rw [show ((1385091 / 1000000) : ℝ) = ((1000000 / 1385091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (486280989 / 1000000000) ≤ -Real.log (614909 / 1000000) ∧
    -Real.log (614909 / 1000000) ≤ (48628099 / 100000000) := by
  have h := checkLog_sound (w := (385091 / 1614909)) (n := 12)
    (lo := (486280989 / 1000000000)) (hi := (48628099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 614909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 614909) = 1/(614909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-48628099 / 100000000) (-486280989 / 1000000000) (Real.log (614909 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (326913843 / 1000000000) ≤ -Real.log (500000 / 693341) ∧
    -Real.log (500000 / 693341) ≤ (81728461 / 250000000) := by
  have h := checkLog_sound (w := (193341 / 1193341)) (n := 12)
    (lo := (326913843 / 1000000000)) (hi := (81728461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693341 / 500000) = 1/(500000 / 693341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (326913843 / 1000000000) (81728461 / 250000000) (Real.log (693341 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (693341 / 500000) = -Real.log (500000 / 693341) := by
    rw [show ((693341 / 500000) : ℝ) = ((500000 / 693341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (488871717 / 1000000000) ≤ -Real.log (306659 / 500000) ∧
    -Real.log (306659 / 500000) ≤ (244435859 / 500000000) := by
  have h := checkLog_sound (w := (193341 / 806659)) (n := 12)
    (lo := (488871717 / 1000000000)) (hi := (244435859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 306659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 306659) = 1/(306659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-244435859 / 500000000) (-488871717 / 1000000000) (Real.log (306659 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1115029089 / 1000000000) ≤ -Real.log (500000000000 / 1524828446409) ∧
    -Real.log (500000000000 / 1524828446409) ≤ (1115029091 / 1000000000) := by
  have h := checkLog_sound (w := (524828446409 / 2524828446409)) (n := 12)
    (lo := (421881909 / 1000000000)) (hi := (42188191 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1524828446409 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1524828446409 / 1000000000000) = 1/(500000000000 / 1524828446409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1115029089 / 1000000000) (1115029091 / 1000000000) (Real.log (1524828446409 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1524828446409 / 500000000000) = -Real.log (500000000000 / 1524828446409) := by
    rw [show ((1524828446409 / 500000000000) : ℝ) = ((500000000000 / 1524828446409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1119915271 / 1000000000) ≤ -Real.log (500000000000 / 1532297268187) ∧
    -Real.log (500000000000 / 1532297268187) ≤ (1119915273 / 1000000000) := by
  have h := checkLog_sound (w := (532297268187 / 2532297268187)) (n := 12)
    (lo := (426768091 / 1000000000)) (hi := (106692023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1532297268187 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1532297268187 / 1000000000000) = 1/(500000000000 / 1532297268187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1119915271 / 1000000000) (1119915273 / 1000000000) (Real.log (1532297268187 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1532297268187 / 500000000000) = -Real.log (500000000000 / 1532297268187) := by
    rw [show ((1532297268187 / 500000000000) : ℝ) = ((500000000000 / 1532297268187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (81204683 / 100000000) ≤ -Real.log (31250000000 / 70391055831) ∧
    -Real.log (31250000000 / 70391055831) ≤ (50752927 / 62500000) := by
  have h := checkLog_sound (w := (7891055831 / 132891055831)) (n := 12)
    (lo := (2377993 / 20000000)) (hi := (118899651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70391055831 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(70391055831 / 62500000000) = 1/(31250000000 / 70391055831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (81204683 / 100000000) (50752927 / 62500000) (Real.log (70391055831 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (70391055831 / 31250000000) = -Real.log (31250000000 / 70391055831) := by
    rw [show ((70391055831 / 31250000000) : ℝ) = ((31250000000 / 70391055831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (20394639 / 25000000) ≤ -Real.log (250000000000 / 565237772249) ∧
    -Real.log (250000000000 / 565237772249) ≤ (407892781 / 500000000) := by
  have h := checkLog_sound (w := (65237772249 / 1065237772249)) (n := 12)
    (lo := (6131919 / 50000000)) (hi := (122638381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565237772249 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(565237772249 / 500000000000) = 1/(250000000000 / 565237772249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (20394639 / 25000000) (407892781 / 500000000) (Real.log (565237772249 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (565237772249 / 250000000000) = -Real.log (250000000000 / 565237772249) := by
    rw [show ((565237772249 / 250000000000) : ℝ) = ((250000000000 / 565237772249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0139

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0140Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0140
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

theorem reflection_log_1_neg : (299236159 / 1000000000) ≤ -Real.log (2560 / 3453) ∧
    -Real.log (2560 / 3453) ≤ (935113 / 3125000) := by
  have h := checkLog_sound (w := (893 / 6013)) (n := 12)
    (lo := (299236159 / 1000000000)) (hi := (935113 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3453 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3453 / 2560) = 1/(2560 / 3453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (299236159 / 1000000000) (935113 / 3125000) (Real.log (3453 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3453 / 2560) = -Real.log (2560 / 3453) := by
    rw [show ((3453 / 2560) : ℝ) = ((2560 / 3453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (214490827 / 500000000) ≤ -Real.log (1667 / 2560) ∧
    -Real.log (1667 / 2560) ≤ (85796331 / 200000000) := by
  have h := checkLog_sound (w := (893 / 4227)) (n := 12)
    (lo := (214490827 / 500000000)) (hi := (85796331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1667) = 1/(1667 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-85796331 / 200000000) (-214490827 / 500000000) (Real.log (1667 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (74591743 / 250000000) ≤ -Real.log (256 / 345) ∧
    -Real.log (256 / 345) ≤ (298366973 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 601)) (n := 12)
    (lo := (74591743 / 250000000)) (hi := (298366973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345 / 256) = 1/(256 / 345) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (74591743 / 250000000) (298366973 / 1000000000) (Real.log (345 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (345 / 256) = -Real.log (256 / 345) := by
    rw [show ((345 / 256) : ℝ) = ((256 / 345) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (26698977 / 62500000) ≤ -Real.log (167 / 256) ∧
    -Real.log (167 / 256) ≤ (427183633 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 423)) (n := 12)
    (lo := (26698977 / 62500000)) (hi := (427183633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 167) = 1/(167 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-427183633 / 1000000000) (-26698977 / 62500000) (Real.log (167 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (529248623 / 1000000000) ≤ -Real.log (1280 / 2173) ∧
    -Real.log (1280 / 2173) ≤ (33078039 / 62500000) := by
  have h := checkLog_sound (w := (893 / 3453)) (n := 12)
    (lo := (529248623 / 1000000000)) (hi := (33078039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2173 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2173 / 1280) = 1/(1280 / 2173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (529248623 / 1000000000) (33078039 / 62500000) (Real.log (2173 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2173 / 1280) = -Real.log (1280 / 2173) := by
    rw [show ((2173 / 1280) : ℝ) = ((1280 / 2173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1196190663 / 1000000000) ≤ -Real.log (387 / 1280) ∧
    -Real.log (387 / 1280) ≤ (239238133 / 200000000) := by
  have h := checkLog_sound (w := (253 / 1027)) (n := 12)
    (lo := (503043483 / 1000000000)) (hi := (125760871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 387) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 387) = 1/(387 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-239238133 / 200000000) (-1196190663 / 1000000000) (Real.log (387 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (527867089 / 1000000000) ≤ -Real.log (128 / 217) ∧
    -Real.log (128 / 217) ≤ (52786709 / 100000000) := by
  have h := checkLog_sound (w := (89 / 345)) (n := 12)
    (lo := (527867089 / 1000000000)) (hi := (52786709 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217 / 128) = 1/(128 / 217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (527867089 / 1000000000) (52786709 / 100000000) (Real.log (217 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (217 / 128) = -Real.log (128 / 217) := by
    rw [show ((217 / 128) : ℝ) = ((128 / 217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1188468617 / 1000000000) ≤ -Real.log (39 / 128) ∧
    -Real.log (39 / 128) ≤ (1188468619 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 39) = 1/(39 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1188468619 / 1000000000) (-1188468617 / 1000000000) (Real.log (39 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (25521269 / 62500000) ≤ -Real.log (1000000 / 1504319) ∧
    -Real.log (1000000 / 1504319) ≤ (81668061 / 200000000) := by
  have h := checkLog_sound (w := (504319 / 2504319)) (n := 12)
    (lo := (25521269 / 62500000)) (hi := (81668061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1504319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1504319 / 1000000) = 1/(1000000 / 1504319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (25521269 / 62500000) (81668061 / 200000000) (Real.log (1504319 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1504319 / 1000000) = -Real.log (1000000 / 1504319) := by
    rw [show ((1504319 / 1000000) : ℝ) = ((1000000 / 1504319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (701822703 / 1000000000) ≤ -Real.log (495681 / 1000000) ∧
    -Real.log (495681 / 1000000) ≤ (140364541 / 200000000) := by
  have h := checkLog_sound (w := (4319 / 995681)) (n := 12)
    (lo := (8675523 / 1000000000)) (hi := (2168881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 495681) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 495681) = 1/(495681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-140364541 / 200000000) (-701822703 / 1000000000) (Real.log (495681 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (204772387 / 500000000) ≤ -Real.log (250000 / 376533) ∧
    -Real.log (250000 / 376533) ≤ (16381791 / 40000000) := by
  have h := checkLog_sound (w := (126533 / 626533)) (n := 12)
    (lo := (204772387 / 500000000)) (hi := (16381791 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376533 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376533 / 250000) = 1/(250000 / 376533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (204772387 / 500000000) (16381791 / 40000000) (Real.log (376533 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (376533 / 250000) = -Real.log (250000 / 376533) := by
    rw [show ((376533 / 250000) : ℝ) = ((250000 / 376533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (705487003 / 1000000000) ≤ -Real.log (123467 / 250000) ∧
    -Real.log (123467 / 250000) ≤ (141097401 / 200000000) := by
  have h := checkLog_sound (w := (1533 / 248467)) (n := 12)
    (lo := (12339823 / 1000000000)) (hi := (771239 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 123467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 123467) = 1/(123467 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-141097401 / 200000000) (-705487003 / 1000000000) (Real.log (123467 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (162310067 / 500000000) ≤ -Real.log (200000 / 276701) ∧
    -Real.log (200000 / 276701) ≤ (64924027 / 200000000) := by
  have h := checkLog_sound (w := (76701 / 476701)) (n := 12)
    (lo := (162310067 / 500000000)) (hi := (64924027 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((276701 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(276701 / 200000) = 1/(200000 / 276701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (162310067 / 500000000) (64924027 / 200000000) (Real.log (276701 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (276701 / 200000) = -Real.log (200000 / 276701) := by
    rw [show ((276701 / 200000) : ℝ) = ((200000 / 276701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (241852533 / 500000000) ≤ -Real.log (123299 / 200000) ∧
    -Real.log (123299 / 200000) ≤ (483705067 / 1000000000) := by
  have h := checkLog_sound (w := (76701 / 323299)) (n := 12)
    (lo := (241852533 / 500000000)) (hi := (483705067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 123299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 123299) = 1/(123299 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-483705067 / 1000000000) (-241852533 / 500000000) (Real.log (123299 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (325766563 / 1000000000) ≤ -Real.log (250000 / 346273) ∧
    -Real.log (250000 / 346273) ≤ (81441641 / 250000000) := by
  have h := checkLog_sound (w := (96273 / 596273)) (n := 12)
    (lo := (325766563 / 1000000000)) (hi := (81441641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346273 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346273 / 250000) = 1/(250000 / 346273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (325766563 / 1000000000) (81441641 / 250000000) (Real.log (346273 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (346273 / 250000) = -Real.log (250000 / 346273) := by
    rw [show ((346273 / 250000) : ℝ) = ((250000 / 346273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (97256523 / 200000000) ≤ -Real.log (153727 / 250000) ∧
    -Real.log (153727 / 250000) ≤ (60785327 / 125000000) := by
  have h := checkLog_sound (w := (96273 / 403727)) (n := 12)
    (lo := (97256523 / 200000000)) (hi := (60785327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 153727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 153727) = 1/(153727 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60785327 / 125000000) (-97256523 / 200000000) (Real.log (153727 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1110163007 / 1000000000) ≤ -Real.log (500000000000 / 1517426530369) ∧
    -Real.log (500000000000 / 1517426530369) ≤ (1110163009 / 1000000000) := by
  have h := checkLog_sound (w := (517426530369 / 2517426530369)) (n := 12)
    (lo := (417015827 / 1000000000)) (hi := (104253957 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517426530369 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1517426530369 / 1000000000000) = 1/(500000000000 / 1517426530369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1110163007 / 1000000000) (1110163009 / 1000000000) (Real.log (1517426530369 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1517426530369 / 500000000000) = -Real.log (500000000000 / 1517426530369) := by
    rw [show ((1517426530369 / 500000000000) : ℝ) = ((500000000000 / 1517426530369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (557515889 / 500000000) ≤ -Real.log (500000000000 / 1524832546349) ∧
    -Real.log (500000000000 / 1524832546349) ≤ (55751589 / 50000000) := by
  have h := checkLog_sound (w := (524832546349 / 2524832546349)) (n := 12)
    (lo := (210942299 / 500000000)) (hi := (421884599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1524832546349 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1524832546349 / 1000000000000) = 1/(500000000000 / 1524832546349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (557515889 / 500000000) (55751589 / 50000000) (Real.log (1524832546349 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1524832546349 / 500000000000) = -Real.log (500000000000 / 1524832546349) := by
    rw [show ((1524832546349 / 500000000000) : ℝ) = ((500000000000 / 1524832546349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2020813 / 2500000) ≤ -Real.log (12500000000 / 28051829293) ∧
    -Real.log (12500000000 / 28051829293) ≤ (404162601 / 500000000) := by
  have h := checkLog_sound (w := (3051829293 / 53051829293)) (n := 12)
    (lo := (5758901 / 50000000)) (hi := (115178021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28051829293 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(28051829293 / 25000000000) = 1/(12500000000 / 28051829293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2020813 / 2500000) (404162601 / 500000000) (Real.log (28051829293 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28051829293 / 12500000000) = -Real.log (12500000000 / 28051829293) := by
    rw [show ((28051829293 / 12500000000) : ℝ) = ((12500000000 / 28051829293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (406024589 / 500000000) ≤ -Real.log (500000000000 / 1126259538013) ∧
    -Real.log (500000000000 / 1126259538013) ≤ (40602459 / 50000000) := by
  have h := checkLog_sound (w := (126259538013 / 2126259538013)) (n := 12)
    (lo := (59450999 / 500000000)) (hi := (118901999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126259538013 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1126259538013 / 1000000000000) = 1/(500000000000 / 1126259538013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (406024589 / 500000000) (40602459 / 50000000) (Real.log (1126259538013 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1126259538013 / 500000000000) = -Real.log (500000000000 / 1126259538013) := by
    rw [show ((1126259538013 / 500000000000) : ℝ) = ((500000000000 / 1126259538013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0140

end


