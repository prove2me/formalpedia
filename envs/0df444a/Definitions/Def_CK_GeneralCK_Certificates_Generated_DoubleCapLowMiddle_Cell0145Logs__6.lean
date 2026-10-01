-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0145Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0145Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:09:35.935982+00:00
-- url     : https://prove2.me/theorems/e5c1f06a-b56d-4739-b36d-727aa706b996
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0145Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0146Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0145Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0146Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0147Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0148Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0149Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0150Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0145Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0146Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0147Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0148Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0149Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0150Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0145Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0146Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0147Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0148Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0149Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0150Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0145Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0146Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0147Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0148Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0149Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0150Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0145Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0145
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

theorem reflection_log_1_neg : (164126877 / 250000000) ≤ -Real.log (12800 / 24679) ∧
    -Real.log (12800 / 24679) ≤ (656507509 / 1000000000) := by
  have h := checkLog_sound (w := (11879 / 37479)) (n := 12)
    (lo := (164126877 / 250000000)) (hi := (656507509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24679 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24679 / 12800) = 1/(12800 / 24679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (164126877 / 250000000) (656507509 / 1000000000) (Real.log (24679 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24679 / 12800) = -Real.log (12800 / 24679) := by
    rw [show ((24679 / 12800) : ℝ) = ((12800 / 24679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2631740411 / 1000000000) ≤ -Real.log (921 / 12800) ∧
    -Real.log (921 / 12800) ≤ (526348083 / 200000000) := by
  have h := checkLog_sound (w := (679 / 2521)) (n := 12)
    (lo := (552298871 / 1000000000)) (hi := (69037359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 921) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 921) = 1/(921 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-526348083 / 200000000) (-2631740411 / 1000000000) (Real.log (921 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (656122491 / 1000000000) ≤ -Real.log (25600 / 49339) ∧
    -Real.log (25600 / 49339) ≤ (164030623 / 250000000) := by
  have h := checkLog_sound (w := (23739 / 74939)) (n := 12)
    (lo := (656122491 / 1000000000)) (hi := (164030623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49339 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49339 / 25600) = 1/(25600 / 49339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (656122491 / 1000000000) (164030623 / 250000000) (Real.log (49339 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49339 / 25600) = -Real.log (25600 / 49339) := by
    rw [show ((49339 / 25600) : ℝ) = ((25600 / 49339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (655369593 / 250000000) ≤ -Real.log (1861 / 25600) ∧
    -Real.log (1861 / 25600) ≤ (327684797 / 125000000) := by
  have h := checkLog_sound (w := (1339 / 5061)) (n := 12)
    (lo := (16938651 / 31250000)) (hi := (542036833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1861) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1861) = 1/(1861 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-327684797 / 125000000) (-655369593 / 250000000) (Real.log (1861 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19327317 / 31250000) ≤ -Real.log (6400 / 11879) ∧
    -Real.log (6400 / 11879) ≤ (123694829 / 200000000) := by
  have h := checkLog_sound (w := (5479 / 18279)) (n := 12)
    (lo := (19327317 / 31250000)) (hi := (123694829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11879 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11879 / 6400) = 1/(6400 / 11879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19327317 / 31250000) (123694829 / 200000000) (Real.log (11879 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11879 / 6400) = -Real.log (6400 / 11879) := by
    rw [show ((11879 / 6400) : ℝ) = ((6400 / 11879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1938593231 / 1000000000) ≤ -Real.log (921 / 6400) ∧
    -Real.log (921 / 6400) ≤ (969296617 / 500000000) := by
  have h := checkLog_sound (w := (679 / 2521)) (n := 12)
    (lo := (552298871 / 1000000000)) (hi := (69037359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 921) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 921) = 1/(921 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-969296617 / 500000000) (-1938593231 / 1000000000) (Real.log (921 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (308837047 / 500000000) ≤ -Real.log (12800 / 23739) ∧
    -Real.log (12800 / 23739) ≤ (123534819 / 200000000) := by
  have h := checkLog_sound (w := (10939 / 36539)) (n := 12)
    (lo := (308837047 / 500000000)) (hi := (123534819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23739 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23739 / 12800) = 1/(12800 / 23739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (308837047 / 500000000) (123534819 / 200000000) (Real.log (23739 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23739 / 12800) = -Real.log (12800 / 23739) := by
    rw [show ((23739 / 12800) : ℝ) = ((12800 / 23739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (241041399 / 125000000) ≤ -Real.log (1861 / 12800) ∧
    -Real.log (1861 / 12800) ≤ (385666239 / 200000000) := by
  have h := checkLog_sound (w := (1339 / 5061)) (n := 12)
    (lo := (16938651 / 31250000)) (hi := (542036833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1861) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1861) = 1/(1861 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-385666239 / 200000000) (-241041399 / 125000000) (Real.log (1861 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166000643 / 250000000) ≤ -Real.log (125000 / 242819) ∧
    -Real.log (125000 / 242819) ≤ (664002573 / 1000000000) := by
  have h := checkLog_sound (w := (117819 / 367819)) (n := 12)
    (lo := (166000643 / 250000000)) (hi := (664002573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242819 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242819 / 125000) = 1/(125000 / 242819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166000643 / 250000000) (664002573 / 1000000000) (Real.log (242819 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (242819 / 125000) = -Real.log (125000 / 242819) := by
    rw [show ((242819 / 125000) : ℝ) = ((125000 / 242819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (571375017 / 200000000) ≤ -Real.log (7181 / 125000) ∧
    -Real.log (7181 / 125000) ≤ (285687509 / 100000000) := by
  have h := checkLog_sound (w := (1263 / 29987)) (n := 12)
    (lo := (16857273 / 200000000)) (hi := (42143183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14362) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 14362) = 1/(7181 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-285687509 / 100000000) (-571375017 / 200000000) (Real.log (7181 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (664279489 / 1000000000) ≤ -Real.log (100000 / 194309) ∧
    -Real.log (100000 / 194309) ≤ (66427949 / 100000000) := by
  have h := checkLog_sound (w := (94309 / 294309)) (n := 12)
    (lo := (664279489 / 1000000000)) (hi := (66427949 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194309 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194309 / 100000) = 1/(100000 / 194309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (664279489 / 1000000000) (66427949 / 100000000) (Real.log (194309 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (194309 / 100000) = -Real.log (100000 / 194309) := by
    rw [show ((194309 / 100000) : ℝ) = ((100000 / 194309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (716571051 / 250000000) ≤ -Real.log (5691 / 100000) ∧
    -Real.log (5691 / 100000) ≤ (2866284209 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 11941)) (n := 12)
    (lo := (23423871 / 250000000)) (hi := (18739097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5691) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 5691) = 1/(5691 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2866284209 / 1000000000) (-716571051 / 250000000) (Real.log (5691 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (331710347 / 500000000) ≤ -Real.log (500000 / 970711) ∧
    -Real.log (500000 / 970711) ≤ (132684139 / 200000000) := by
  have h := checkLog_sound (w := (470711 / 1470711)) (n := 12)
    (lo := (331710347 / 500000000)) (hi := (132684139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970711 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970711 / 500000) = 1/(500000 / 970711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (331710347 / 500000000) (132684139 / 200000000) (Real.log (970711 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (970711 / 500000) = -Real.log (500000 / 970711) := by
    rw [show ((970711 / 500000) : ℝ) = ((500000 / 970711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2837396077 / 1000000000) ≤ -Real.log (29289 / 500000) ∧
    -Real.log (29289 / 500000) ≤ (1418698041 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 60539)) (n := 12)
    (lo := (64807357 / 1000000000)) (hi := (32403679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29289) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 29289) = 1/(29289 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1418698041 / 500000000) (-2837396077 / 1000000000) (Real.log (29289 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (16592779 / 25000000) ≤ -Real.log (500000 / 970993) ∧
    -Real.log (500000 / 970993) ≤ (663711161 / 1000000000) := by
  have h := checkLog_sound (w := (470993 / 1470993)) (n := 12)
    (lo := (16592779 / 25000000)) (hi := (663711161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970993 / 500000) = 1/(500000 / 970993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (16592779 / 25000000) (663711161 / 1000000000) (Real.log (970993 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (970993 / 500000) = -Real.log (500000 / 970993) := by
    rw [show ((970993 / 500000) : ℝ) = ((500000 / 970993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (711767729 / 250000000) ≤ -Real.log (29007 / 500000) ∧
    -Real.log (29007 / 500000) ≤ (2847070921 / 1000000000) := by
  have h := checkLog_sound (w := (2243 / 60257)) (n := 12)
    (lo := (18620549 / 250000000)) (hi := (74482197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29007) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 29007) = 1/(29007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2847070921 / 1000000000) (-711767729 / 250000000) (Real.log (29007 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3520877657 / 1000000000) ≤ -Real.log (500000000000 / 16907046372371) ∧
    -Real.log (500000000000 / 16907046372371) ≤ (3520877663 / 1000000000) := by
  have h := checkLog_sound (w := (907046372371 / 32907046372371)) (n := 12)
    (lo := (55141757 / 1000000000)) (hi := (27570879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16907046372371 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16907046372371 / 16000000000000) = 1/(500000000000 / 16907046372371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3520877657 / 1000000000) (3520877663 / 1000000000) (Real.log (16907046372371 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16907046372371 / 500000000000) = -Real.log (500000000000 / 16907046372371) := by
    rw [show ((16907046372371 / 500000000000) : ℝ) = ((500000000000 / 16907046372371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3530563693 / 1000000000) ≤ -Real.log (31250000000 / 1066975267967) ∧
    -Real.log (31250000000 / 1066975267967) ≤ (3530563699 / 1000000000) := by
  have h := checkLog_sound (w := (66975267967 / 2066975267967)) (n := 12)
    (lo := (64827793 / 1000000000)) (hi := (32413897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1066975267967 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1066975267967 / 1000000000000) = 1/(31250000000 / 1066975267967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3530563693 / 1000000000) (3530563699 / 1000000000) (Real.log (1066975267967 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1066975267967 / 31250000000) = -Real.log (31250000000 / 1066975267967) := by
    rw [show ((1066975267967 / 31250000000) : ℝ) = ((31250000000 / 1066975267967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (350081677 / 100000000) ≤ -Real.log (500000000000 / 16571255420123) ∧
    -Real.log (500000000000 / 16571255420123) ≤ (437602097 / 125000000) := by
  have h := checkLog_sound (w := (571255420123 / 32571255420123)) (n := 12)
    (lo := (3508087 / 100000000)) (hi := (35080871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16571255420123 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16571255420123 / 16000000000000) = 1/(500000000000 / 16571255420123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (350081677 / 100000000) (437602097 / 125000000) (Real.log (16571255420123 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (16571255420123 / 500000000000) = -Real.log (500000000000 / 16571255420123) := by
    rw [show ((16571255420123 / 500000000000) : ℝ) = ((500000000000 / 16571255420123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (877695519 / 250000000) ≤ -Real.log (500000000000 / 16737218602407) ∧
    -Real.log (500000000000 / 16737218602407) ≤ (1755391041 / 500000000) := by
  have h := checkLog_sound (w := (737218602407 / 32737218602407)) (n := 12)
    (lo := (1407693 / 31250000)) (hi := (45046177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16737218602407 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16737218602407 / 16000000000000) = 1/(500000000000 / 16737218602407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (877695519 / 250000000) (1755391041 / 500000000) (Real.log (16737218602407 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16737218602407 / 500000000000) = -Real.log (500000000000 / 16737218602407) := by
    rw [show ((16737218602407 / 500000000000) : ℝ) = ((500000000000 / 16737218602407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0145

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0146Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0146
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

theorem reflection_log_1_neg : (656122491 / 1000000000) ≤ -Real.log (25600 / 49339) ∧
    -Real.log (25600 / 49339) ≤ (164030623 / 250000000) := by
  have h := checkLog_sound (w := (23739 / 74939)) (n := 12)
    (lo := (656122491 / 1000000000)) (hi := (164030623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49339 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49339 / 25600) = 1/(25600 / 49339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (656122491 / 1000000000) (164030623 / 250000000) (Real.log (49339 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49339 / 25600) = -Real.log (25600 / 49339) := by
    rw [show ((49339 / 25600) : ℝ) = ((25600 / 49339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (655369593 / 250000000) ≤ -Real.log (1861 / 25600) ∧
    -Real.log (1861 / 25600) ≤ (327684797 / 125000000) := by
  have h := checkLog_sound (w := (1339 / 5061)) (n := 12)
    (lo := (16938651 / 31250000)) (hi := (542036833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1861) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1861) = 1/(1861 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-327684797 / 125000000) (-655369593 / 250000000) (Real.log (1861 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (327868663 / 500000000) ≤ -Real.log (640 / 1233) ∧
    -Real.log (640 / 1233) ≤ (655737327 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 1873)) (n := 12)
    (lo := (327868663 / 500000000)) (hi := (655737327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 640) = 1/(640 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (327868663 / 500000000) (655737327 / 1000000000) (Real.log (1233 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1233 / 640) = -Real.log (640 / 1233) := by
    rw [show ((1233 / 640) : ℝ) = ((640 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (652830143 / 250000000) ≤ -Real.log (47 / 640) ∧
    -Real.log (47 / 640) ≤ (10200471 / 3906250) := by
  have h := checkLog_sound (w := (33 / 127)) (n := 12)
    (lo := (66484879 / 125000000)) (hi := (531879033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 47) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 47) = 1/(47 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10200471 / 3906250) (-652830143 / 250000000) (Real.log (47 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (308837047 / 500000000) ≤ -Real.log (12800 / 23739) ∧
    -Real.log (12800 / 23739) ≤ (123534819 / 200000000) := by
  have h := checkLog_sound (w := (10939 / 36539)) (n := 12)
    (lo := (308837047 / 500000000)) (hi := (123534819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23739 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23739 / 12800) = 1/(12800 / 23739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (308837047 / 500000000) (123534819 / 200000000) (Real.log (23739 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23739 / 12800) = -Real.log (12800 / 23739) := by
    rw [show ((23739 / 12800) : ℝ) = ((12800 / 23739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (241041399 / 125000000) ≤ -Real.log (1861 / 12800) ∧
    -Real.log (1861 / 12800) ≤ (385666239 / 200000000) := by
  have h := checkLog_sound (w := (1339 / 5061)) (n := 12)
    (lo := (16938651 / 31250000)) (hi := (542036833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1861) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1861) = 1/(1861 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-385666239 / 200000000) (-241041399 / 125000000) (Real.log (1861 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (616873403 / 1000000000) ≤ -Real.log (320 / 593) ∧
    -Real.log (320 / 593) ≤ (154218351 / 250000000) := by
  have h := checkLog_sound (w := (273 / 913)) (n := 12)
    (lo := (616873403 / 1000000000)) (hi := (154218351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593 / 320) = 1/(320 / 593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (616873403 / 1000000000) (154218351 / 250000000) (Real.log (593 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (593 / 320) = -Real.log (320 / 593) := by
    rw [show ((593 / 320) : ℝ) = ((320 / 593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (119885837 / 62500000) ≤ -Real.log (47 / 320) ∧
    -Real.log (47 / 320) ≤ (383634679 / 200000000) := by
  have h := checkLog_sound (w := (33 / 127)) (n := 12)
    (lo := (66484879 / 125000000)) (hi := (531879033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 47) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 47) = 1/(47 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-383634679 / 200000000) (-119885837 / 62500000) (Real.log (47 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (663726093 / 1000000000) ≤ -Real.log (200000 / 388403) ∧
    -Real.log (200000 / 388403) ≤ (331863047 / 500000000) := by
  have h := checkLog_sound (w := (188403 / 588403)) (n := 12)
    (lo := (663726093 / 1000000000)) (hi := (331863047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388403 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388403 / 200000) = 1/(200000 / 388403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (663726093 / 1000000000) (331863047 / 500000000) (Real.log (388403 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (388403 / 200000) = -Real.log (200000 / 388403) := by
    rw [show ((388403 / 200000) : ℝ) = ((200000 / 388403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (71189273 / 25000000) ≤ -Real.log (11597 / 200000) ∧
    -Real.log (11597 / 200000) ≤ (113902837 / 40000000) := by
  have h := checkLog_sound (w := (903 / 24097)) (n := 12)
    (lo := (374911 / 5000000)) (hi := (74982201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11597) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11597) = 1/(11597 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-113902837 / 40000000) (-71189273 / 25000000) (Real.log (11597 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (664003087 / 1000000000) ≤ -Real.log (1000000 / 1942553) ∧
    -Real.log (1000000 / 1942553) ≤ (41500193 / 62500000) := by
  have h := checkLog_sound (w := (942553 / 2942553)) (n := 12)
    (lo := (664003087 / 1000000000)) (hi := (41500193 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1942553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1942553 / 1000000) = 1/(1000000 / 1942553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (664003087 / 1000000000) (41500193 / 62500000) (Real.log (1942553 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1942553 / 1000000) = -Real.log (1000000 / 1942553) := by
    rw [show ((1942553 / 1000000) : ℝ) = ((1000000 / 1942553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2856892493 / 1000000000) ≤ -Real.log (57447 / 1000000) ∧
    -Real.log (57447 / 1000000) ≤ (1428446249 / 500000000) := by
  have h := checkLog_sound (w := (5053 / 119947)) (n := 12)
    (lo := (84303773 / 1000000000)) (hi := (42151887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57447) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 57447) = 1/(57447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1428446249 / 500000000) (-2856892493 / 1000000000) (Real.log (57447 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (331565329 / 500000000) ≤ -Real.log (1000000 / 1940859) ∧
    -Real.log (1000000 / 1940859) ≤ (663130659 / 1000000000) := by
  have h := checkLog_sound (w := (940859 / 2940859)) (n := 12)
    (lo := (331565329 / 500000000)) (hi := (663130659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1940859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1940859 / 1000000) = 1/(1000000 / 1940859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (331565329 / 500000000) (663130659 / 1000000000) (Real.log (1940859 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1940859 / 1000000) = -Real.log (1000000 / 1940859) := by
    rw [show ((1940859 / 1000000) : ℝ) = ((1000000 / 1940859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2827830853 / 1000000000) ≤ -Real.log (59141 / 1000000) ∧
    -Real.log (59141 / 1000000) ≤ (1413915429 / 500000000) := by
  have h := checkLog_sound (w := (3359 / 121641)) (n := 12)
    (lo := (55242133 / 1000000000)) (hi := (27621067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59141) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 59141) = 1/(59141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1413915429 / 500000000) (-2827830853 / 1000000000) (Real.log (59141 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (663421209 / 1000000000) ≤ -Real.log (1000000 / 1941423) ∧
    -Real.log (1000000 / 1941423) ≤ (66342121 / 100000000) := by
  have h := checkLog_sound (w := (941423 / 2941423)) (n := 12)
    (lo := (663421209 / 1000000000)) (hi := (66342121 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1941423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1941423 / 1000000) = 1/(1000000 / 1941423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (663421209 / 1000000000) (66342121 / 100000000) (Real.log (1941423 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1941423 / 1000000) = -Real.log (1000000 / 1941423) := by
    rw [show ((1941423 / 1000000) : ℝ) = ((1000000 / 1941423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (709353287 / 250000000) ≤ -Real.log (58577 / 1000000) ∧
    -Real.log (58577 / 1000000) ≤ (2837413153 / 1000000000) := by
  have h := checkLog_sound (w := (3923 / 121077)) (n := 12)
    (lo := (16206107 / 250000000)) (hi := (64824429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 58577) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 58577) = 1/(58577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2837413153 / 1000000000) (-709353287 / 250000000) (Real.log (58577 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3511297013 / 1000000000) ≤ -Real.log (250000000000 / 8372919720617) ∧
    -Real.log (250000000000 / 8372919720617) ≤ (3511297019 / 1000000000) := by
  have h := checkLog_sound (w := (372919720617 / 16372919720617)) (n := 12)
    (lo := (45561113 / 1000000000)) (hi := (22780557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8372919720617 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8372919720617 / 8000000000000) = 1/(250000000000 / 8372919720617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3511297013 / 1000000000) (3511297019 / 1000000000) (Real.log (8372919720617 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8372919720617 / 250000000000) = -Real.log (250000000000 / 8372919720617) := by
    rw [show ((8372919720617 / 250000000000) : ℝ) = ((250000000000 / 8372919720617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3520895579 / 1000000000) ≤ -Real.log (50000000000 / 1690734938291) ∧
    -Real.log (50000000000 / 1690734938291) ≤ (704179117 / 200000000) := by
  have h := checkLog_sound (w := (90734938291 / 3290734938291)) (n := 12)
    (lo := (55159679 / 1000000000)) (hi := (86187 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1690734938291 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1690734938291 / 1600000000000) = 1/(50000000000 / 1690734938291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3520895579 / 1000000000) (704179117 / 200000000) (Real.log (1690734938291 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1690734938291 / 50000000000) = -Real.log (50000000000 / 1690734938291) := by
    rw [show ((1690734938291 / 50000000000) : ℝ) = ((50000000000 / 1690734938291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3490961511 / 1000000000) ≤ -Real.log (500000000000 / 16408743511269) ∧
    -Real.log (500000000000 / 16408743511269) ≤ (3490961517 / 1000000000) := by
  have h := checkLog_sound (w := (408743511269 / 32408743511269)) (n := 12)
    (lo := (25225611 / 1000000000)) (hi := (6306403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16408743511269 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16408743511269 / 16000000000000) = 1/(500000000000 / 16408743511269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3490961511 / 1000000000) (3490961517 / 1000000000) (Real.log (16408743511269 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (16408743511269 / 500000000000) = -Real.log (500000000000 / 16408743511269) := by
    rw [show ((16408743511269 / 500000000000) : ℝ) = ((500000000000 / 16408743511269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3500834357 / 1000000000) ≤ -Real.log (500000000000 / 16571546852861) ∧
    -Real.log (500000000000 / 16571546852861) ≤ (3500834363 / 1000000000) := by
  have h := checkLog_sound (w := (571546852861 / 32571546852861)) (n := 12)
    (lo := (35098457 / 1000000000)) (hi := (17549229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16571546852861 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16571546852861 / 16000000000000) = 1/(500000000000 / 16571546852861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3500834357 / 1000000000) (3500834363 / 1000000000) (Real.log (16571546852861 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16571546852861 / 500000000000) = -Real.log (500000000000 / 16571546852861) := by
    rw [show ((16571546852861 / 500000000000) : ℝ) = ((500000000000 / 16571546852861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0146

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0147Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0147
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

theorem reflection_log_1_neg : (327868663 / 500000000) ≤ -Real.log (640 / 1233) ∧
    -Real.log (640 / 1233) ≤ (655737327 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 1873)) (n := 12)
    (lo := (327868663 / 500000000)) (hi := (655737327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 640) = 1/(640 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (327868663 / 500000000) (655737327 / 1000000000) (Real.log (1233 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1233 / 640) = -Real.log (640 / 1233) := by
    rw [show ((1233 / 640) : ℝ) = ((640 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (652830143 / 250000000) ≤ -Real.log (47 / 640) ∧
    -Real.log (47 / 640) ≤ (10200471 / 3906250) := by
  have h := checkLog_sound (w := (33 / 127)) (n := 12)
    (lo := (66484879 / 125000000)) (hi := (531879033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 47) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 47) = 1/(47 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10200471 / 3906250) (-652830143 / 250000000) (Real.log (47 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (654966551 / 1000000000) ≤ -Real.log (12800 / 24641) ∧
    -Real.log (12800 / 24641) ≤ (81870819 / 125000000) := by
  have h := checkLog_sound (w := (11841 / 37441)) (n := 12)
    (lo := (654966551 / 1000000000)) (hi := (81870819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24641 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24641 / 12800) = 1/(12800 / 24641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (654966551 / 1000000000) (81870819 / 125000000) (Real.log (24641 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24641 / 12800) = -Real.log (12800 / 24641) := by
    rw [show ((24641 / 12800) : ℝ) = ((12800 / 24641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2591309373 / 1000000000) ≤ -Real.log (959 / 12800) ∧
    -Real.log (959 / 12800) ≤ (2591309377 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 2559)) (n := 12)
    (lo := (511867833 / 1000000000)) (hi := (255933917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 959) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 959) = 1/(959 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2591309377 / 1000000000) (-2591309373 / 1000000000) (Real.log (959 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (616873403 / 1000000000) ≤ -Real.log (320 / 593) ∧
    -Real.log (320 / 593) ≤ (154218351 / 250000000) := by
  have h := checkLog_sound (w := (273 / 913)) (n := 12)
    (lo := (616873403 / 1000000000)) (hi := (154218351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593 / 320) = 1/(320 / 593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (616873403 / 1000000000) (154218351 / 250000000) (Real.log (593 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (593 / 320) = -Real.log (320 / 593) := by
    rw [show ((593 / 320) : ℝ) = ((320 / 593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (119885837 / 62500000) ≤ -Real.log (47 / 320) ∧
    -Real.log (47 / 320) ≤ (383634679 / 200000000) := by
  have h := checkLog_sound (w := (33 / 127)) (n := 12)
    (lo := (66484879 / 125000000)) (hi := (531879033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 47) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 47) = 1/(47 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-383634679 / 200000000) (-119885837 / 62500000) (Real.log (47 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (307635047 / 500000000) ≤ -Real.log (6400 / 11841) ∧
    -Real.log (6400 / 11841) ≤ (123054019 / 200000000) := by
  have h := checkLog_sound (w := (5441 / 18241)) (n := 12)
    (lo := (307635047 / 500000000)) (hi := (123054019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11841 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11841 / 6400) = 1/(6400 / 11841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (307635047 / 500000000) (123054019 / 200000000) (Real.log (11841 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11841 / 6400) = -Real.log (6400 / 11841) := by
    rw [show ((11841 / 6400) : ℝ) = ((6400 / 11841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1898162193 / 1000000000) ≤ -Real.log (959 / 6400) ∧
    -Real.log (959 / 6400) ≤ (474540549 / 250000000) := by
  have h := checkLog_sound (w := (641 / 2559)) (n := 12)
    (lo := (511867833 / 1000000000)) (hi := (255933917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 959) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 959) = 1/(959 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-474540549 / 250000000) (-1898162193 / 1000000000) (Real.log (959 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (663175483 / 1000000000) ≤ -Real.log (500000 / 970473) ∧
    -Real.log (500000 / 970473) ≤ (165793871 / 250000000) := by
  have h := checkLog_sound (w := (470473 / 1470473)) (n := 12)
    (lo := (663175483 / 1000000000)) (hi := (165793871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970473 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970473 / 500000) = 1/(500000 / 970473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (663175483 / 1000000000) (165793871 / 250000000) (Real.log (970473 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (970473 / 500000) = -Real.log (500000 / 970473) := by
    rw [show ((970473 / 500000) : ℝ) = ((500000 / 970473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2829302997 / 1000000000) ≤ -Real.log (29527 / 500000) ∧
    -Real.log (29527 / 500000) ≤ (1414651501 / 500000000) := by
  have h := checkLog_sound (w := (1723 / 60777)) (n := 12)
    (lo := (56714277 / 1000000000)) (hi := (28357139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29527) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 29527) = 1/(29527 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1414651501 / 500000000) (-2829302997 / 1000000000) (Real.log (29527 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (41482913 / 62500000) ≤ -Real.log (15625 / 30344) ∧
    -Real.log (15625 / 30344) ≤ (663726609 / 1000000000) := by
  have h := checkLog_sound (w := (14719 / 45969)) (n := 12)
    (lo := (41482913 / 62500000)) (hi := (663726609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30344 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30344 / 15625) = 1/(15625 / 30344) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (41482913 / 62500000) (663726609 / 1000000000) (Real.log (30344 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (30344 / 15625) = -Real.log (15625 / 30344) := by
    rw [show ((30344 / 15625) : ℝ) = ((15625 / 30344) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1423794083 / 500000000) ≤ -Real.log (906 / 15625) ∧
    -Real.log (906 / 15625) ≤ (2847588171 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 30121)) (n := 12)
    (lo := (37499723 / 500000000)) (hi := (74999447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14496) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 14496) = 1/(906 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2847588171 / 1000000000) (-1423794083 / 500000000) (Real.log (906 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13251017 / 20000000) ≤ -Real.log (500000 / 969867) ∧
    -Real.log (500000 / 969867) ≤ (662550851 / 1000000000) := by
  have h := checkLog_sound (w := (469867 / 1469867)) (n := 12)
    (lo := (13251017 / 20000000)) (hi := (662550851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((969867 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(969867 / 500000) = 1/(500000 / 969867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13251017 / 20000000) (662550851 / 1000000000) (Real.log (969867 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (969867 / 500000) = -Real.log (500000 / 969867) := by
    rw [show ((969867 / 500000) : ℝ) = ((500000 / 969867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2808987179 / 1000000000) ≤ -Real.log (30133 / 500000) ∧
    -Real.log (30133 / 500000) ≤ (175561699 / 62500000) := by
  have h := checkLog_sound (w := (1117 / 61383)) (n := 12)
    (lo := (36398459 / 1000000000)) (hi := (1819923 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30133) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 30133) = 1/(30133 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-175561699 / 62500000) (-2808987179 / 1000000000) (Real.log (30133 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (663131173 / 1000000000) ≤ -Real.log (50000 / 97043) ∧
    -Real.log (50000 / 97043) ≤ (331565587 / 500000000) := by
  have h := checkLog_sound (w := (47043 / 147043)) (n := 12)
    (lo := (663131173 / 1000000000)) (hi := (331565587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97043 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97043 / 50000) = 1/(50000 / 97043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (663131173 / 1000000000) (331565587 / 500000000) (Real.log (97043 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (97043 / 50000) = -Real.log (50000 / 97043) := by
    rw [show ((97043 / 50000) : ℝ) = ((50000 / 97043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1413923881 / 500000000) ≤ -Real.log (2957 / 50000) ∧
    -Real.log (2957 / 50000) ≤ (2827847767 / 1000000000) := by
  have h := checkLog_sound (w := (84 / 3041)) (n := 12)
    (lo := (27629521 / 500000000)) (hi := (55259043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2957) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2957) = 1/(2957 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2827847767 / 1000000000) (-1413923881 / 500000000) (Real.log (2957 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3492478479 / 1000000000) ≤ -Real.log (62500000000 / 2054206742981) ∧
    -Real.log (62500000000 / 2054206742981) ≤ (698495697 / 200000000) := by
  have h := checkLog_sound (w := (54206742981 / 4054206742981)) (n := 12)
    (lo := (26742579 / 1000000000)) (hi := (1337129 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2054206742981 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2054206742981 / 2000000000000) = 1/(62500000000 / 2054206742981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3492478479 / 1000000000) (698495697 / 200000000) (Real.log (2054206742981 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2054206742981 / 62500000000) = -Real.log (62500000000 / 2054206742981) := by
    rw [show ((2054206742981 / 62500000000) : ℝ) = ((62500000000 / 2054206742981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1755657387 / 500000000) ≤ -Real.log (500000000000 / 16746136865343) ∧
    -Real.log (500000000000 / 16746136865343) ≤ (175565739 / 50000000) := by
  have h := checkLog_sound (w := (746136865343 / 32746136865343)) (n := 12)
    (lo := (22789437 / 500000000)) (hi := (364631 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16746136865343 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16746136865343 / 16000000000000) = 1/(500000000000 / 16746136865343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1755657387 / 500000000) (175565739 / 50000000) (Real.log (16746136865343 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (16746136865343 / 500000000000) = -Real.log (500000000000 / 16746136865343) := by
    rw [show ((16746136865343 / 500000000000) : ℝ) = ((500000000000 / 16746136865343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3471538029 / 1000000000) ≤ -Real.log (15625000000 / 502909497063) ∧
    -Real.log (15625000000 / 502909497063) ≤ (694307607 / 200000000) := by
  have h := checkLog_sound (w := (2909497063 / 1002909497063)) (n := 12)
    (lo := (5802129 / 1000000000)) (hi := (580213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((502909497063 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(502909497063 / 500000000000) = 1/(15625000000 / 502909497063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3471538029 / 1000000000) (694307607 / 200000000) (Real.log (502909497063 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (502909497063 / 15625000000) = -Real.log (15625000000 / 502909497063) := by
    rw [show ((502909497063 / 15625000000) : ℝ) = ((15625000000 / 502909497063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (698195787 / 200000000) ≤ -Real.log (31250000000 / 1025564338857) ∧
    -Real.log (31250000000 / 1025564338857) ≤ (3490978941 / 1000000000) := by
  have h := checkLog_sound (w := (25564338857 / 2025564338857)) (n := 12)
    (lo := (5048607 / 200000000)) (hi := (6310759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1025564338857 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1025564338857 / 1000000000000) = 1/(31250000000 / 1025564338857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (698195787 / 200000000) (3490978941 / 1000000000) (Real.log (1025564338857 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1025564338857 / 31250000000) = -Real.log (31250000000 / 1025564338857) := by
    rw [show ((1025564338857 / 31250000000) : ℝ) = ((31250000000 / 1025564338857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0147

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0148Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0148
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

theorem reflection_log_1_neg : (654966551 / 1000000000) ≤ -Real.log (12800 / 24641) ∧
    -Real.log (12800 / 24641) ≤ (81870819 / 125000000) := by
  have h := checkLog_sound (w := (11841 / 37441)) (n := 12)
    (lo := (654966551 / 1000000000)) (hi := (81870819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24641 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24641 / 12800) = 1/(12800 / 24641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (654966551 / 1000000000) (81870819 / 125000000) (Real.log (24641 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24641 / 12800) = -Real.log (12800 / 24641) := by
    rw [show ((24641 / 12800) : ℝ) = ((12800 / 24641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2591309373 / 1000000000) ≤ -Real.log (959 / 12800) ∧
    -Real.log (959 / 12800) ≤ (2591309377 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 2559)) (n := 12)
    (lo := (511867833 / 1000000000)) (hi := (255933917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 959) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 959) = 1/(959 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2591309377 / 1000000000) (-2591309373 / 1000000000) (Real.log (959 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (654195181 / 1000000000) ≤ -Real.log (6400 / 12311) ∧
    -Real.log (6400 / 12311) ≤ (327097591 / 500000000) := by
  have h := checkLog_sound (w := (5911 / 18711)) (n := 12)
    (lo := (654195181 / 1000000000)) (hi := (327097591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12311 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12311 / 6400) = 1/(6400 / 12311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (654195181 / 1000000000) (327097591 / 500000000) (Real.log (12311 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12311 / 6400) = -Real.log (6400 / 12311) := by
    rw [show ((12311 / 6400) : ℝ) = ((6400 / 12311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1285845389 / 500000000) ≤ -Real.log (489 / 6400) ∧
    -Real.log (489 / 6400) ≤ (1285845391 / 500000000) := by
  have h := checkLog_sound (w := (311 / 1289)) (n := 12)
    (lo := (246124619 / 500000000)) (hi := (492249239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 489) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 489) = 1/(489 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1285845391 / 500000000) (-1285845389 / 500000000) (Real.log (489 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (307635047 / 500000000) ≤ -Real.log (6400 / 11841) ∧
    -Real.log (6400 / 11841) ≤ (123054019 / 200000000) := by
  have h := checkLog_sound (w := (5441 / 18241)) (n := 12)
    (lo := (307635047 / 500000000)) (hi := (123054019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11841 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11841 / 6400) = 1/(6400 / 11841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (307635047 / 500000000) (123054019 / 200000000) (Real.log (11841 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11841 / 6400) = -Real.log (6400 / 11841) := by
    rw [show ((11841 / 6400) : ℝ) = ((6400 / 11841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1898162193 / 1000000000) ≤ -Real.log (959 / 6400) ∧
    -Real.log (959 / 6400) ≤ (474540549 / 250000000) := by
  have h := checkLog_sound (w := (641 / 2559)) (n := 12)
    (lo := (511867833 / 1000000000)) (hi := (255933917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 959) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 959) = 1/(959 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-474540549 / 250000000) (-1898162193 / 1000000000) (Real.log (959 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (153416053 / 250000000) ≤ -Real.log (3200 / 5911) ∧
    -Real.log (3200 / 5911) ≤ (613664213 / 1000000000) := by
  have h := checkLog_sound (w := (2711 / 9111)) (n := 12)
    (lo := (153416053 / 250000000)) (hi := (613664213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5911 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5911 / 3200) = 1/(3200 / 5911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (153416053 / 250000000) (613664213 / 1000000000) (Real.log (5911 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5911 / 3200) = -Real.log (3200 / 5911) := by
    rw [show ((5911 / 3200) : ℝ) = ((3200 / 5911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (939271799 / 500000000) ≤ -Real.log (489 / 3200) ∧
    -Real.log (489 / 3200) ≤ (1878543601 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1289)) (n := 12)
    (lo := (246124619 / 500000000)) (hi := (492249239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 489) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 489) = 1/(489 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1878543601 / 1000000000) (-939271799 / 500000000) (Real.log (489 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (662625599 / 1000000000) ≤ -Real.log (1000000 / 1939879) ∧
    -Real.log (1000000 / 1939879) ≤ (414141 / 625000) := by
  have h := checkLog_sound (w := (939879 / 2939879)) (n := 12)
    (lo := (662625599 / 1000000000)) (hi := (414141 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1939879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1939879 / 1000000) = 1/(1000000 / 1939879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (662625599 / 1000000000) (414141 / 625000) (Real.log (1939879 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1939879 / 1000000) = -Real.log (1000000 / 1939879) := by
    rw [show ((1939879 / 1000000) : ℝ) = ((1000000 / 1939879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1405698039 / 500000000) ≤ -Real.log (60121 / 1000000) ∧
    -Real.log (60121 / 1000000) ≤ (2811396083 / 1000000000) := by
  have h := checkLog_sound (w := (2379 / 122621)) (n := 12)
    (lo := (19403679 / 500000000)) (hi := (38807359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 60121) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 60121) = 1/(60121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2811396083 / 1000000000) (-1405698039 / 500000000) (Real.log (60121 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (331587999 / 500000000) ≤ -Real.log (1000000 / 1940947) ∧
    -Real.log (1000000 / 1940947) ≤ (663175999 / 1000000000) := by
  have h := checkLog_sound (w := (940947 / 2940947)) (n := 12)
    (lo := (331587999 / 500000000)) (hi := (663175999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1940947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1940947 / 1000000) = 1/(1000000 / 1940947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (331587999 / 500000000) (663175999 / 1000000000) (Real.log (1940947 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1940947 / 1000000) = -Real.log (1000000 / 1940947) := by
    rw [show ((1940947 / 1000000) : ℝ) = ((1000000 / 1940947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (282931993 / 100000000) ≤ -Real.log (59053 / 1000000) ∧
    -Real.log (59053 / 1000000) ≤ (565863987 / 200000000) := by
  have h := checkLog_sound (w := (3447 / 121553)) (n := 12)
    (lo := (5673121 / 100000000)) (hi := (56731211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59053) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 59053) = 1/(59053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-565863987 / 200000000) (-282931993 / 100000000) (Real.log (59053 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (661972253 / 1000000000) ≤ -Real.log (250000 / 484653) ∧
    -Real.log (250000 / 484653) ≤ (330986127 / 500000000) := by
  have h := checkLog_sound (w := (234653 / 734653)) (n := 12)
    (lo := (661972253 / 1000000000)) (hi := (330986127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484653 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484653 / 250000) = 1/(250000 / 484653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (661972253 / 1000000000) (330986127 / 500000000) (Real.log (484653 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (484653 / 250000) = -Real.log (250000 / 484653) := by
    rw [show ((484653 / 250000) : ℝ) = ((250000 / 484653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (27905409 / 10000000) ≤ -Real.log (15347 / 250000) ∧
    -Real.log (15347 / 250000) ≤ (558108181 / 200000000) := by
  have h := checkLog_sound (w := (139 / 15486)) (n := 12)
    (lo := (897609 / 50000000)) (hi := (17952181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15347) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 15347) = 1/(15347 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-558108181 / 200000000) (-27905409 / 10000000) (Real.log (15347 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (132510273 / 200000000) ≤ -Real.log (200000 / 387947) ∧
    -Real.log (200000 / 387947) ≤ (331275683 / 500000000) := by
  have h := checkLog_sound (w := (187947 / 587947)) (n := 12)
    (lo := (132510273 / 200000000)) (hi := (331275683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387947 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387947 / 200000) = 1/(200000 / 387947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (132510273 / 200000000) (331275683 / 500000000) (Real.log (387947 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (387947 / 200000) = -Real.log (200000 / 387947) := by
    rw [show ((387947 / 200000) : ℝ) = ((200000 / 387947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (702250943 / 250000000) ≤ -Real.log (12053 / 200000) ∧
    -Real.log (12053 / 200000) ≤ (2809003777 / 1000000000) := by
  have h := checkLog_sound (w := (447 / 24553)) (n := 12)
    (lo := (9103763 / 250000000)) (hi := (36415053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12053) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 12053) = 1/(12053 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2809003777 / 1000000000) (-702250943 / 250000000) (Real.log (12053 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1737010839 / 500000000) ≤ -Real.log (500000000000 / 16133123201543) ∧
    -Real.log (500000000000 / 16133123201543) ≤ (868505421 / 250000000) := by
  have h := checkLog_sound (w := (133123201543 / 32133123201543)) (n := 12)
    (lo := (4142889 / 500000000)) (hi := (8285779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16133123201543 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16133123201543 / 16000000000000) = 1/(500000000000 / 16133123201543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1737010839 / 500000000) (868505421 / 250000000) (Real.log (16133123201543 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16133123201543 / 500000000000) = -Real.log (500000000000 / 16133123201543) := by
    rw [show ((16133123201543 / 500000000000) : ℝ) = ((500000000000 / 16133123201543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (436561991 / 125000000) ≤ -Real.log (25000000000 / 821697034867) ∧
    -Real.log (25000000000 / 821697034867) ≤ (1746247967 / 500000000) := by
  have h := checkLog_sound (w := (21697034867 / 1621697034867)) (n := 12)
    (lo := (6690007 / 250000000)) (hi := (26760029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821697034867 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(821697034867 / 800000000000) = 1/(25000000000 / 821697034867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (436561991 / 125000000) (1746247967 / 500000000) (Real.log (821697034867 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (821697034867 / 25000000000) = -Real.log (25000000000 / 821697034867) := by
    rw [show ((821697034867 / 25000000000) : ℝ) = ((25000000000 / 821697034867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3452513153 / 1000000000) ≤ -Real.log (250000000000 / 7894914315501) ∧
    -Real.log (250000000000 / 7894914315501) ≤ (1726256579 / 500000000) := by
  have h := checkLog_sound (w := (3894914315501 / 11894914315501)) (n := 12)
    (lo := (679924433 / 1000000000)) (hi := (339962217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7894914315501 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7894914315501 / 4000000000000) = 1/(250000000000 / 7894914315501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3452513153 / 1000000000) (1726256579 / 500000000) (Real.log (7894914315501 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7894914315501 / 250000000000) = -Real.log (250000000000 / 7894914315501) := by
    rw [show ((7894914315501 / 250000000000) : ℝ) = ((250000000000 / 7894914315501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3471555137 / 1000000000) ≤ -Real.log (500000000000 / 16093379241683) ∧
    -Real.log (500000000000 / 16093379241683) ≤ (3471555143 / 1000000000) := by
  have h := checkLog_sound (w := (93379241683 / 32093379241683)) (n := 12)
    (lo := (5819237 / 1000000000)) (hi := (2909619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16093379241683 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16093379241683 / 16000000000000) = 1/(500000000000 / 16093379241683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3471555137 / 1000000000) (3471555143 / 1000000000) (Real.log (16093379241683 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16093379241683 / 500000000000) = -Real.log (500000000000 / 16093379241683) := by
    rw [show ((16093379241683 / 500000000000) : ℝ) = ((500000000000 / 16093379241683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0148

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0149Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0149
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

theorem reflection_log_1_neg : (654195181 / 1000000000) ≤ -Real.log (6400 / 12311) ∧
    -Real.log (6400 / 12311) ≤ (327097591 / 500000000) := by
  have h := checkLog_sound (w := (5911 / 18711)) (n := 12)
    (lo := (654195181 / 1000000000)) (hi := (327097591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12311 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12311 / 6400) = 1/(6400 / 12311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (654195181 / 1000000000) (327097591 / 500000000) (Real.log (12311 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12311 / 6400) = -Real.log (6400 / 12311) := by
    rw [show ((12311 / 6400) : ℝ) = ((6400 / 12311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1285845389 / 500000000) ≤ -Real.log (489 / 6400) ∧
    -Real.log (489 / 6400) ≤ (1285845391 / 500000000) := by
  have h := checkLog_sound (w := (311 / 1289)) (n := 12)
    (lo := (246124619 / 500000000)) (hi := (492249239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 489) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 489) = 1/(489 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1285845391 / 500000000) (-1285845389 / 500000000) (Real.log (489 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (130684643 / 200000000) ≤ -Real.log (12800 / 24603) ∧
    -Real.log (12800 / 24603) ≤ (40838951 / 62500000) := by
  have h := checkLog_sound (w := (11803 / 37403)) (n := 12)
    (lo := (130684643 / 200000000)) (hi := (40838951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24603 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24603 / 12800) = 1/(12800 / 24603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (130684643 / 200000000) (40838951 / 62500000) (Real.log (24603 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24603 / 12800) = -Real.log (12800 / 24603) := by
    rw [show ((24603 / 12800) : ℝ) = ((12800 / 24603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1276224839 / 500000000) ≤ -Real.log (997 / 12800) ∧
    -Real.log (997 / 12800) ≤ (1276224841 / 500000000) := by
  have h := checkLog_sound (w := (603 / 2597)) (n := 12)
    (lo := (236504069 / 500000000)) (hi := (473008139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 997) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 997) = 1/(997 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1276224841 / 500000000) (-1276224839 / 500000000) (Real.log (997 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (153416053 / 250000000) ≤ -Real.log (3200 / 5911) ∧
    -Real.log (3200 / 5911) ≤ (613664213 / 1000000000) := by
  have h := checkLog_sound (w := (2711 / 9111)) (n := 12)
    (lo := (153416053 / 250000000)) (hi := (613664213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5911 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5911 / 3200) = 1/(3200 / 5911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (153416053 / 250000000) (613664213 / 1000000000) (Real.log (5911 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5911 / 3200) = -Real.log (3200 / 5911) := by
    rw [show ((5911 / 3200) : ℝ) = ((3200 / 5911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (939271799 / 500000000) ≤ -Real.log (489 / 3200) ∧
    -Real.log (489 / 3200) ≤ (1878543601 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1289)) (n := 12)
    (lo := (246124619 / 500000000)) (hi := (492249239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 489) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 489) = 1/(489 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1878543601 / 1000000000) (-939271799 / 500000000) (Real.log (489 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (306027873 / 500000000) ≤ -Real.log (6400 / 11803) ∧
    -Real.log (6400 / 11803) ≤ (612055747 / 1000000000) := by
  have h := checkLog_sound (w := (5403 / 18203)) (n := 12)
    (lo := (306027873 / 500000000)) (hi := (612055747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11803 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11803 / 6400) = 1/(6400 / 11803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (306027873 / 500000000) (612055747 / 1000000000) (Real.log (11803 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11803 / 6400) = -Real.log (6400 / 11803) := by
    rw [show ((11803 / 6400) : ℝ) = ((6400 / 11803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (929651249 / 500000000) ≤ -Real.log (997 / 6400) ∧
    -Real.log (997 / 6400) ≤ (1859302501 / 1000000000) := by
  have h := checkLog_sound (w := (603 / 2597)) (n := 12)
    (lo := (236504069 / 500000000)) (hi := (473008139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 997) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 997) = 1/(997 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1859302501 / 1000000000) (-929651249 / 500000000) (Real.log (997 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (662077477 / 1000000000) ≤ -Real.log (15625 / 30294) ∧
    -Real.log (15625 / 30294) ≤ (331038739 / 500000000) := by
  have h := checkLog_sound (w := (14669 / 45919)) (n := 12)
    (lo := (662077477 / 1000000000)) (hi := (331038739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30294 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30294 / 15625) = 1/(15625 / 30294) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (662077477 / 1000000000) (331038739 / 500000000) (Real.log (30294 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (30294 / 15625) = -Real.log (15625 / 30294) := by
    rw [show ((30294 / 15625) : ℝ) = ((15625 / 30294) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2793869559 / 1000000000) ≤ -Real.log (956 / 15625) ∧
    -Real.log (956 / 15625) ≤ (698467391 / 250000000) := by
  have h := checkLog_sound (w := (329 / 30921)) (n := 12)
    (lo := (21280839 / 1000000000)) (hi := (532021 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15296) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 15296) = 1/(956 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-698467391 / 250000000) (-2793869559 / 1000000000) (Real.log (956 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (132525223 / 200000000) ≤ -Real.log (25000 / 48497) ∧
    -Real.log (25000 / 48497) ≤ (165656529 / 250000000) := by
  have h := checkLog_sound (w := (23497 / 73497)) (n := 12)
    (lo := (132525223 / 200000000)) (hi := (165656529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48497 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48497 / 25000) = 1/(25000 / 48497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (132525223 / 200000000) (165656529 / 250000000) (Real.log (48497 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (48497 / 25000) = -Real.log (25000 / 48497) := by
    rw [show ((48497 / 25000) : ℝ) = ((25000 / 48497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2811412711 / 1000000000) ≤ -Real.log (1503 / 25000) ∧
    -Real.log (1503 / 25000) ≤ (702853179 / 250000000) := by
  have h := checkLog_sound (w := (119 / 6131)) (n := 12)
    (lo := (38823991 / 1000000000)) (hi := (4852999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3006) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 3006) = 1/(1503 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-702853179 / 250000000) (-2811412711 / 1000000000) (Real.log (1503 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (661393837 / 1000000000) ≤ -Real.log (1000000 / 1937491) ∧
    -Real.log (1000000 / 1937491) ≤ (330696919 / 500000000) := by
  have h := checkLog_sound (w := (937491 / 2937491)) (n := 12)
    (lo := (661393837 / 1000000000)) (hi := (330696919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1937491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1937491 / 1000000) = 1/(1000000 / 1937491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (661393837 / 1000000000) (330696919 / 500000000) (Real.log (1937491 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1937491 / 1000000) = -Real.log (1000000 / 1937491) := by
    rw [show ((1937491 / 1000000) : ℝ) = ((1000000 / 1937491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (277244473 / 100000000) ≤ -Real.log (62509 / 1000000) ∧
    -Real.log (62509 / 1000000) ≤ (1386222367 / 500000000) := by
  have h := checkLog_sound (w := (62491 / 187509)) (n := 12)
    (lo := (69300319 / 100000000)) (hi := (693003191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 62509) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 62509) = 1/(62509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1386222367 / 500000000) (-277244473 / 100000000) (Real.log (62509 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (20686649 / 31250000) ≤ -Real.log (1000000 / 1938613) ∧
    -Real.log (1000000 / 1938613) ≤ (661972769 / 1000000000) := by
  have h := checkLog_sound (w := (938613 / 2938613)) (n := 12)
    (lo := (20686649 / 31250000)) (hi := (661972769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1938613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1938613 / 1000000) = 1/(1000000 / 1938613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20686649 / 31250000) (661972769 / 1000000000) (Real.log (1938613 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1938613 / 1000000) = -Real.log (1000000 / 1938613) := by
    rw [show ((1938613 / 1000000) : ℝ) = ((1000000 / 1938613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (279055719 / 100000000) ≤ -Real.log (61387 / 1000000) ∧
    -Real.log (61387 / 1000000) ≤ (558111439 / 200000000) := by
  have h := checkLog_sound (w := (1113 / 123887)) (n := 12)
    (lo := (1796847 / 100000000)) (hi := (17968471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 61387) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 61387) = 1/(61387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-558111439 / 200000000) (-279055719 / 100000000) (Real.log (61387 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (863986759 / 250000000) ≤ -Real.log (250000000000 / 7922071129707) ∧
    -Real.log (250000000000 / 7922071129707) ≤ (3455947041 / 1000000000) := by
  have h := checkLog_sound (w := (3922071129707 / 11922071129707)) (n := 12)
    (lo := (170839579 / 250000000)) (hi := (683358317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7922071129707 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7922071129707 / 4000000000000) = 1/(250000000000 / 7922071129707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (863986759 / 250000000) (3455947041 / 1000000000) (Real.log (7922071129707 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7922071129707 / 250000000000) = -Real.log (250000000000 / 7922071129707) := by
    rw [show ((7922071129707 / 250000000000) : ℝ) = ((250000000000 / 7922071129707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1737019413 / 500000000) ≤ -Real.log (500000000000 / 16133399866933) ∧
    -Real.log (500000000000 / 16133399866933) ≤ (217127427 / 62500000) := by
  have h := checkLog_sound (w := (133399866933 / 32133399866933)) (n := 12)
    (lo := (4151463 / 500000000)) (hi := (8302927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16133399866933 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16133399866933 / 16000000000000) = 1/(500000000000 / 16133399866933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1737019413 / 500000000) (217127427 / 62500000) (Real.log (16133399866933 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (16133399866933 / 500000000000) = -Real.log (500000000000 / 16133399866933) := by
    rw [show ((16133399866933 / 500000000000) : ℝ) = ((500000000000 / 16133399866933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3433838567 / 1000000000) ≤ -Real.log (31250000000 / 968606020733) ∧
    -Real.log (31250000000 / 968606020733) ≤ (858459643 / 250000000) := by
  have h := checkLog_sound (w := (468606020733 / 1468606020733)) (n := 12)
    (lo := (661249847 / 1000000000)) (hi := (82656231 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968606020733 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(968606020733 / 500000000000) = 1/(31250000000 / 968606020733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3433838567 / 1000000000) (858459643 / 250000000) (Real.log (968606020733 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (968606020733 / 31250000000) = -Real.log (31250000000 / 968606020733) := by
    rw [show ((968606020733 / 31250000000) : ℝ) = ((31250000000 / 968606020733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3452529959 / 1000000000) ≤ -Real.log (500000000000 / 15790093993843) ∧
    -Real.log (500000000000 / 15790093993843) ≤ (863132491 / 250000000) := by
  have h := checkLog_sound (w := (7790093993843 / 23790093993843)) (n := 12)
    (lo := (679941239 / 1000000000)) (hi := (16998531 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15790093993843 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15790093993843 / 8000000000000) = 1/(500000000000 / 15790093993843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3452529959 / 1000000000) (863132491 / 250000000) (Real.log (15790093993843 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (15790093993843 / 500000000000) = -Real.log (500000000000 / 15790093993843) := by
    rw [show ((15790093993843 / 500000000000) : ℝ) = ((500000000000 / 15790093993843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0149

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0150Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0150
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

theorem reflection_log_1_neg : (130684643 / 200000000) ≤ -Real.log (12800 / 24603) ∧
    -Real.log (12800 / 24603) ≤ (40838951 / 62500000) := by
  have h := checkLog_sound (w := (11803 / 37403)) (n := 12)
    (lo := (130684643 / 200000000)) (hi := (40838951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24603 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24603 / 12800) = 1/(12800 / 24603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (130684643 / 200000000) (40838951 / 62500000) (Real.log (24603 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24603 / 12800) = -Real.log (12800 / 24603) := by
    rw [show ((24603 / 12800) : ℝ) = ((12800 / 24603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1276224839 / 500000000) ≤ -Real.log (997 / 12800) ∧
    -Real.log (997 / 12800) ≤ (1276224841 / 500000000) := by
  have h := checkLog_sound (w := (603 / 2597)) (n := 12)
    (lo := (236504069 / 500000000)) (hi := (473008139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 997) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 997) = 1/(997 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1276224841 / 500000000) (-1276224839 / 500000000) (Real.log (997 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (652650653 / 1000000000) ≤ -Real.log (1600 / 3073) ∧
    -Real.log (1600 / 3073) ≤ (326325327 / 500000000) := by
  have h := checkLog_sound (w := (1473 / 4673)) (n := 12)
    (lo := (652650653 / 1000000000)) (hi := (326325327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3073 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3073 / 1600) = 1/(1600 / 3073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (652650653 / 1000000000) (326325327 / 500000000) (Real.log (3073 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3073 / 1600) = -Real.log (1600 / 3073) := by
    rw [show ((3073 / 1600) : ℝ) = ((1600 / 3073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (126678591 / 50000000) ≤ -Real.log (127 / 1600) ∧
    -Real.log (127 / 1600) ≤ (158348239 / 62500000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 127) = 1/(127 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-158348239 / 62500000) (-126678591 / 50000000) (Real.log (127 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (306027873 / 500000000) ≤ -Real.log (6400 / 11803) ∧
    -Real.log (6400 / 11803) ≤ (612055747 / 1000000000) := by
  have h := checkLog_sound (w := (5403 / 18203)) (n := 12)
    (lo := (306027873 / 500000000)) (hi := (612055747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11803 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11803 / 6400) = 1/(6400 / 11803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (306027873 / 500000000) (612055747 / 1000000000) (Real.log (11803 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11803 / 6400) = -Real.log (6400 / 11803) := by
    rw [show ((11803 / 6400) : ℝ) = ((6400 / 11803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (929651249 / 500000000) ≤ -Real.log (997 / 6400) ∧
    -Real.log (997 / 6400) ≤ (1859302501 / 1000000000) := by
  have h := checkLog_sound (w := (603 / 2597)) (n := 12)
    (lo := (236504069 / 500000000)) (hi := (473008139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 997) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 997) = 1/(997 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1859302501 / 1000000000) (-929651249 / 500000000) (Real.log (997 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (38152793 / 62500000) ≤ -Real.log (800 / 1473) ∧
    -Real.log (800 / 1473) ≤ (610444689 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 2273)) (n := 12)
    (lo := (38152793 / 62500000)) (hi := (610444689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473 / 800) = 1/(800 / 1473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (38152793 / 62500000) (610444689 / 1000000000) (Real.log (1473 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1473 / 800) = -Real.log (800 / 1473) := by
    rw [show ((1473 / 800) : ℝ) = ((800 / 1473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5751327 / 3125000) ≤ -Real.log (127 / 800) ∧
    -Real.log (127 / 800) ≤ (1840424643 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 127) = 1/(127 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1840424643 / 1000000000) (-5751327 / 3125000) (Real.log (127 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (330765301 / 500000000) ≤ -Real.log (250000 / 484439) ∧
    -Real.log (250000 / 484439) ≤ (661530603 / 1000000000) := by
  have h := checkLog_sound (w := (234439 / 734439)) (n := 12)
    (lo := (330765301 / 500000000)) (hi := (661530603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484439 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484439 / 250000) = 1/(250000 / 484439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (330765301 / 500000000) (661530603 / 1000000000) (Real.log (484439 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (484439 / 250000) = -Real.log (250000 / 484439) := by
    rw [show ((484439 / 250000) : ℝ) = ((250000 / 484439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2776693131 / 1000000000) ≤ -Real.log (15561 / 250000) ∧
    -Real.log (15561 / 250000) ≤ (173543321 / 62500000) := by
  have h := checkLog_sound (w := (32 / 15593)) (n := 12)
    (lo := (4104411 / 1000000000)) (hi := (1026103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15561) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 15561) = 1/(15561 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-173543321 / 62500000) (-2776693131 / 1000000000) (Real.log (15561 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (662077993 / 1000000000) ≤ -Real.log (1000000 / 1938817) ∧
    -Real.log (1000000 / 1938817) ≤ (331038997 / 500000000) := by
  have h := checkLog_sound (w := (938817 / 2938817)) (n := 12)
    (lo := (662077993 / 1000000000)) (hi := (331038997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1938817 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1938817 / 1000000) = 1/(1000000 / 1938817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (662077993 / 1000000000) (331038997 / 500000000) (Real.log (1938817 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1938817 / 1000000) = -Real.log (1000000 / 1938817) := by
    rw [show ((1938817 / 1000000) : ℝ) = ((1000000 / 1938817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2793885903 / 1000000000) ≤ -Real.log (61183 / 1000000) ∧
    -Real.log (61183 / 1000000) ≤ (698471477 / 250000000) := by
  have h := checkLog_sound (w := (1317 / 123683)) (n := 12)
    (lo := (21297183 / 1000000000)) (hi := (665537 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 61183) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 61183) = 1/(61183 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-698471477 / 250000000) (-2793885903 / 1000000000) (Real.log (61183 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (660816119 / 1000000000) ≤ -Real.log (250000 / 484093) ∧
    -Real.log (250000 / 484093) ≤ (16520403 / 25000000) := by
  have h := checkLog_sound (w := (234093 / 734093)) (n := 12)
    (lo := (660816119 / 1000000000)) (hi := (16520403 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484093 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484093 / 250000) = 1/(250000 / 484093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (660816119 / 1000000000) (16520403 / 25000000) (Real.log (484093 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (484093 / 250000) = -Real.log (250000 / 484093) := by
    rw [show ((484093 / 250000) : ℝ) = ((250000 / 484093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (688675413 / 250000000) ≤ -Real.log (15907 / 250000) ∧
    -Real.log (15907 / 250000) ≤ (344337707 / 125000000) := by
  have h := checkLog_sound (w := (15343 / 47157)) (n := 12)
    (lo := (42203757 / 62500000)) (hi := (675260113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 15907) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 15907) = 1/(15907 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-344337707 / 125000000) (-688675413 / 250000000) (Real.log (15907 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (661394353 / 1000000000) ≤ -Real.log (250000 / 484373) ∧
    -Real.log (250000 / 484373) ≤ (330697177 / 500000000) := by
  have h := checkLog_sound (w := (234373 / 734373)) (n := 12)
    (lo := (661394353 / 1000000000)) (hi := (330697177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484373 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484373 / 250000) = 1/(250000 / 484373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (661394353 / 1000000000) (330697177 / 500000000) (Real.log (484373 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (484373 / 250000) = -Real.log (250000 / 484373) := by
    rw [show ((484373 / 250000) : ℝ) = ((250000 / 484373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (346557591 / 125000000) ≤ -Real.log (15627 / 250000) ∧
    -Real.log (15627 / 250000) ≤ (693115183 / 250000000) := by
  have h := checkLog_sound (w := (15623 / 46877)) (n := 12)
    (lo := (173254797 / 250000000)) (hi := (693019189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 15627) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 15627) = 1/(15627 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-693115183 / 250000000) (-346557591 / 125000000) (Real.log (15627 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1719111867 / 500000000) ≤ -Real.log (500000000000 / 15565805539489) ∧
    -Real.log (500000000000 / 15565805539489) ≤ (3438223739 / 1000000000) := by
  have h := checkLog_sound (w := (7565805539489 / 23565805539489)) (n := 12)
    (lo := (332817507 / 500000000)) (hi := (133127003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15565805539489 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15565805539489 / 8000000000000) = 1/(500000000000 / 15565805539489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1719111867 / 500000000) (3438223739 / 1000000000) (Real.log (15565805539489 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15565805539489 / 500000000000) = -Real.log (500000000000 / 15565805539489) := by
    rw [show ((15565805539489 / 500000000000) : ℝ) = ((500000000000 / 15565805539489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (431995487 / 125000000) ≤ -Real.log (500000000000 / 15844409394767) ∧
    -Real.log (500000000000 / 15844409394767) ≤ (3455963901 / 1000000000) := by
  have h := checkLog_sound (w := (7844409394767 / 23844409394767)) (n := 12)
    (lo := (85421897 / 125000000)) (hi := (683375177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15844409394767 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15844409394767 / 8000000000000) = 1/(500000000000 / 15844409394767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (431995487 / 125000000) (3455963901 / 1000000000) (Real.log (15844409394767 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (15844409394767 / 500000000000) = -Real.log (500000000000 / 15844409394767) := by
    rw [show ((15844409394767 / 500000000000) : ℝ) = ((500000000000 / 15844409394767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (341551777 / 100000000) ≤ -Real.log (125000000000 / 3804087822971) ∧
    -Real.log (125000000000 / 3804087822971) ≤ (136620711 / 40000000) := by
  have h := checkLog_sound (w := (1804087822971 / 5804087822971)) (n := 12)
    (lo := (12858581 / 20000000)) (hi := (642929051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3804087822971 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3804087822971 / 2000000000000) = 1/(125000000000 / 3804087822971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (341551777 / 100000000) (136620711 / 40000000) (Real.log (3804087822971 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3804087822971 / 125000000000) = -Real.log (125000000000 / 3804087822971) := by
    rw [show ((3804087822971 / 125000000000) : ℝ) = ((125000000000 / 3804087822971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3433855081 / 1000000000) ≤ -Real.log (500000000000 / 15497952262111) ∧
    -Real.log (500000000000 / 15497952262111) ≤ (1716927543 / 500000000) := by
  have h := checkLog_sound (w := (7497952262111 / 23497952262111)) (n := 12)
    (lo := (661266361 / 1000000000)) (hi := (330633181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15497952262111 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15497952262111 / 8000000000000) = 1/(500000000000 / 15497952262111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3433855081 / 1000000000) (1716927543 / 500000000) (Real.log (15497952262111 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (15497952262111 / 500000000000) = -Real.log (500000000000 / 15497952262111) := by
    rw [show ((15497952262111 / 500000000000) : ℝ) = ((500000000000 / 15497952262111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0150

end


