-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0187Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0187Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:43:12.619823+00:00
-- url     : https://prove2.me/theorems/c697473b-f0b9-455c-b9ed-4e88644e7910
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0187Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0188Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0187Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0188Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0189Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0190Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0191Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0192Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0187Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0188Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0189Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0190Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0191Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0192Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0187Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0188Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0189Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0190Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0191Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0192Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0187Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0188Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0189Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0190Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0191Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0192Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0187Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0187
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

theorem reflection_log_1_neg : (2401749 / 3906250) ≤ -Real.log (1600 / 2959) ∧
    -Real.log (1600 / 2959) ≤ (122969549 / 200000000) := by
  have h := checkLog_sound (w := (1359 / 4559)) (n := 12)
    (lo := (2401749 / 3906250)) (hi := (122969549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2959 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2959 / 1600) = 1/(1600 / 2959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2401749 / 3906250) (122969549 / 200000000) (Real.log (2959 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2959 / 1600) = -Real.log (1600 / 2959) := by
    rw [show ((2959 / 1600) : ℝ) = ((1600 / 2959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1892961973 / 1000000000) ≤ -Real.log (241 / 1600) ∧
    -Real.log (241 / 1600) ≤ (236620247 / 125000000) := by
  have h := checkLog_sound (w := (159 / 641)) (n := 12)
    (lo := (506667613 / 1000000000)) (hi := (253333807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 241) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 241) = 1/(241 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-236620247 / 125000000) (-1892961973 / 1000000000) (Real.log (241 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (306620591 / 500000000) ≤ -Real.log (6400 / 11817) ∧
    -Real.log (6400 / 11817) ≤ (613241183 / 1000000000) := by
  have h := checkLog_sound (w := (5417 / 18217)) (n := 12)
    (lo := (306620591 / 500000000)) (hi := (613241183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11817 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11817 / 6400) = 1/(6400 / 11817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (306620591 / 500000000) (613241183 / 1000000000) (Real.log (11817 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11817 / 6400) = -Real.log (6400 / 11817) := by
    rw [show ((11817 / 6400) : ℝ) = ((6400 / 11817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (468361037 / 250000000) ≤ -Real.log (983 / 6400) ∧
    -Real.log (983 / 6400) ≤ (1873444151 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 2583)) (n := 12)
    (lo := (121787447 / 250000000)) (hi := (487149789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 983) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 983) = 1/(983 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1873444151 / 1000000000) (-468361037 / 250000000) (Real.log (983 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (264946343 / 500000000) ≤ -Real.log (800 / 1359) ∧
    -Real.log (800 / 1359) ≤ (529892687 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 2159)) (n := 12)
    (lo := (264946343 / 500000000)) (hi := (529892687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 800) = 1/(800 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (264946343 / 500000000) (529892687 / 1000000000) (Real.log (1359 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1359 / 800) = -Real.log (800 / 1359) := by
    rw [show ((1359 / 800) : ℝ) = ((800 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1199814793 / 1000000000) ≤ -Real.log (241 / 800) ∧
    -Real.log (241 / 800) ≤ (239962959 / 200000000) := by
  have h := checkLog_sound (w := (159 / 641)) (n := 12)
    (lo := (506667613 / 1000000000)) (hi := (253333807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 241) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 241) = 1/(241 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-239962959 / 200000000) (-1199814793 / 1000000000) (Real.log (241 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (263195673 / 500000000) ≤ -Real.log (3200 / 5417) ∧
    -Real.log (3200 / 5417) ≤ (526391347 / 1000000000) := by
  have h := checkLog_sound (w := (2217 / 8617)) (n := 12)
    (lo := (263195673 / 500000000)) (hi := (526391347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5417 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5417 / 3200) = 1/(3200 / 5417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (263195673 / 500000000) (526391347 / 1000000000) (Real.log (5417 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5417 / 3200) = -Real.log (3200 / 5417) := by
    rw [show ((5417 / 3200) : ℝ) = ((3200 / 5417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (147537121 / 125000000) ≤ -Real.log (983 / 3200) ∧
    -Real.log (983 / 3200) ≤ (118029697 / 100000000) := by
  have h := checkLog_sound (w := (617 / 2583)) (n := 12)
    (lo := (121787447 / 250000000)) (hi := (487149789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 983) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 983) = 1/(983 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118029697 / 100000000) (-147537121 / 125000000) (Real.log (983 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79503831 / 125000000) ≤ -Real.log (125000 / 236121) ∧
    -Real.log (125000 / 236121) ≤ (636030649 / 1000000000) := by
  have h := checkLog_sound (w := (111121 / 361121)) (n := 12)
    (lo := (79503831 / 125000000)) (hi := (636030649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236121 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236121 / 125000) = 1/(125000 / 236121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79503831 / 125000000) (636030649 / 1000000000) (Real.log (236121 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (236121 / 125000) = -Real.log (125000 / 236121) := by
    rw [show ((236121 / 125000) : ℝ) = ((125000 / 236121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2197936829 / 1000000000) ≤ -Real.log (13879 / 125000) ∧
    -Real.log (13879 / 125000) ≤ (2197936833 / 1000000000) := by
  have h := checkLog_sound (w := (873 / 14752)) (n := 12)
    (lo := (118495289 / 1000000000)) (hi := (11849529 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13879) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 13879) = 1/(13879 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2197936833 / 1000000000) (-2197936829 / 1000000000) (Real.log (13879 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31849049 / 50000000) ≤ -Real.log (250000 / 472691) ∧
    -Real.log (250000 / 472691) ≤ (636980981 / 1000000000) := by
  have h := checkLog_sound (w := (222691 / 722691)) (n := 12)
    (lo := (31849049 / 50000000)) (hi := (636980981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((472691 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(472691 / 250000) = 1/(250000 / 472691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31849049 / 50000000) (636980981 / 1000000000) (Real.log (472691 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (472691 / 250000) = -Real.log (250000 / 472691) := by
    rw [show ((472691 / 250000) : ℝ) = ((250000 / 472691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2214244597 / 1000000000) ≤ -Real.log (27309 / 250000) ∧
    -Real.log (27309 / 250000) ≤ (2214244601 / 1000000000) := by
  have h := checkLog_sound (w := (3941 / 58559)) (n := 12)
    (lo := (134803057 / 1000000000)) (hi := (67401529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27309) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 27309) = 1/(27309 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2214244601 / 1000000000) (-2214244597 / 1000000000) (Real.log (27309 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (632575713 / 1000000000) ≤ -Real.log (1000000 / 1882453) ∧
    -Real.log (1000000 / 1882453) ≤ (316287857 / 500000000) := by
  have h := checkLog_sound (w := (882453 / 2882453)) (n := 12)
    (lo := (632575713 / 1000000000)) (hi := (316287857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1882453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1882453 / 1000000) = 1/(1000000 / 1882453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (632575713 / 1000000000) (316287857 / 500000000) (Real.log (1882453 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1882453 / 1000000) = -Real.log (1000000 / 1882453) := by
    rw [show ((1882453 / 1000000) : ℝ) = ((1000000 / 1882453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2140917023 / 1000000000) ≤ -Real.log (117547 / 1000000) ∧
    -Real.log (117547 / 1000000) ≤ (2140917027 / 1000000000) := by
  have h := checkLog_sound (w := (7453 / 242547)) (n := 12)
    (lo := (61475483 / 1000000000)) (hi := (15368871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 117547) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 117547) = 1/(117547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2140917027 / 1000000000) (-2140917023 / 1000000000) (Real.log (117547 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (158421603 / 250000000) ≤ -Real.log (200000 / 376909) ∧
    -Real.log (200000 / 376909) ≤ (633686413 / 1000000000) := by
  have h := checkLog_sound (w := (176909 / 576909)) (n := 12)
    (lo := (158421603 / 250000000)) (hi := (633686413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376909 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376909 / 200000) = 1/(200000 / 376909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (158421603 / 250000000) (633686413 / 1000000000) (Real.log (376909 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (376909 / 200000) = -Real.log (200000 / 376909) := by
    rw [show ((376909 / 200000) : ℝ) = ((200000 / 376909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2158874433 / 1000000000) ≤ -Real.log (23091 / 200000) ∧
    -Real.log (23091 / 200000) ≤ (2158874437 / 1000000000) := by
  have h := checkLog_sound (w := (1909 / 48091)) (n := 12)
    (lo := (79432893 / 1000000000)) (hi := (39716447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23091) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 23091) = 1/(23091 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2158874437 / 1000000000) (-2158874433 / 1000000000) (Real.log (23091 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (708491869 / 250000000) ≤ -Real.log (250000000000 / 4253206282873) ∧
    -Real.log (250000000000 / 4253206282873) ≤ (2833967481 / 1000000000) := by
  have h := checkLog_sound (w := (253206282873 / 8253206282873)) (n := 12)
    (lo := (15344689 / 250000000)) (hi := (61378757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4253206282873 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4253206282873 / 4000000000000) = 1/(250000000000 / 4253206282873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (708491869 / 250000000) (2833967481 / 1000000000) (Real.log (4253206282873 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4253206282873 / 250000000000) = -Real.log (250000000000 / 4253206282873) := by
    rw [show ((4253206282873 / 250000000000) : ℝ) = ((250000000000 / 4253206282873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2851225577 / 1000000000) ≤ -Real.log (25000000000 / 432724559669) ∧
    -Real.log (25000000000 / 432724559669) ≤ (1425612791 / 500000000) := by
  have h := checkLog_sound (w := (32724559669 / 832724559669)) (n := 12)
    (lo := (78636857 / 1000000000)) (hi := (39318429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432724559669 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(432724559669 / 400000000000) = 1/(25000000000 / 432724559669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2851225577 / 1000000000) (1425612791 / 500000000) (Real.log (432724559669 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (432724559669 / 25000000000) = -Real.log (25000000000 / 432724559669) := by
    rw [show ((432724559669 / 25000000000) : ℝ) = ((25000000000 / 432724559669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5416978 / 1953125) ≤ -Real.log (50000000000 / 800723540371) ∧
    -Real.log (50000000000 / 800723540371) ≤ (2773492741 / 1000000000) := by
  have h := checkLog_sound (w := (723540371 / 1600723540371)) (n := 12)
    (lo := (56501 / 62500000)) (hi := (904017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800723540371 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800723540371 / 800000000000) = 1/(50000000000 / 800723540371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (5416978 / 1953125) (2773492741 / 1000000000) (Real.log (800723540371 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (800723540371 / 50000000000) = -Real.log (50000000000 / 800723540371) := by
    rw [show ((800723540371 / 50000000000) : ℝ) = ((50000000000 / 800723540371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (558512169 / 200000000) ≤ -Real.log (500000000000 / 8161383222901) ∧
    -Real.log (500000000000 / 8161383222901) ≤ (55851217 / 20000000) := by
  have h := checkLog_sound (w := (161383222901 / 16161383222901)) (n := 12)
    (lo := (159777 / 8000000)) (hi := (9986063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8161383222901 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8161383222901 / 8000000000000) = 1/(500000000000 / 8161383222901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (558512169 / 200000000) (55851217 / 20000000) (Real.log (8161383222901 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8161383222901 / 500000000000) = -Real.log (500000000000 / 8161383222901) := by
    rw [show ((8161383222901 / 500000000000) : ℝ) = ((500000000000 / 8161383222901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0187

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0188Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0188
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

theorem reflection_log_1_neg : (306620591 / 500000000) ≤ -Real.log (6400 / 11817) ∧
    -Real.log (6400 / 11817) ≤ (613241183 / 1000000000) := by
  have h := checkLog_sound (w := (5417 / 18217)) (n := 12)
    (lo := (306620591 / 500000000)) (hi := (613241183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11817 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11817 / 6400) = 1/(6400 / 11817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (306620591 / 500000000) (613241183 / 1000000000) (Real.log (11817 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11817 / 6400) = -Real.log (6400 / 11817) := by
    rw [show ((11817 / 6400) : ℝ) = ((6400 / 11817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (468361037 / 250000000) ≤ -Real.log (983 / 6400) ∧
    -Real.log (983 / 6400) ≤ (1873444151 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 2583)) (n := 12)
    (lo := (121787447 / 250000000)) (hi := (487149789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 983) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 983) = 1/(983 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1873444151 / 1000000000) (-468361037 / 250000000) (Real.log (983 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (122326407 / 200000000) ≤ -Real.log (3200 / 5899) ∧
    -Real.log (3200 / 5899) ≤ (152908009 / 250000000) := by
  have h := checkLog_sound (w := (2699 / 9099)) (n := 12)
    (lo := (122326407 / 200000000)) (hi := (152908009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5899 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5899 / 3200) = 1/(3200 / 5899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (122326407 / 200000000) (152908009 / 250000000) (Real.log (5899 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5899 / 3200) = -Real.log (3200 / 5899) := by
    rw [show ((5899 / 3200) : ℝ) = ((3200 / 5899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (927149993 / 500000000) ≤ -Real.log (501 / 3200) ∧
    -Real.log (501 / 3200) ≤ (1854299989 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1301)) (n := 12)
    (lo := (234002813 / 500000000)) (hi := (468005627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 501) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 501) = 1/(501 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1854299989 / 1000000000) (-927149993 / 500000000) (Real.log (501 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (263195673 / 500000000) ≤ -Real.log (3200 / 5417) ∧
    -Real.log (3200 / 5417) ≤ (526391347 / 1000000000) := by
  have h := checkLog_sound (w := (2217 / 8617)) (n := 12)
    (lo := (263195673 / 500000000)) (hi := (526391347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5417 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5417 / 3200) = 1/(3200 / 5417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (263195673 / 500000000) (526391347 / 1000000000) (Real.log (5417 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5417 / 3200) = -Real.log (3200 / 5417) := by
    rw [show ((5417 / 3200) : ℝ) = ((3200 / 5417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (147537121 / 125000000) ≤ -Real.log (983 / 3200) ∧
    -Real.log (983 / 3200) ≤ (118029697 / 100000000) := by
  have h := checkLog_sound (w := (617 / 2583)) (n := 12)
    (lo := (121787447 / 250000000)) (hi := (487149789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 983) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 983) = 1/(983 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118029697 / 100000000) (-147537121 / 125000000) (Real.log (983 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (65359713 / 125000000) ≤ -Real.log (1600 / 2699) ∧
    -Real.log (1600 / 2699) ≤ (104575541 / 200000000) := by
  have h := checkLog_sound (w := (1099 / 4299)) (n := 12)
    (lo := (65359713 / 125000000)) (hi := (104575541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2699 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2699 / 1600) = 1/(1600 / 2699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (65359713 / 125000000) (104575541 / 200000000) (Real.log (2699 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2699 / 1600) = -Real.log (1600 / 2699) := by
    rw [show ((2699 / 1600) : ℝ) = ((1600 / 2699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (580576403 / 500000000) ≤ -Real.log (501 / 1600) ∧
    -Real.log (501 / 1600) ≤ (145144101 / 125000000) := by
  have h := checkLog_sound (w := (299 / 1301)) (n := 12)
    (lo := (234002813 / 500000000)) (hi := (468005627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 501) = 1/(501 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-145144101 / 125000000) (-580576403 / 500000000) (Real.log (501 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (248081 / 390625) ≤ -Real.log (1000000 / 1887187) ∧
    -Real.log (1000000 / 1887187) ≤ (635087361 / 1000000000) := by
  have h := checkLog_sound (w := (887187 / 2887187)) (n := 12)
    (lo := (248081 / 390625)) (hi := (635087361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1887187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1887187 / 1000000) = 1/(1000000 / 1887187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (248081 / 390625) (635087361 / 1000000000) (Real.log (1887187 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1887187 / 1000000) = -Real.log (1000000 / 1887187) := by
    rw [show ((1887187 / 1000000) : ℝ) = ((1000000 / 1887187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (136376481 / 62500000) ≤ -Real.log (112813 / 1000000) ∧
    -Real.log (112813 / 1000000) ≤ (21820237 / 10000000) := by
  have h := checkLog_sound (w := (12187 / 237813)) (n := 12)
    (lo := (25645539 / 250000000)) (hi := (102582157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112813) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 112813) = 1/(112813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21820237 / 10000000) (-136376481 / 62500000) (Real.log (112813 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (636031177 / 1000000000) ≤ -Real.log (1000000 / 1888969) ∧
    -Real.log (1000000 / 1888969) ≤ (318015589 / 500000000) := by
  have h := checkLog_sound (w := (888969 / 2888969)) (n := 12)
    (lo := (636031177 / 1000000000)) (hi := (318015589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1888969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1888969 / 1000000) = 1/(1000000 / 1888969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (636031177 / 1000000000) (318015589 / 500000000) (Real.log (1888969 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1888969 / 1000000) = -Real.log (1000000 / 1888969) := by
    rw [show ((1888969 / 1000000) : ℝ) = ((1000000 / 1888969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (439589167 / 200000000) ≤ -Real.log (111031 / 1000000) ∧
    -Real.log (111031 / 1000000) ≤ (2197945839 / 1000000000) := by
  have h := checkLog_sound (w := (13969 / 236031)) (n := 12)
    (lo := (23700859 / 200000000)) (hi := (14813037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 111031) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 111031) = 1/(111031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2197945839 / 1000000000) (-439589167 / 200000000) (Real.log (111031 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (315733219 / 500000000) ≤ -Real.log (500000 / 940183) ∧
    -Real.log (500000 / 940183) ≤ (631466439 / 1000000000) := by
  have h := checkLog_sound (w := (440183 / 1440183)) (n := 12)
    (lo := (315733219 / 500000000)) (hi := (631466439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940183 / 500000) = 1/(500000 / 940183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (315733219 / 500000000) (631466439 / 1000000000) (Real.log (940183 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (940183 / 500000) = -Real.log (500000 / 940183) := by
    rw [show ((940183 / 500000) : ℝ) = ((500000 / 940183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (424663639 / 200000000) ≤ -Real.log (59817 / 500000) ∧
    -Real.log (59817 / 500000) ≤ (2123318199 / 1000000000) := by
  have h := checkLog_sound (w := (2683 / 122317)) (n := 12)
    (lo := (8775331 / 200000000)) (hi := (2742291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59817) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 59817) = 1/(59817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2123318199 / 1000000000) (-424663639 / 200000000) (Real.log (59817 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (158144061 / 250000000) ≤ -Real.log (500000 / 941227) ∧
    -Real.log (500000 / 941227) ≤ (126515249 / 200000000) := by
  have h := checkLog_sound (w := (441227 / 1441227)) (n := 12)
    (lo := (158144061 / 250000000)) (hi := (126515249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941227 / 500000) = 1/(500000 / 941227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (158144061 / 250000000) (126515249 / 200000000) (Real.log (941227 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (941227 / 500000) = -Real.log (500000 / 941227) := by
    rw [show ((941227 / 500000) : ℝ) = ((500000 / 941227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (214092553 / 100000000) ≤ -Real.log (58773 / 500000) ∧
    -Real.log (58773 / 500000) ≤ (1070462767 / 500000000) := by
  have h := checkLog_sound (w := (3727 / 121273)) (n := 12)
    (lo := (6148399 / 100000000)) (hi := (61483991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 58773) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 58773) = 1/(58773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1070462767 / 500000000) (-214092553 / 100000000) (Real.log (58773 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (176069441 / 62500000) ≤ -Real.log (250000000000 / 4182113320273) ∧
    -Real.log (250000000000 / 4182113320273) ≤ (2817111061 / 1000000000) := by
  have h := checkLog_sound (w := (182113320273 / 8182113320273)) (n := 12)
    (lo := (1391323 / 31250000)) (hi := (44522337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4182113320273 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4182113320273 / 4000000000000) = 1/(250000000000 / 4182113320273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (176069441 / 62500000) (2817111061 / 1000000000) (Real.log (4182113320273 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4182113320273 / 250000000000) = -Real.log (250000000000 / 4182113320273) := by
    rw [show ((4182113320273 / 250000000000) : ℝ) = ((250000000000 / 4182113320273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (708494253 / 250000000) ≤ -Real.log (100000000000 / 1701298736389) ∧
    -Real.log (100000000000 / 1701298736389) ≤ (2833977017 / 1000000000) := by
  have h := checkLog_sound (w := (101298736389 / 3301298736389)) (n := 12)
    (lo := (15347073 / 250000000)) (hi := (61388293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1701298736389 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1701298736389 / 1600000000000) = 1/(100000000000 / 1701298736389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (708494253 / 250000000) (2833977017 / 1000000000) (Real.log (1701298736389 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1701298736389 / 100000000000) = -Real.log (100000000000 / 1701298736389) := by
    rw [show ((1701298736389 / 100000000000) : ℝ) = ((100000000000 / 1701298736389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2754784633 / 1000000000) ≤ -Real.log (100000000000 / 1571765551599) ∧
    -Real.log (100000000000 / 1571765551599) ≤ (2754784637 / 1000000000) := by
  have h := checkLog_sound (w := (771765551599 / 2371765551599)) (n := 12)
    (lo := (675343093 / 1000000000)) (hi := (337671547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1571765551599 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1571765551599 / 800000000000) = 1/(100000000000 / 1571765551599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2754784633 / 1000000000) (2754784637 / 1000000000) (Real.log (1571765551599 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1571765551599 / 100000000000) = -Real.log (100000000000 / 1571765551599) := by
    rw [show ((1571765551599 / 100000000000) : ℝ) = ((100000000000 / 1571765551599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (110940071 / 40000000) ≤ -Real.log (500000000000 / 8007307777381) ∧
    -Real.log (500000000000 / 8007307777381) ≤ (138675089 / 50000000) := by
  have h := checkLog_sound (w := (7307777381 / 16007307777381)) (n := 12)
    (lo := (182611 / 200000000)) (hi := (28533 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8007307777381 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8007307777381 / 8000000000000) = 1/(500000000000 / 8007307777381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (110940071 / 40000000) (138675089 / 50000000) (Real.log (8007307777381 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8007307777381 / 500000000000) = -Real.log (500000000000 / 8007307777381) := by
    rw [show ((8007307777381 / 500000000000) : ℝ) = ((500000000000 / 8007307777381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0188

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0189Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0189
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

theorem reflection_log_1_neg : (122326407 / 200000000) ≤ -Real.log (3200 / 5899) ∧
    -Real.log (3200 / 5899) ≤ (152908009 / 250000000) := by
  have h := checkLog_sound (w := (2699 / 9099)) (n := 12)
    (lo := (122326407 / 200000000)) (hi := (152908009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5899 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5899 / 3200) = 1/(3200 / 5899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (122326407 / 200000000) (152908009 / 250000000) (Real.log (5899 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5899 / 3200) = -Real.log (3200 / 5899) := by
    rw [show ((5899 / 3200) : ℝ) = ((3200 / 5899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (927149993 / 500000000) ≤ -Real.log (501 / 3200) ∧
    -Real.log (501 / 3200) ≤ (1854299989 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1301)) (n := 12)
    (lo := (234002813 / 500000000)) (hi := (468005627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 501) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 501) = 1/(501 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1854299989 / 1000000000) (-927149993 / 500000000) (Real.log (501 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (305010147 / 500000000) ≤ -Real.log (6400 / 11779) ∧
    -Real.log (6400 / 11779) ≤ (122004059 / 200000000) := by
  have h := checkLog_sound (w := (5379 / 18179)) (n := 12)
    (lo := (305010147 / 500000000)) (hi := (122004059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11779 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11779 / 6400) = 1/(6400 / 11779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (305010147 / 500000000) (122004059 / 200000000) (Real.log (11779 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11779 / 6400) = -Real.log (6400 / 11779) := by
    rw [show ((11779 / 6400) : ℝ) = ((6400 / 11779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36710309 / 20000000) ≤ -Real.log (1021 / 6400) ∧
    -Real.log (1021 / 6400) ≤ (1835515453 / 1000000000) := by
  have h := checkLog_sound (w := (579 / 2621)) (n := 12)
    (lo := (44922109 / 100000000)) (hi := (449221091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1021) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1021) = 1/(1021 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1835515453 / 1000000000) (-36710309 / 20000000) (Real.log (1021 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (65359713 / 125000000) ≤ -Real.log (1600 / 2699) ∧
    -Real.log (1600 / 2699) ≤ (104575541 / 200000000) := by
  have h := checkLog_sound (w := (1099 / 4299)) (n := 12)
    (lo := (65359713 / 125000000)) (hi := (104575541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2699 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2699 / 1600) = 1/(1600 / 2699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (65359713 / 125000000) (104575541 / 200000000) (Real.log (2699 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2699 / 1600) = -Real.log (1600 / 2699) := by
    rw [show ((2699 / 1600) : ℝ) = ((1600 / 2699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (580576403 / 500000000) ≤ -Real.log (501 / 1600) ∧
    -Real.log (501 / 1600) ≤ (145144101 / 125000000) := by
  have h := checkLog_sound (w := (299 / 1301)) (n := 12)
    (lo := (234002813 / 500000000)) (hi := (468005627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 501) = 1/(501 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-145144101 / 125000000) (-580576403 / 500000000) (Real.log (501 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (519351673 / 1000000000) ≤ -Real.log (3200 / 5379) ∧
    -Real.log (3200 / 5379) ≤ (259675837 / 500000000) := by
  have h := checkLog_sound (w := (2179 / 8579)) (n := 12)
    (lo := (519351673 / 1000000000)) (hi := (259675837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5379 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5379 / 3200) = 1/(3200 / 5379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (519351673 / 1000000000) (259675837 / 500000000) (Real.log (5379 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5379 / 3200) = -Real.log (3200 / 5379) := by
    rw [show ((5379 / 3200) : ℝ) = ((3200 / 5379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114236827 / 100000000) ≤ -Real.log (1021 / 3200) ∧
    -Real.log (1021 / 3200) ≤ (71398017 / 62500000) := by
  have h := checkLog_sound (w := (579 / 2621)) (n := 12)
    (lo := (44922109 / 100000000)) (hi := (449221091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1021) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1021) = 1/(1021 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-71398017 / 62500000) (-114236827 / 100000000) (Real.log (1021 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (634150077 / 1000000000) ≤ -Real.log (1000000 / 1885419) ∧
    -Real.log (1000000 / 1885419) ≤ (317075039 / 500000000) := by
  have h := checkLog_sound (w := (885419 / 2885419)) (n := 12)
    (lo := (634150077 / 1000000000)) (hi := (317075039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1885419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1885419 / 1000000) = 1/(1000000 / 1885419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (634150077 / 1000000000) (317075039 / 500000000) (Real.log (1885419 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1885419 / 1000000) = -Real.log (1000000 / 1885419) := by
    rw [show ((1885419 / 1000000) : ℝ) = ((1000000 / 1885419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (6770229 / 3125000) ≤ -Real.log (114581 / 1000000) ∧
    -Real.log (114581 / 1000000) ≤ (541618321 / 250000000) := by
  have h := checkLog_sound (w := (10419 / 239581)) (n := 12)
    (lo := (4351587 / 50000000)) (hi := (87031741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114581) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 114581) = 1/(114581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-541618321 / 250000000) (-6770229 / 3125000) (Real.log (114581 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (63508789 / 100000000) ≤ -Real.log (250000 / 471797) ∧
    -Real.log (250000 / 471797) ≤ (635087891 / 1000000000) := by
  have h := checkLog_sound (w := (221797 / 721797)) (n := 12)
    (lo := (63508789 / 100000000)) (hi := (635087891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471797 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471797 / 250000) = 1/(250000 / 471797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (63508789 / 100000000) (635087891 / 1000000000) (Real.log (471797 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (471797 / 250000) = -Real.log (250000 / 471797) := by
    rw [show ((471797 / 250000) : ℝ) = ((250000 / 471797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27275407 / 12500000) ≤ -Real.log (28203 / 250000) ∧
    -Real.log (28203 / 250000) ≤ (545508141 / 250000000) := by
  have h := checkLog_sound (w := (3047 / 59453)) (n := 12)
    (lo := (5129551 / 50000000)) (hi := (102591021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28203) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 28203) = 1/(28203 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-545508141 / 250000000) (-27275407 / 12500000) (Real.log (28203 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (315179563 / 500000000) ≤ -Real.log (200000 / 375657) ∧
    -Real.log (200000 / 375657) ≤ (630359127 / 1000000000) := by
  have h := checkLog_sound (w := (175657 / 575657)) (n := 12)
    (lo := (315179563 / 500000000)) (hi := (630359127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375657 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375657 / 200000) = 1/(200000 / 375657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (315179563 / 500000000) (630359127 / 1000000000) (Real.log (375657 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (375657 / 200000) = -Real.log (200000 / 375657) := by
    rw [show ((375657 / 200000) : ℝ) = ((200000 / 375657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2106073031 / 1000000000) ≤ -Real.log (24343 / 200000) ∧
    -Real.log (24343 / 200000) ≤ (421214607 / 200000000) := by
  have h := checkLog_sound (w := (657 / 49343)) (n := 12)
    (lo := (26631491 / 1000000000)) (hi := (6657873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24343) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 24343) = 1/(24343 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-421214607 / 200000000) (-2106073031 / 1000000000) (Real.log (24343 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (63146697 / 100000000) ≤ -Real.log (1000000 / 1880367) ∧
    -Real.log (1000000 / 1880367) ≤ (631466971 / 1000000000) := by
  have h := checkLog_sound (w := (880367 / 2880367)) (n := 12)
    (lo := (63146697 / 100000000)) (hi := (631466971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1880367 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1880367 / 1000000) = 1/(1000000 / 1880367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (63146697 / 100000000) (631466971 / 1000000000) (Real.log (1880367 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1880367 / 1000000) = -Real.log (1000000 / 1880367) := by
    rw [show ((1880367 / 1000000) : ℝ) = ((1000000 / 1880367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1061663277 / 500000000) ≤ -Real.log (119633 / 1000000) ∧
    -Real.log (119633 / 1000000) ≤ (1061663279 / 500000000) := by
  have h := checkLog_sound (w := (5367 / 244633)) (n := 12)
    (lo := (21942507 / 500000000)) (hi := (8777003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 119633) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 119633) = 1/(119633 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1061663279 / 500000000) (-1061663277 / 500000000) (Real.log (119633 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2800623357 / 1000000000) ≤ -Real.log (5000000000 / 82274504499) ∧
    -Real.log (5000000000 / 82274504499) ≤ (1400311681 / 500000000) := by
  have h := checkLog_sound (w := (2274504499 / 162274504499)) (n := 12)
    (lo := (28034637 / 1000000000)) (hi := (14017319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82274504499 / 80000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(82274504499 / 80000000000) = 1/(5000000000 / 82274504499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2800623357 / 1000000000) (1400311681 / 500000000) (Real.log (82274504499 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (82274504499 / 5000000000) = -Real.log (5000000000 / 82274504499) := by
    rw [show ((82274504499 / 5000000000) : ℝ) = ((5000000000 / 82274504499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (56342409 / 20000000) ≤ -Real.log (250000000000 / 4182152607879) ∧
    -Real.log (250000000000 / 4182152607879) ≤ (563424091 / 200000000) := by
  have h := checkLog_sound (w := (182152607879 / 8182152607879)) (n := 12)
    (lo := (4453173 / 100000000)) (hi := (44531731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4182152607879 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4182152607879 / 4000000000000) = 1/(250000000000 / 4182152607879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (56342409 / 20000000) (563424091 / 200000000) (Real.log (4182152607879 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4182152607879 / 250000000000) = -Real.log (250000000000 / 4182152607879) := by
    rw [show ((4182152607879 / 250000000000) : ℝ) = ((250000000000 / 4182152607879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2736432157 / 1000000000) ≤ -Real.log (100000000000 / 1543182845171) ∧
    -Real.log (100000000000 / 1543182845171) ≤ (2736432161 / 1000000000) := by
  have h := checkLog_sound (w := (743182845171 / 2343182845171)) (n := 12)
    (lo := (656990617 / 1000000000)) (hi := (328495309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1543182845171 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1543182845171 / 800000000000) = 1/(100000000000 / 1543182845171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2736432157 / 1000000000) (2736432161 / 1000000000) (Real.log (1543182845171 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1543182845171 / 100000000000) = -Real.log (100000000000 / 1543182845171) := by
    rw [show ((1543182845171 / 100000000000) : ℝ) = ((100000000000 / 1543182845171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (688698381 / 250000000) ≤ -Real.log (500000000000 / 7858897628581) ∧
    -Real.log (500000000000 / 7858897628581) ≤ (344349191 / 125000000) := by
  have h := checkLog_sound (w := (3858897628581 / 11858897628581)) (n := 12)
    (lo := (42209499 / 62500000)) (hi := (135070397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7858897628581 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7858897628581 / 4000000000000) = 1/(500000000000 / 7858897628581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (688698381 / 250000000) (344349191 / 125000000) (Real.log (7858897628581 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7858897628581 / 500000000000) = -Real.log (500000000000 / 7858897628581) := by
    rw [show ((7858897628581 / 500000000000) : ℝ) = ((500000000000 / 7858897628581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0189

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0190Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0190
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

theorem reflection_log_1_neg : (305010147 / 500000000) ≤ -Real.log (6400 / 11779) ∧
    -Real.log (6400 / 11779) ≤ (122004059 / 200000000) := by
  have h := checkLog_sound (w := (5379 / 18179)) (n := 12)
    (lo := (305010147 / 500000000)) (hi := (122004059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11779 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11779 / 6400) = 1/(6400 / 11779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (305010147 / 500000000) (122004059 / 200000000) (Real.log (11779 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11779 / 6400) = -Real.log (6400 / 11779) := by
    rw [show ((11779 / 6400) : ℝ) = ((6400 / 11779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36710309 / 20000000) ≤ -Real.log (1021 / 6400) ∧
    -Real.log (1021 / 6400) ≤ (1835515453 / 1000000000) := by
  have h := checkLog_sound (w := (579 / 2621)) (n := 12)
    (lo := (44922109 / 100000000)) (hi := (449221091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1021) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1021) = 1/(1021 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1835515453 / 1000000000) (-36710309 / 20000000) (Real.log (1021 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (9506343 / 15625000) ≤ -Real.log (80 / 147) ∧
    -Real.log (80 / 147) ≤ (608405953 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 227)) (n := 12)
    (lo := (9506343 / 15625000)) (hi := (608405953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147 / 80) = 1/(80 / 147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (9506343 / 15625000) (608405953 / 1000000000) (Real.log (147 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (147 / 80) = -Real.log (80 / 147) := by
    rw [show ((147 / 80) : ℝ) = ((80 / 147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (454269319 / 250000000) ≤ -Real.log (13 / 80) ∧
    -Real.log (13 / 80) ≤ (1817077279 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(20 / 13) = 1/(13 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1817077279 / 1000000000) (-454269319 / 250000000) (Real.log (13 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (519351673 / 1000000000) ≤ -Real.log (3200 / 5379) ∧
    -Real.log (3200 / 5379) ≤ (259675837 / 500000000) := by
  have h := checkLog_sound (w := (2179 / 8579)) (n := 12)
    (lo := (519351673 / 1000000000)) (hi := (259675837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5379 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5379 / 3200) = 1/(3200 / 5379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (519351673 / 1000000000) (259675837 / 500000000) (Real.log (5379 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5379 / 3200) = -Real.log (3200 / 5379) := by
    rw [show ((5379 / 3200) : ℝ) = ((3200 / 5379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (114236827 / 100000000) ≤ -Real.log (1021 / 3200) ∧
    -Real.log (1021 / 3200) ≤ (71398017 / 62500000) := by
  have h := checkLog_sound (w := (579 / 2621)) (n := 12)
    (lo := (44922109 / 100000000)) (hi := (449221091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1021) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1021) = 1/(1021 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71398017 / 62500000) (-114236827 / 100000000) (Real.log (1021 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (103162633 / 200000000) ≤ -Real.log (40 / 67) ∧
    -Real.log (40 / 67) ≤ (257906583 / 500000000) := by
  have h := checkLog_sound (w := (27 / 107)) (n := 12)
    (lo := (103162633 / 200000000)) (hi := (257906583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67 / 40) = 1/(40 / 67) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (103162633 / 200000000) (257906583 / 500000000) (Real.log (67 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (67 / 40) = -Real.log (40 / 67) := by
    rw [show ((67 / 40) : ℝ) = ((40 / 67) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (70245631 / 62500000) ≤ -Real.log (13 / 40) ∧
    -Real.log (13 / 40) ≤ (561965049 / 500000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 13) = 1/(13 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-561965049 / 500000000) (-70245631 / 62500000) (Real.log (13 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2473511 / 3906250) ≤ -Real.log (62500 / 117729) ∧
    -Real.log (62500 / 117729) ≤ (633218817 / 1000000000) := by
  have h := checkLog_sound (w := (55229 / 180229)) (n := 12)
    (lo := (2473511 / 3906250)) (hi := (633218817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117729 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117729 / 62500) = 1/(62500 / 117729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2473511 / 3906250) (633218817 / 1000000000) (Real.log (117729 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (117729 / 62500) = -Real.log (62500 / 117729) := by
    rw [show ((117729 / 62500) : ℝ) = ((62500 / 117729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2151272721 / 1000000000) ≤ -Real.log (7271 / 62500) ∧
    -Real.log (7271 / 62500) ≤ (86050909 / 40000000) := by
  have h := checkLog_sound (w := (1083 / 30167)) (n := 12)
    (lo := (71831181 / 1000000000)) (hi := (35915591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14542) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 14542) = 1/(7271 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86050909 / 40000000) (-2151272721 / 1000000000) (Real.log (7271 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (634150607 / 1000000000) ≤ -Real.log (50000 / 94271) ∧
    -Real.log (50000 / 94271) ≤ (39634413 / 62500000) := by
  have h := checkLog_sound (w := (44271 / 144271)) (n := 12)
    (lo := (634150607 / 1000000000)) (hi := (39634413 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94271 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94271 / 50000) = 1/(50000 / 94271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (634150607 / 1000000000) (39634413 / 62500000) (Real.log (94271 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (94271 / 50000) = -Real.log (50000 / 94271) := by
    rw [show ((94271 / 50000) : ℝ) = ((50000 / 94271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (270810251 / 125000000) ≤ -Real.log (5729 / 50000) ∧
    -Real.log (5729 / 50000) ≤ (541620503 / 250000000) := by
  have h := checkLog_sound (w := (521 / 11979)) (n := 12)
    (lo := (21760117 / 250000000)) (hi := (87040469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5729) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 5729) = 1/(5729 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-541620503 / 250000000) (-270810251 / 125000000) (Real.log (5729 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (314626359 / 500000000) ≤ -Real.log (62500 / 117263) ∧
    -Real.log (62500 / 117263) ≤ (629252719 / 1000000000) := by
  have h := checkLog_sound (w := (54763 / 179763)) (n := 12)
    (lo := (314626359 / 500000000)) (hi := (629252719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117263 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117263 / 62500) = 1/(62500 / 117263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (314626359 / 500000000) (629252719 / 1000000000) (Real.log (117263 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (117263 / 62500) = -Real.log (62500 / 117263) := by
    rw [show ((117263 / 62500) : ℝ) = ((62500 / 117263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2089152539 / 1000000000) ≤ -Real.log (7737 / 62500) ∧
    -Real.log (7737 / 62500) ≤ (2089152543 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 31099)) (n := 12)
    (lo := (9710999 / 1000000000)) (hi := (9711 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15474) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 15474) = 1/(7737 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2089152543 / 1000000000) (-2089152539 / 1000000000) (Real.log (7737 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (315179829 / 500000000) ≤ -Real.log (500000 / 939143) ∧
    -Real.log (500000 / 939143) ≤ (630359659 / 1000000000) := by
  have h := checkLog_sound (w := (439143 / 1439143)) (n := 12)
    (lo := (315179829 / 500000000)) (hi := (630359659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939143 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939143 / 500000) = 1/(500000 / 939143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (315179829 / 500000000) (630359659 / 1000000000) (Real.log (939143 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (939143 / 500000) = -Real.log (500000 / 939143) := by
    rw [show ((939143 / 500000) : ℝ) = ((500000 / 939143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1053040623 / 500000000) ≤ -Real.log (60857 / 500000) ∧
    -Real.log (60857 / 500000) ≤ (336973 / 160000) := by
  have h := checkLog_sound (w := (1643 / 123357)) (n := 12)
    (lo := (13319853 / 500000000)) (hi := (26639707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 60857) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 60857) = 1/(60857 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-336973 / 160000) (-1053040623 / 500000000) (Real.log (60857 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2784491537 / 1000000000) ≤ -Real.log (500000000000 / 8095791500481) ∧
    -Real.log (500000000000 / 8095791500481) ≤ (1392245771 / 500000000) := by
  have h := checkLog_sound (w := (95791500481 / 16095791500481)) (n := 12)
    (lo := (11902817 / 1000000000)) (hi := (5951409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8095791500481 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8095791500481 / 8000000000000) = 1/(500000000000 / 8095791500481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2784491537 / 1000000000) (1392245771 / 500000000) (Real.log (8095791500481 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8095791500481 / 500000000000) = -Real.log (500000000000 / 8095791500481) := by
    rw [show ((8095791500481 / 500000000000) : ℝ) = ((500000000000 / 8095791500481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (560126523 / 200000000) ≤ -Real.log (500000000000 / 8227526618957) ∧
    -Real.log (500000000000 / 8227526618957) ≤ (140031631 / 50000000) := by
  have h := checkLog_sound (w := (227526618957 / 16227526618957)) (n := 12)
    (lo := (5608779 / 200000000)) (hi := (3505487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8227526618957 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8227526618957 / 8000000000000) = 1/(500000000000 / 8227526618957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (560126523 / 200000000) (140031631 / 50000000) (Real.log (8227526618957 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8227526618957 / 500000000000) = -Real.log (500000000000 / 8227526618957) := by
    rw [show ((8227526618957 / 500000000000) : ℝ) = ((500000000000 / 8227526618957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1359202629 / 500000000) ≤ -Real.log (250000000000 / 3789033217009) ∧
    -Real.log (250000000000 / 3789033217009) ≤ (1359202631 / 500000000) := by
  have h := checkLog_sound (w := (1789033217009 / 5789033217009)) (n := 12)
    (lo := (319481859 / 500000000)) (hi := (638963719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3789033217009 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3789033217009 / 2000000000000) = 1/(250000000000 / 3789033217009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1359202629 / 500000000) (1359202631 / 500000000) (Real.log (3789033217009 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3789033217009 / 250000000000) = -Real.log (250000000000 / 3789033217009) := by
    rw [show ((3789033217009 / 250000000000) : ℝ) = ((250000000000 / 3789033217009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (547288181 / 200000000) ≤ -Real.log (500000000000 / 7715981727657) ∧
    -Real.log (500000000000 / 7715981727657) ≤ (2736440909 / 1000000000) := by
  have h := checkLog_sound (w := (3715981727657 / 11715981727657)) (n := 12)
    (lo := (131399873 / 200000000)) (hi := (328499683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7715981727657 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7715981727657 / 4000000000000) = 1/(500000000000 / 7715981727657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (547288181 / 200000000) (2736440909 / 1000000000) (Real.log (7715981727657 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7715981727657 / 500000000000) = -Real.log (500000000000 / 7715981727657) := by
    rw [show ((7715981727657 / 500000000000) : ℝ) = ((500000000000 / 7715981727657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0190

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0191Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0191
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

theorem reflection_log_1_neg : (9506343 / 15625000) ≤ -Real.log (80 / 147) ∧
    -Real.log (80 / 147) ≤ (608405953 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 227)) (n := 12)
    (lo := (9506343 / 15625000)) (hi := (608405953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147 / 80) = 1/(80 / 147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (9506343 / 15625000) (608405953 / 1000000000) (Real.log (147 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (147 / 80) = -Real.log (80 / 147) := by
    rw [show ((147 / 80) : ℝ) = ((80 / 147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (454269319 / 250000000) ≤ -Real.log (13 / 80) ∧
    -Real.log (13 / 80) ≤ (1817077279 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(20 / 13) = 1/(13 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1817077279 / 1000000000) (-454269319 / 250000000) (Real.log (13 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (606788999 / 1000000000) ≤ -Real.log (6400 / 11741) ∧
    -Real.log (6400 / 11741) ≤ (606789 / 1000000) := by
  have h := checkLog_sound (w := (5341 / 18141)) (n := 12)
    (lo := (606788999 / 1000000000)) (hi := (606789 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11741 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11741 / 6400) = 1/(6400 / 11741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (606788999 / 1000000000) (606789 / 1000000) (Real.log (11741 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11741 / 6400) = -Real.log (6400 / 11741) := by
    rw [show ((11741 / 6400) : ℝ) = ((6400 / 11741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (899486461 / 500000000) ≤ -Real.log (1059 / 6400) ∧
    -Real.log (1059 / 6400) ≤ (71958917 / 40000000) := by
  have h := checkLog_sound (w := (541 / 2659)) (n := 12)
    (lo := (206339281 / 500000000)) (hi := (412678563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1059) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1059) = 1/(1059 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-71958917 / 40000000) (-899486461 / 500000000) (Real.log (1059 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (103162633 / 200000000) ≤ -Real.log (40 / 67) ∧
    -Real.log (40 / 67) ≤ (257906583 / 500000000) := by
  have h := checkLog_sound (w := (27 / 107)) (n := 12)
    (lo := (103162633 / 200000000)) (hi := (257906583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67 / 40) = 1/(40 / 67) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (103162633 / 200000000) (257906583 / 500000000) (Real.log (67 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (67 / 40) = -Real.log (40 / 67) := by
    rw [show ((67 / 40) : ℝ) = ((40 / 67) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70245631 / 62500000) ≤ -Real.log (13 / 40) ∧
    -Real.log (13 / 40) ≤ (561965049 / 500000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 13) = 1/(13 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-561965049 / 500000000) (-70245631 / 62500000) (Real.log (13 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (512262091 / 1000000000) ≤ -Real.log (3200 / 5341) ∧
    -Real.log (3200 / 5341) ≤ (128065523 / 250000000) := by
  have h := checkLog_sound (w := (2141 / 8541)) (n := 12)
    (lo := (512262091 / 1000000000)) (hi := (128065523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5341 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5341 / 3200) = 1/(3200 / 5341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (512262091 / 1000000000) (128065523 / 250000000) (Real.log (5341 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5341 / 3200) = -Real.log (3200 / 5341) := by
    rw [show ((5341 / 3200) : ℝ) = ((3200 / 5341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (552912871 / 500000000) ≤ -Real.log (1059 / 3200) ∧
    -Real.log (1059 / 3200) ≤ (69114109 / 62500000) := by
  have h := checkLog_sound (w := (541 / 2659)) (n := 12)
    (lo := (206339281 / 500000000)) (hi := (412678563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1059) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1059) = 1/(1059 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-69114109 / 62500000) (-552912871 / 500000000) (Real.log (1059 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (126458719 / 200000000) ≤ -Real.log (500000 / 940961) ∧
    -Real.log (500000 / 940961) ≤ (158073399 / 250000000) := by
  have h := checkLog_sound (w := (440961 / 1440961)) (n := 12)
    (lo := (126458719 / 200000000)) (hi := (158073399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940961 / 500000) = 1/(500000 / 940961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (126458719 / 200000000) (158073399 / 250000000) (Real.log (940961 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (940961 / 500000) = -Real.log (500000 / 940961) := by
    rw [show ((940961 / 500000) : ℝ) = ((500000 / 940961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1068204927 / 500000000) ≤ -Real.log (59039 / 500000) ∧
    -Real.log (59039 / 500000) ≤ (1068204929 / 500000000) := by
  have h := checkLog_sound (w := (3461 / 121539)) (n := 12)
    (lo := (28484157 / 500000000)) (hi := (11393663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59039) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 59039) = 1/(59039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1068204929 / 500000000) (-1068204927 / 500000000) (Real.log (59039 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (633219347 / 1000000000) ≤ -Real.log (200000 / 376733) ∧
    -Real.log (200000 / 376733) ≤ (158304837 / 250000000) := by
  have h := checkLog_sound (w := (176733 / 576733)) (n := 12)
    (lo := (633219347 / 1000000000)) (hi := (158304837 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376733 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376733 / 200000) = 1/(200000 / 376733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (633219347 / 1000000000) (158304837 / 250000000) (Real.log (376733 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (376733 / 200000) = -Real.log (200000 / 376733) := by
    rw [show ((376733 / 200000) : ℝ) = ((200000 / 376733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2151281317 / 1000000000) ≤ -Real.log (23267 / 200000) ∧
    -Real.log (23267 / 200000) ≤ (2151281321 / 1000000000) := by
  have h := checkLog_sound (w := (1733 / 48267)) (n := 12)
    (lo := (71839777 / 1000000000)) (hi := (35919889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23267) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 23267) = 1/(23267 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2151281321 / 1000000000) (-2151281317 / 1000000000) (Real.log (23267 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (628147753 / 1000000000) ≤ -Real.log (125000 / 234267) ∧
    -Real.log (125000 / 234267) ≤ (314073877 / 500000000) := by
  have h := checkLog_sound (w := (109267 / 359267)) (n := 12)
    (lo := (628147753 / 1000000000)) (hi := (314073877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234267 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234267 / 125000) = 1/(125000 / 234267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (628147753 / 1000000000) (314073877 / 500000000) (Real.log (234267 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (234267 / 125000) = -Real.log (125000 / 234267) := by
    rw [show ((234267 / 125000) : ℝ) = ((125000 / 234267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1036276659 / 500000000) ≤ -Real.log (15733 / 125000) ∧
    -Real.log (15733 / 125000) ≤ (2072553321 / 1000000000) := by
  have h := checkLog_sound (w := (15517 / 46983)) (n := 12)
    (lo := (343129479 / 500000000)) (hi := (686258959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 15733) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 15733) = 1/(15733 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2072553321 / 1000000000) (-1036276659 / 500000000) (Real.log (15733 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (629253251 / 1000000000) ≤ -Real.log (1000000 / 1876209) ∧
    -Real.log (1000000 / 1876209) ≤ (157313313 / 250000000) := by
  have h := checkLog_sound (w := (876209 / 2876209)) (n := 12)
    (lo := (629253251 / 1000000000)) (hi := (157313313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1876209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1876209 / 1000000) = 1/(1000000 / 1876209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (629253251 / 1000000000) (157313313 / 250000000) (Real.log (1876209 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1876209 / 1000000) = -Real.log (1000000 / 1876209) := by
    rw [show ((1876209 / 1000000) : ℝ) = ((1000000 / 1876209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2089160617 / 1000000000) ≤ -Real.log (123791 / 1000000) ∧
    -Real.log (123791 / 1000000) ≤ (2089160621 / 1000000000) := by
  have h := checkLog_sound (w := (1209 / 248791)) (n := 12)
    (lo := (9719077 / 1000000000)) (hi := (4859539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 123791) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 123791) = 1/(123791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2089160621 / 1000000000) (-2089160617 / 1000000000) (Real.log (123791 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2768703449 / 1000000000) ≤ -Real.log (250000000000 / 3984489066549) ∧
    -Real.log (250000000000 / 3984489066549) ≤ (2768703453 / 1000000000) := by
  have h := checkLog_sound (w := (1984489066549 / 5984489066549)) (n := 12)
    (lo := (689261909 / 1000000000)) (hi := (68926191 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3984489066549 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3984489066549 / 2000000000000) = 1/(250000000000 / 3984489066549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2768703449 / 1000000000) (2768703453 / 1000000000) (Real.log (3984489066549 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3984489066549 / 250000000000) = -Real.log (250000000000 / 3984489066549) := by
    rw [show ((3984489066549 / 250000000000) : ℝ) = ((250000000000 / 3984489066549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2784500663 / 1000000000) ≤ -Real.log (500000000000 / 8095865388749) ∧
    -Real.log (500000000000 / 8095865388749) ≤ (696125167 / 250000000) := by
  have h := checkLog_sound (w := (95865388749 / 16095865388749)) (n := 12)
    (lo := (11911943 / 1000000000)) (hi := (1488993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8095865388749 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8095865388749 / 8000000000000) = 1/(500000000000 / 8095865388749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2784500663 / 1000000000) (696125167 / 250000000) (Real.log (8095865388749 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8095865388749 / 500000000000) = -Real.log (500000000000 / 8095865388749) := by
    rw [show ((8095865388749 / 500000000000) : ℝ) = ((500000000000 / 8095865388749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2700701071 / 1000000000) ≤ -Real.log (500000000000 / 7445083582279) ∧
    -Real.log (500000000000 / 7445083582279) ≤ (108028043 / 40000000) := by
  have h := checkLog_sound (w := (3445083582279 / 11445083582279)) (n := 12)
    (lo := (621259531 / 1000000000)) (hi := (155314883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7445083582279 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7445083582279 / 4000000000000) = 1/(500000000000 / 7445083582279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2700701071 / 1000000000) (108028043 / 40000000) (Real.log (7445083582279 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7445083582279 / 500000000000) = -Real.log (500000000000 / 7445083582279) := by
    rw [show ((7445083582279 / 500000000000) : ℝ) = ((500000000000 / 7445083582279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2718413869 / 1000000000) ≤ -Real.log (500000000000 / 7578131689703) ∧
    -Real.log (500000000000 / 7578131689703) ≤ (2718413873 / 1000000000) := by
  have h := checkLog_sound (w := (3578131689703 / 11578131689703)) (n := 12)
    (lo := (638972329 / 1000000000)) (hi := (63897233 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7578131689703 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7578131689703 / 4000000000000) = 1/(500000000000 / 7578131689703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2718413869 / 1000000000) (2718413873 / 1000000000) (Real.log (7578131689703 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7578131689703 / 500000000000) = -Real.log (500000000000 / 7578131689703) := by
    rw [show ((7578131689703 / 500000000000) : ℝ) = ((500000000000 / 7578131689703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0191

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0192Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0192
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

theorem reflection_log_1_neg : (606788999 / 1000000000) ≤ -Real.log (6400 / 11741) ∧
    -Real.log (6400 / 11741) ≤ (606789 / 1000000) := by
  have h := checkLog_sound (w := (5341 / 18141)) (n := 12)
    (lo := (606788999 / 1000000000)) (hi := (606789 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11741 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11741 / 6400) = 1/(6400 / 11741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (606788999 / 1000000000) (606789 / 1000000) (Real.log (11741 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11741 / 6400) = -Real.log (6400 / 11741) := by
    rw [show ((11741 / 6400) : ℝ) = ((6400 / 11741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (899486461 / 500000000) ≤ -Real.log (1059 / 6400) ∧
    -Real.log (1059 / 6400) ≤ (71958917 / 40000000) := by
  have h := checkLog_sound (w := (541 / 2659)) (n := 12)
    (lo := (206339281 / 500000000)) (hi := (412678563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1059) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1059) = 1/(1059 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-71958917 / 40000000) (-899486461 / 500000000) (Real.log (1059 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (605169427 / 1000000000) ≤ -Real.log (3200 / 5861) ∧
    -Real.log (3200 / 5861) ≤ (151292357 / 250000000) := by
  have h := checkLog_sound (w := (2661 / 9061)) (n := 12)
    (lo := (605169427 / 1000000000)) (hi := (151292357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5861 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5861 / 3200) = 1/(3200 / 5861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (605169427 / 1000000000) (151292357 / 250000000) (Real.log (5861 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5861 / 3200) = -Real.log (3200 / 5861) := by
    rw [show ((5861 / 3200) : ℝ) = ((3200 / 5861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (445297629 / 250000000) ≤ -Real.log (539 / 3200) ∧
    -Real.log (539 / 3200) ≤ (1781190519 / 1000000000) := by
  have h := checkLog_sound (w := (261 / 1339)) (n := 12)
    (lo := (98724039 / 250000000)) (hi := (394896157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 539) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 539) = 1/(539 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1781190519 / 1000000000) (-445297629 / 250000000) (Real.log (539 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (512262091 / 1000000000) ≤ -Real.log (3200 / 5341) ∧
    -Real.log (3200 / 5341) ≤ (128065523 / 250000000) := by
  have h := checkLog_sound (w := (2141 / 8541)) (n := 12)
    (lo := (512262091 / 1000000000)) (hi := (128065523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5341 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5341 / 3200) = 1/(3200 / 5341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (512262091 / 1000000000) (128065523 / 250000000) (Real.log (5341 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5341 / 3200) = -Real.log (3200 / 5341) := by
    rw [show ((5341 / 3200) : ℝ) = ((3200 / 5341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (552912871 / 500000000) ≤ -Real.log (1059 / 3200) ∧
    -Real.log (1059 / 3200) ≤ (69114109 / 62500000) := by
  have h := checkLog_sound (w := (541 / 2659)) (n := 12)
    (lo := (206339281 / 500000000)) (hi := (412678563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1059) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1059) = 1/(1059 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-69114109 / 62500000) (-552912871 / 500000000) (Real.log (1059 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (254349181 / 500000000) ≤ -Real.log (1600 / 2661) ∧
    -Real.log (1600 / 2661) ≤ (508698363 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 4261)) (n := 12)
    (lo := (254349181 / 500000000)) (hi := (508698363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2661 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2661 / 1600) = 1/(1600 / 2661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (254349181 / 500000000) (508698363 / 1000000000) (Real.log (2661 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2661 / 1600) = -Real.log (1600 / 2661) := by
    rw [show ((2661 / 1600) : ℝ) = ((1600 / 2661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (136005417 / 125000000) ≤ -Real.log (539 / 1600) ∧
    -Real.log (539 / 1600) ≤ (544021669 / 500000000) := by
  have h := checkLog_sound (w := (261 / 1339)) (n := 12)
    (lo := (98724039 / 250000000)) (hi := (394896157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 539) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 539) = 1/(539 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-544021669 / 500000000) (-136005417 / 125000000) (Real.log (539 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (631374963 / 1000000000) ≤ -Real.log (500000 / 940097) ∧
    -Real.log (500000 / 940097) ≤ (157843741 / 250000000) := by
  have h := checkLog_sound (w := (440097 / 1440097)) (n := 12)
    (lo := (631374963 / 1000000000)) (hi := (157843741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940097 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940097 / 500000) = 1/(500000 / 940097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (631374963 / 1000000000) (157843741 / 250000000) (Real.log (940097 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (940097 / 500000) = -Real.log (500000 / 940097) := by
    rw [show ((940097 / 500000) : ℝ) = ((500000 / 940097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2121881509 / 1000000000) ≤ -Real.log (59903 / 500000) ∧
    -Real.log (59903 / 500000) ≤ (2121881513 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 122403)) (n := 12)
    (lo := (42439969 / 1000000000)) (hi := (4243997 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59903) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 59903) = 1/(59903 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2121881513 / 1000000000) (-2121881509 / 1000000000) (Real.log (59903 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (316147063 / 500000000) ≤ -Real.log (1000000 / 1881923) ∧
    -Real.log (1000000 / 1881923) ≤ (632294127 / 1000000000) := by
  have h := checkLog_sound (w := (881923 / 2881923)) (n := 12)
    (lo := (316147063 / 500000000)) (hi := (632294127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1881923 / 1000000) = 1/(1000000 / 1881923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (316147063 / 500000000) (632294127 / 1000000000) (Real.log (1881923 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1881923 / 1000000) = -Real.log (1000000 / 1881923) := by
    rw [show ((1881923 / 1000000) : ℝ) = ((1000000 / 1881923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2136418323 / 1000000000) ≤ -Real.log (118077 / 1000000) ∧
    -Real.log (118077 / 1000000) ≤ (2136418327 / 1000000000) := by
  have h := checkLog_sound (w := (6923 / 243077)) (n := 12)
    (lo := (56976783 / 1000000000)) (hi := (3561049 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 118077) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 118077) = 1/(118077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2136418327 / 1000000000) (-2136418323 / 1000000000) (Real.log (118077 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (313521851 / 500000000) ≤ -Real.log (250000 / 468017) ∧
    -Real.log (250000 / 468017) ≤ (627043703 / 1000000000) := by
  have h := checkLog_sound (w := (218017 / 718017)) (n := 12)
    (lo := (313521851 / 500000000)) (hi := (627043703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468017 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468017 / 250000) = 1/(250000 / 468017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (313521851 / 500000000) (627043703 / 1000000000) (Real.log (468017 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (468017 / 250000) = -Real.log (250000 / 468017) := by
    rw [show ((468017 / 250000) : ℝ) = ((250000 / 468017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (411251281 / 200000000) ≤ -Real.log (31983 / 250000) ∧
    -Real.log (31983 / 250000) ≤ (257032051 / 125000000) := by
  have h := checkLog_sound (w := (30517 / 94483)) (n := 12)
    (lo := (133992409 / 200000000)) (hi := (334981023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31983) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 31983) = 1/(31983 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-257032051 / 125000000) (-411251281 / 200000000) (Real.log (31983 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (314074143 / 500000000) ≤ -Real.log (1000000 / 1874137) ∧
    -Real.log (1000000 / 1874137) ≤ (628148287 / 1000000000) := by
  have h := checkLog_sound (w := (874137 / 2874137)) (n := 12)
    (lo := (314074143 / 500000000)) (hi := (628148287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1874137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1874137 / 1000000) = 1/(1000000 / 1874137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (314074143 / 500000000) (628148287 / 1000000000) (Real.log (1874137 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1874137 / 1000000) = -Real.log (1000000 / 1874137) := by
    rw [show ((1874137 / 1000000) : ℝ) = ((1000000 / 1874137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (129535079 / 62500000) ≤ -Real.log (125863 / 1000000) ∧
    -Real.log (125863 / 1000000) ≤ (2072561267 / 1000000000) := by
  have h := checkLog_sound (w := (124137 / 375863)) (n := 12)
    (lo := (85783363 / 125000000)) (hi := (137253381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 125863) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 125863) = 1/(125863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2072561267 / 1000000000) (-129535079 / 62500000) (Real.log (125863 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (344157059 / 125000000) ≤ -Real.log (125000000000 / 1961706842729) ∧
    -Real.log (125000000000 / 1961706842729) ≤ (688314119 / 250000000) := by
  have h := checkLog_sound (w := (961706842729 / 2961706842729)) (n := 12)
    (lo := (168453733 / 250000000)) (hi := (673814933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961706842729 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1961706842729 / 1000000000000) = 1/(125000000000 / 1961706842729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (344157059 / 125000000) (688314119 / 250000000) (Real.log (1961706842729 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1961706842729 / 125000000000) = -Real.log (125000000000 / 1961706842729) := by
    rw [show ((1961706842729 / 125000000000) : ℝ) = ((125000000000 / 1961706842729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2768712449 / 1000000000) ≤ -Real.log (500000000000 / 7969049857297) ∧
    -Real.log (500000000000 / 7969049857297) ≤ (2768712453 / 1000000000) := by
  have h := checkLog_sound (w := (3969049857297 / 11969049857297)) (n := 12)
    (lo := (689270909 / 1000000000)) (hi := (68927091 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7969049857297 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7969049857297 / 4000000000000) = 1/(500000000000 / 7969049857297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2768712449 / 1000000000) (2768712453 / 1000000000) (Real.log (7969049857297 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7969049857297 / 500000000000) = -Real.log (500000000000 / 7969049857297) := by
    rw [show ((7969049857297 / 500000000000) : ℝ) = ((500000000000 / 7969049857297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1341650053 / 500000000) ≤ -Real.log (500000000000 / 7316652596691) ∧
    -Real.log (500000000000 / 7316652596691) ≤ (268330011 / 100000000) := by
  have h := checkLog_sound (w := (3316652596691 / 11316652596691)) (n := 12)
    (lo := (301929283 / 500000000)) (hi := (603858567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7316652596691 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7316652596691 / 4000000000000) = 1/(500000000000 / 7316652596691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1341650053 / 500000000) (268330011 / 100000000) (Real.log (7316652596691 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7316652596691 / 500000000000) = -Real.log (500000000000 / 7316652596691) := by
    rw [show ((7316652596691 / 500000000000) : ℝ) = ((500000000000 / 7316652596691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (54014191 / 20000000) ≤ -Real.log (250000000000 / 3722573353567) ∧
    -Real.log (250000000000 / 3722573353567) ≤ (1350354777 / 500000000) := by
  have h := checkLog_sound (w := (1722573353567 / 5722573353567)) (n := 12)
    (lo := (62126801 / 100000000)) (hi := (621268011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3722573353567 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3722573353567 / 2000000000000) = 1/(250000000000 / 3722573353567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (54014191 / 20000000) (1350354777 / 500000000) (Real.log (3722573353567 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3722573353567 / 250000000000) = -Real.log (250000000000 / 3722573353567) := by
    rw [show ((3722573353567 / 250000000000) : ℝ) = ((250000000000 / 3722573353567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0192

end


