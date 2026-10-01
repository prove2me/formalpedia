-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0199Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0199Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:54:13.148389+00:00
-- url     : https://prove2.me/theorems/e1be41df-8a01-491e-b2d0-12c76de29b18
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0199Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0200Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0199Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0200Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0201Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0202Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0203Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0204Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0205Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0199Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0200Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0201Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0202Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0203Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0204Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0205Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0199Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0200Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0201Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0202Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0203Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0204Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0205Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0199Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0200Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0201Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0202Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0203Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0204Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0205Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0199Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0199
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

theorem reflection_log_1_neg : (23815861 / 40000000) ≤ -Real.log (800 / 1451) ∧
    -Real.log (800 / 1451) ≤ (297698263 / 500000000) := by
  have h := checkLog_sound (w := (651 / 2251)) (n := 12)
    (lo := (23815861 / 40000000)) (hi := (297698263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 800) = 1/(800 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (23815861 / 40000000) (297698263 / 500000000) (Real.log (1451 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1451 / 800) = -Real.log (800 / 1451) := by
    rw [show ((1451 / 800) : ℝ) = ((800 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (84033271 / 50000000) ≤ -Real.log (149 / 800) ∧
    -Real.log (149 / 800) ≤ (1680665423 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 349)) (n := 12)
    (lo := (14718553 / 50000000)) (hi := (294371061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 149) = 1/(149 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1680665423 / 1000000000) (-84033271 / 50000000) (Real.log (149 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11842351 / 20000000) ≤ -Real.log (640 / 1157) ∧
    -Real.log (640 / 1157) ≤ (592117551 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 1797)) (n := 12)
    (lo := (11842351 / 20000000)) (hi := (592117551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 640) = 1/(640 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11842351 / 20000000) (592117551 / 1000000000) (Real.log (1157 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1157 / 640) = -Real.log (640 / 1157) := by
    rw [show ((1157 / 640) : ℝ) = ((640 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1649283819 / 1000000000) ≤ -Real.log (123 / 640) ∧
    -Real.log (123 / 640) ≤ (824641911 / 500000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 123) = 1/(123 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-824641911 / 500000000) (-1649283819 / 1000000000) (Real.log (123 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97409019 / 200000000) ≤ -Real.log (400 / 651) ∧
    -Real.log (400 / 651) ≤ (60880637 / 125000000) := by
  have h := checkLog_sound (w := (251 / 1051)) (n := 12)
    (lo := (97409019 / 200000000)) (hi := (60880637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 400) = 1/(400 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (97409019 / 200000000) (60880637 / 125000000) (Real.log (651 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (651 / 400) = -Real.log (400 / 651) := by
    rw [show ((651 / 400) : ℝ) = ((400 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6171989 / 6250000) ≤ -Real.log (149 / 400) ∧
    -Real.log (149 / 400) ≤ (493759121 / 500000000) := by
  have h := checkLog_sound (w := (51 / 349)) (n := 12)
    (lo := (14718553 / 50000000)) (hi := (294371061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 149) = 1/(149 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-493759121 / 500000000) (-6171989 / 6250000) (Real.log (149 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (239860939 / 500000000) ≤ -Real.log (320 / 517) ∧
    -Real.log (320 / 517) ≤ (479721879 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 837)) (n := 12)
    (lo := (239860939 / 500000000)) (hi := (479721879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 320) = 1/(320 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (239860939 / 500000000) (479721879 / 1000000000) (Real.log (517 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (517 / 320) = -Real.log (320 / 517) := by
    rw [show ((517 / 320) : ℝ) = ((320 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (956136639 / 1000000000) ≤ -Real.log (123 / 320) ∧
    -Real.log (123 / 320) ≤ (956136641 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 123) = 1/(123 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-956136641 / 1000000000) (-956136639 / 1000000000) (Real.log (123 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (624251447 / 1000000000) ≤ -Real.log (31250 / 58339) ∧
    -Real.log (31250 / 58339) ≤ (78031431 / 125000000) := by
  have h := checkLog_sound (w := (27089 / 89589)) (n := 12)
    (lo := (624251447 / 1000000000)) (hi := (78031431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58339 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58339 / 31250) = 1/(31250 / 58339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (624251447 / 1000000000) (78031431 / 125000000) (Real.log (58339 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (58339 / 31250) = -Real.log (31250 / 58339) := by
    rw [show ((58339 / 31250) : ℝ) = ((31250 / 58339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (403252789 / 200000000) ≤ -Real.log (4161 / 31250) ∧
    -Real.log (4161 / 31250) ≤ (504065987 / 250000000) := by
  have h := checkLog_sound (w := (7303 / 23947)) (n := 12)
    (lo := (125993917 / 200000000)) (hi := (314984793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8322) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 8322) = 1/(4161 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-504065987 / 250000000) (-403252789 / 200000000) (Real.log (4161 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (625994579 / 1000000000) ≤ -Real.log (200000 / 374021) ∧
    -Real.log (200000 / 374021) ≤ (31299729 / 50000000) := by
  have h := checkLog_sound (w := (174021 / 574021)) (n := 12)
    (lo := (625994579 / 1000000000)) (hi := (31299729 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374021 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374021 / 200000) = 1/(200000 / 374021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (625994579 / 1000000000) (31299729 / 50000000) (Real.log (374021 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (374021 / 200000) = -Real.log (200000 / 374021) := by
    rw [show ((374021 / 200000) : ℝ) = ((200000 / 374021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1020514423 / 500000000) ≤ -Real.log (25979 / 200000) ∧
    -Real.log (25979 / 200000) ≤ (2041028849 / 1000000000) := by
  have h := checkLog_sound (w := (24021 / 75979)) (n := 12)
    (lo := (327367243 / 500000000)) (hi := (654734487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 25979) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 25979) = 1/(25979 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2041028849 / 1000000000) (-1020514423 / 500000000) (Real.log (25979 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (19320367 / 31250000) ≤ -Real.log (1000000 / 1855681) ∧
    -Real.log (1000000 / 1855681) ≤ (123650349 / 200000000) := by
  have h := checkLog_sound (w := (855681 / 2855681)) (n := 12)
    (lo := (19320367 / 31250000)) (hi := (123650349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1855681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1855681 / 1000000) = 1/(1000000 / 1855681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (19320367 / 31250000) (123650349 / 200000000) (Real.log (1855681 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1855681 / 1000000) = -Real.log (1000000 / 1855681) := by
    rw [show ((1855681 / 1000000) : ℝ) = ((1000000 / 1855681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (38714583 / 20000000) ≤ -Real.log (144319 / 1000000) ∧
    -Real.log (144319 / 1000000) ≤ (1935729153 / 1000000000) := by
  have h := checkLog_sound (w := (105681 / 394319)) (n := 12)
    (lo := (54943479 / 100000000)) (hi := (549434791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 144319) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 144319) = 1/(144319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1935729153 / 1000000000) (-38714583 / 20000000) (Real.log (144319 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (31022211 / 50000000) ≤ -Real.log (500000 / 929877) ∧
    -Real.log (500000 / 929877) ≤ (620444221 / 1000000000) := by
  have h := checkLog_sound (w := (429877 / 1429877)) (n := 12)
    (lo := (31022211 / 50000000)) (hi := (620444221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929877 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929877 / 500000) = 1/(500000 / 929877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (31022211 / 50000000) (620444221 / 1000000000) (Real.log (929877 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (929877 / 500000) = -Real.log (500000 / 929877) := by
    rw [show ((929877 / 500000) : ℝ) = ((500000 / 929877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (982178627 / 500000000) ≤ -Real.log (70123 / 500000) ∧
    -Real.log (70123 / 500000) ≤ (1964357257 / 1000000000) := by
  have h := checkLog_sound (w := (54877 / 195123)) (n := 12)
    (lo := (289031447 / 500000000)) (hi := (115612579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 70123) = 1/(70123 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1964357257 / 1000000000) (-982178627 / 500000000) (Real.log (70123 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2640515391 / 1000000000) ≤ -Real.log (500000000000 / 7010213890891) ∧
    -Real.log (500000000000 / 7010213890891) ≤ (528103079 / 200000000) := by
  have h := checkLog_sound (w := (3010213890891 / 11010213890891)) (n := 12)
    (lo := (561073851 / 1000000000)) (hi := (140268463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7010213890891 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7010213890891 / 4000000000000) = 1/(500000000000 / 7010213890891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2640515391 / 1000000000) (528103079 / 200000000) (Real.log (7010213890891 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7010213890891 / 500000000000) = -Real.log (500000000000 / 7010213890891) := by
    rw [show ((7010213890891 / 500000000000) : ℝ) = ((500000000000 / 7010213890891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (41672241 / 15625000) ≤ -Real.log (500000000000 / 7198525732323) ∧
    -Real.log (500000000000 / 7198525732323) ≤ (666755857 / 250000000) := by
  have h := checkLog_sound (w := (3198525732323 / 11198525732323)) (n := 12)
    (lo := (146895471 / 250000000)) (hi := (117516377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7198525732323 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7198525732323 / 4000000000000) = 1/(500000000000 / 7198525732323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (41672241 / 15625000) (666755857 / 250000000) (Real.log (7198525732323 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7198525732323 / 500000000000) = -Real.log (500000000000 / 7198525732323) := by
    rw [show ((7198525732323 / 500000000000) : ℝ) = ((500000000000 / 7198525732323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1276990447 / 500000000) ≤ -Real.log (500000000000 / 6429094575211) ∧
    -Real.log (500000000000 / 6429094575211) ≤ (1276990449 / 500000000) := by
  have h := checkLog_sound (w := (2429094575211 / 10429094575211)) (n := 12)
    (lo := (237269677 / 500000000)) (hi := (94907871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6429094575211 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6429094575211 / 4000000000000) = 1/(500000000000 / 6429094575211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1276990447 / 500000000) (1276990449 / 500000000) (Real.log (6429094575211 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6429094575211 / 500000000000) = -Real.log (500000000000 / 6429094575211) := by
    rw [show ((6429094575211 / 500000000000) : ℝ) = ((500000000000 / 6429094575211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1292400737 / 500000000) ≤ -Real.log (500000000000 / 6630328137701) ∧
    -Real.log (500000000000 / 6630328137701) ≤ (1292400739 / 500000000) := by
  have h := checkLog_sound (w := (2630328137701 / 10630328137701)) (n := 12)
    (lo := (252679967 / 500000000)) (hi := (101071987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6630328137701 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6630328137701 / 4000000000000) = 1/(500000000000 / 6630328137701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1292400737 / 500000000) (1292400739 / 500000000) (Real.log (6630328137701 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6630328137701 / 500000000000) = -Real.log (500000000000 / 6630328137701) := by
    rw [show ((6630328137701 / 500000000000) : ℝ) = ((500000000000 / 6630328137701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0199

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0200Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0200
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

theorem reflection_log_1_neg : (11842351 / 20000000) ≤ -Real.log (640 / 1157) ∧
    -Real.log (640 / 1157) ≤ (592117551 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 1797)) (n := 12)
    (lo := (11842351 / 20000000)) (hi := (592117551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 640) = 1/(640 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11842351 / 20000000) (592117551 / 1000000000) (Real.log (1157 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1157 / 640) = -Real.log (640 / 1157) := by
    rw [show ((1157 / 640) : ℝ) = ((640 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1649283819 / 1000000000) ≤ -Real.log (123 / 640) ∧
    -Real.log (123 / 640) ≤ (824641911 / 500000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 123) = 1/(123 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-824641911 / 500000000) (-1649283819 / 1000000000) (Real.log (123 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (588827789 / 1000000000) ≤ -Real.log (1600 / 2883) ∧
    -Real.log (1600 / 2883) ≤ (58882779 / 100000000) := by
  have h := checkLog_sound (w := (1283 / 4483)) (n := 12)
    (lo := (588827789 / 1000000000)) (hi := (58882779 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2883 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2883 / 1600) = 1/(1600 / 2883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (588827789 / 1000000000) (58882779 / 100000000) (Real.log (2883 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2883 / 1600) = -Real.log (1600 / 2883) := by
    rw [show ((2883 / 1600) : ℝ) = ((1600 / 2883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1618857133 / 1000000000) ≤ -Real.log (317 / 1600) ∧
    -Real.log (317 / 1600) ≤ (101178571 / 62500000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 317) = 1/(317 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-101178571 / 62500000) (-1618857133 / 1000000000) (Real.log (317 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (239860939 / 500000000) ≤ -Real.log (320 / 517) ∧
    -Real.log (320 / 517) ≤ (479721879 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 837)) (n := 12)
    (lo := (239860939 / 500000000)) (hi := (479721879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 320) = 1/(320 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (239860939 / 500000000) (479721879 / 1000000000) (Real.log (517 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (517 / 320) = -Real.log (320 / 517) := by
    rw [show ((517 / 320) : ℝ) = ((320 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (956136639 / 1000000000) ≤ -Real.log (123 / 320) ∧
    -Real.log (123 / 320) ≤ (956136641 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 123) = 1/(123 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-956136641 / 1000000000) (-956136639 / 1000000000) (Real.log (123 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (118086159 / 250000000) ≤ -Real.log (800 / 1283) ∧
    -Real.log (800 / 1283) ≤ (472344637 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 2083)) (n := 12)
    (lo := (118086159 / 250000000)) (hi := (472344637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283 / 800) = 1/(800 / 1283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (118086159 / 250000000) (472344637 / 1000000000) (Real.log (1283 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1283 / 800) = -Real.log (800 / 1283) := by
    rw [show ((1283 / 800) : ℝ) = ((800 / 1283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (925709953 / 1000000000) ≤ -Real.log (317 / 800) ∧
    -Real.log (317 / 800) ≤ (185141991 / 200000000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 317) = 1/(317 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-185141991 / 200000000) (-925709953 / 1000000000) (Real.log (317 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15563383 / 25000000) ≤ -Real.log (1000000 / 1863647) ∧
    -Real.log (1000000 / 1863647) ≤ (622535321 / 1000000000) := by
  have h := checkLog_sound (w := (863647 / 2863647)) (n := 12)
    (lo := (15563383 / 25000000)) (hi := (622535321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863647 / 1000000) = 1/(1000000 / 1863647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15563383 / 25000000) (622535321 / 1000000000) (Real.log (1863647 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1863647 / 1000000) = -Real.log (1000000 / 1863647) := by
    rw [show ((1863647 / 1000000) : ℝ) = ((1000000 / 1863647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (996254083 / 500000000) ≤ -Real.log (136353 / 1000000) ∧
    -Real.log (136353 / 1000000) ≤ (1992508169 / 1000000000) := by
  have h := checkLog_sound (w := (113647 / 386353)) (n := 12)
    (lo := (303106903 / 500000000)) (hi := (606213807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 136353) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 136353) = 1/(136353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1992508169 / 1000000000) (-996254083 / 500000000) (Real.log (136353 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (312125991 / 500000000) ≤ -Real.log (1000000 / 1866849) ∧
    -Real.log (1000000 / 1866849) ≤ (624251983 / 1000000000) := by
  have h := checkLog_sound (w := (866849 / 2866849)) (n := 12)
    (lo := (312125991 / 500000000)) (hi := (624251983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1866849 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1866849 / 1000000) = 1/(1000000 / 1866849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (312125991 / 500000000) (624251983 / 1000000000) (Real.log (1866849 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1866849 / 1000000) = -Real.log (1000000 / 1866849) := by
    rw [show ((1866849 / 1000000) : ℝ) = ((1000000 / 1866849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (403254291 / 200000000) ≤ -Real.log (133151 / 1000000) ∧
    -Real.log (133151 / 1000000) ≤ (1008135729 / 500000000) := by
  have h := checkLog_sound (w := (116849 / 383151)) (n := 12)
    (lo := (125995419 / 200000000)) (hi := (78747137 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 133151) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 133151) = 1/(133151 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1008135729 / 500000000) (-403254291 / 200000000) (Real.log (133151 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (616063631 / 1000000000) ≤ -Real.log (8000 / 14813) ∧
    -Real.log (8000 / 14813) ≤ (38503977 / 62500000) := by
  have h := checkLog_sound (w := (6813 / 22813)) (n := 12)
    (lo := (616063631 / 1000000000)) (hi := (38503977 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14813 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14813 / 8000) = 1/(8000 / 14813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (616063631 / 1000000000) (38503977 / 62500000) (Real.log (14813 / 8000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (14813 / 8000) = -Real.log (8000 / 14813) := by
    rw [show ((14813 / 8000) : ℝ) = ((8000 / 14813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (238501553 / 125000000) ≤ -Real.log (1187 / 8000) ∧
    -Real.log (1187 / 8000) ≤ (1908012427 / 1000000000) := by
  have h := checkLog_sound (w := (813 / 3187)) (n := 12)
    (lo := (32607379 / 62500000)) (hi := (104343613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2000 / 1187) = 1/(1187 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1908012427 / 1000000000) (-238501553 / 125000000) (Real.log (1187 / 8000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (618252283 / 1000000000) ≤ -Real.log (500000 / 927841) ∧
    -Real.log (500000 / 927841) ≤ (154563071 / 250000000) := by
  have h := checkLog_sound (w := (427841 / 1427841)) (n := 12)
    (lo := (618252283 / 1000000000)) (hi := (154563071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927841 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927841 / 500000) = 1/(500000 / 927841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (618252283 / 1000000000) (154563071 / 250000000) (Real.log (927841 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (927841 / 500000) = -Real.log (500000 / 927841) := by
    rw [show ((927841 / 500000) : ℝ) = ((500000 / 927841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1935736079 / 1000000000) ≤ -Real.log (72159 / 500000) ∧
    -Real.log (72159 / 500000) ≤ (967868041 / 500000000) := by
  have h := checkLog_sound (w := (52841 / 197159)) (n := 12)
    (lo := (549441719 / 1000000000)) (hi := (13736043 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72159) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 72159) = 1/(72159 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-967868041 / 500000000) (-1935736079 / 1000000000) (Real.log (72159 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1307521743 / 500000000) ≤ -Real.log (15625000000 / 213559543061) ∧
    -Real.log (15625000000 / 213559543061) ≤ (261504349 / 100000000) := by
  have h := checkLog_sound (w := (88559543061 / 338559543061)) (n := 12)
    (lo := (267800973 / 500000000)) (hi := (535601947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213559543061 / 125000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(213559543061 / 125000000000) = 1/(15625000000 / 213559543061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1307521743 / 500000000) (261504349 / 100000000) (Real.log (213559543061 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (213559543061 / 15625000000) = -Real.log (15625000000 / 213559543061) := by
    rw [show ((213559543061 / 15625000000) : ℝ) = ((15625000000 / 213559543061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2640523437 / 1000000000) ≤ -Real.log (125000000000 / 1752567573657) ∧
    -Real.log (125000000000 / 1752567573657) ≤ (2640523441 / 1000000000) := by
  have h := checkLog_sound (w := (752567573657 / 2752567573657)) (n := 12)
    (lo := (561081897 / 1000000000)) (hi := (280540949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1752567573657 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1752567573657 / 1000000000000) = 1/(125000000000 / 1752567573657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2640523437 / 1000000000) (2640523441 / 1000000000) (Real.log (1752567573657 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1752567573657 / 125000000000) = -Real.log (125000000000 / 1752567573657) := by
    rw [show ((1752567573657 / 125000000000) : ℝ) = ((125000000000 / 1752567573657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (315509507 / 125000000) ≤ -Real.log (250000000000 / 3119839932603) ∧
    -Real.log (250000000000 / 3119839932603) ≤ (126203803 / 50000000) := by
  have h := checkLog_sound (w := (1119839932603 / 5119839932603)) (n := 12)
    (lo := (111158629 / 250000000)) (hi := (444634517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3119839932603 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3119839932603 / 2000000000000) = 1/(250000000000 / 3119839932603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (315509507 / 125000000) (126203803 / 50000000) (Real.log (3119839932603 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3119839932603 / 250000000000) = -Real.log (250000000000 / 3119839932603) := by
    rw [show ((3119839932603 / 250000000000) : ℝ) = ((250000000000 / 3119839932603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1276994181 / 500000000) ≤ -Real.log (500000000000 / 6429142587897) ∧
    -Real.log (500000000000 / 6429142587897) ≤ (1276994183 / 500000000) := by
  have h := checkLog_sound (w := (2429142587897 / 10429142587897)) (n := 12)
    (lo := (237273411 / 500000000)) (hi := (474546823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6429142587897 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6429142587897 / 4000000000000) = 1/(500000000000 / 6429142587897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1276994181 / 500000000) (1276994183 / 500000000) (Real.log (6429142587897 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6429142587897 / 500000000000) = -Real.log (500000000000 / 6429142587897) := by
    rw [show ((6429142587897 / 500000000000) : ℝ) = ((500000000000 / 6429142587897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0200

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0201Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0201
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

theorem reflection_log_1_neg : (588827789 / 1000000000) ≤ -Real.log (1600 / 2883) ∧
    -Real.log (1600 / 2883) ≤ (58882779 / 100000000) := by
  have h := checkLog_sound (w := (1283 / 4483)) (n := 12)
    (lo := (588827789 / 1000000000)) (hi := (58882779 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2883 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2883 / 1600) = 1/(1600 / 2883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (588827789 / 1000000000) (58882779 / 100000000) (Real.log (2883 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2883 / 1600) = -Real.log (1600 / 2883) := by
    rw [show ((2883 / 1600) : ℝ) = ((1600 / 2883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1618857133 / 1000000000) ≤ -Real.log (317 / 1600) ∧
    -Real.log (317 / 1600) ≤ (101178571 / 62500000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 317) = 1/(317 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-101178571 / 62500000) (-1618857133 / 1000000000) (Real.log (317 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (585527169 / 1000000000) ≤ -Real.log (3200 / 5747) ∧
    -Real.log (3200 / 5747) ≤ (58552717 / 100000000) := by
  have h := checkLog_sound (w := (2547 / 8947)) (n := 12)
    (lo := (585527169 / 1000000000)) (hi := (58552717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5747 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5747 / 3200) = 1/(3200 / 5747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (585527169 / 1000000000) (58552717 / 100000000) (Real.log (5747 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5747 / 3200) = -Real.log (3200 / 5747) := by
    rw [show ((5747 / 3200) : ℝ) = ((3200 / 5747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (794664479 / 500000000) ≤ -Real.log (653 / 3200) ∧
    -Real.log (653 / 3200) ≤ (1589328961 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 1453)) (n := 12)
    (lo := (101517299 / 500000000)) (hi := (203034599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 653) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 653) = 1/(653 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1589328961 / 1000000000) (-794664479 / 500000000) (Real.log (653 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (118086159 / 250000000) ≤ -Real.log (800 / 1283) ∧
    -Real.log (800 / 1283) ≤ (472344637 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 2083)) (n := 12)
    (lo := (118086159 / 250000000)) (hi := (472344637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283 / 800) = 1/(800 / 1283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (118086159 / 250000000) (472344637 / 1000000000) (Real.log (1283 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1283 / 800) = -Real.log (800 / 1283) := by
    rw [show ((1283 / 800) : ℝ) = ((800 / 1283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (925709953 / 1000000000) ≤ -Real.log (317 / 800) ∧
    -Real.log (317 / 800) ≤ (185141991 / 200000000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 317) = 1/(317 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-185141991 / 200000000) (-925709953 / 1000000000) (Real.log (317 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (232456283 / 500000000) ≤ -Real.log (1600 / 2547) ∧
    -Real.log (1600 / 2547) ≤ (464912567 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 4147)) (n := 12)
    (lo := (232456283 / 500000000)) (hi := (464912567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 1600) = 1/(1600 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (232456283 / 500000000) (464912567 / 1000000000) (Real.log (2547 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2547 / 1600) = -Real.log (1600 / 2547) := by
    rw [show ((2547 / 1600) : ℝ) = ((1600 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (448090889 / 500000000) ≤ -Real.log (653 / 1600) ∧
    -Real.log (653 / 1600) ≤ (44809089 / 50000000) := by
  have h := checkLog_sound (w := (147 / 1453)) (n := 12)
    (lo := (101517299 / 500000000)) (hi := (203034599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 653) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 653) = 1/(653 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-44809089 / 50000000) (-448090889 / 500000000) (Real.log (653 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155211317 / 250000000) ≤ -Real.log (2000 / 3721) ∧
    -Real.log (2000 / 3721) ≤ (620845269 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 5721)) (n := 12)
    (lo := (155211317 / 250000000)) (hi := (620845269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3721 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3721 / 2000) = 1/(2000 / 3721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155211317 / 250000000) (620845269 / 1000000000) (Real.log (3721 / 2000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (3721 / 2000) = -Real.log (2000 / 3721) := by
    rw [show ((3721 / 2000) : ℝ) = ((2000 / 3721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (492422669 / 250000000) ≤ -Real.log (279 / 2000) ∧
    -Real.log (279 / 2000) ≤ (1969690679 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 779)) (n := 12)
    (lo := (145849079 / 250000000)) (hi := (583396317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 279) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(500 / 279) = 1/(279 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1969690679 / 1000000000) (-492422669 / 250000000) (Real.log (279 / 2000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (622535857 / 1000000000) ≤ -Real.log (31250 / 58239) ∧
    -Real.log (31250 / 58239) ≤ (311267929 / 500000000) := by
  have h := checkLog_sound (w := (26989 / 89489)) (n := 12)
    (lo := (622535857 / 1000000000)) (hi := (311267929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58239 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58239 / 31250) = 1/(31250 / 58239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (622535857 / 1000000000) (311267929 / 500000000) (Real.log (58239 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (58239 / 31250) = -Real.log (31250 / 58239) := by
    rw [show ((58239 / 31250) : ℝ) = ((31250 / 58239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3985031 / 2000000) ≤ -Real.log (4261 / 31250) ∧
    -Real.log (4261 / 31250) ≤ (1992515503 / 1000000000) := by
  have h := checkLog_sound (w := (7103 / 24147)) (n := 12)
    (lo := (30311057 / 50000000)) (hi := (606221141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8522) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 8522) = 1/(4261 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1992515503 / 1000000000) (-3985031 / 2000000) (Real.log (4261 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (613878839 / 1000000000) ≤ -Real.log (31250 / 57737) ∧
    -Real.log (31250 / 57737) ≤ (15346971 / 25000000) := by
  have h := checkLog_sound (w := (26487 / 88987)) (n := 12)
    (lo := (613878839 / 1000000000)) (hi := (15346971 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57737 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57737 / 31250) = 1/(31250 / 57737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (613878839 / 1000000000) (15346971 / 25000000) (Real.log (57737 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (57737 / 31250) = -Real.log (31250 / 57737) := by
    rw [show ((57737 / 31250) : ℝ) = ((31250 / 57737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1881141653 / 1000000000) ≤ -Real.log (4763 / 31250) ∧
    -Real.log (4763 / 31250) ≤ (235142707 / 125000000) := by
  have h := checkLog_sound (w := (6099 / 25151)) (n := 12)
    (lo := (494847293 / 1000000000)) (hi := (247423647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9526) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 9526) = 1/(4763 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-235142707 / 125000000) (-1881141653 / 1000000000) (Real.log (4763 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (616064171 / 1000000000) ≤ -Real.log (500000 / 925813) ∧
    -Real.log (500000 / 925813) ≤ (154016043 / 250000000) := by
  have h := checkLog_sound (w := (425813 / 1425813)) (n := 12)
    (lo := (616064171 / 1000000000)) (hi := (154016043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925813 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925813 / 500000) = 1/(500000 / 925813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (616064171 / 1000000000) (154016043 / 250000000) (Real.log (925813 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (925813 / 500000) = -Real.log (500000 / 925813) := by
    rw [show ((925813 / 500000) : ℝ) = ((500000 / 925813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (477004791 / 250000000) ≤ -Real.log (74187 / 500000) ∧
    -Real.log (74187 / 500000) ≤ (1908019167 / 1000000000) := by
  have h := checkLog_sound (w := (50813 / 199187)) (n := 12)
    (lo := (130431201 / 250000000)) (hi := (104344961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 74187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 74187) = 1/(74187 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1908019167 / 1000000000) (-477004791 / 250000000) (Real.log (74187 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (323816993 / 125000000) ≤ -Real.log (250000000000 / 3334229390681) ∧
    -Real.log (250000000000 / 3334229390681) ≤ (647633987 / 250000000) := by
  have h := checkLog_sound (w := (1334229390681 / 5334229390681)) (n := 12)
    (lo := (127773601 / 250000000)) (hi := (102218881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3334229390681 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3334229390681 / 2000000000000) = 1/(250000000000 / 3334229390681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (323816993 / 125000000) (647633987 / 250000000) (Real.log (3334229390681 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3334229390681 / 250000000000) = -Real.log (250000000000 / 3334229390681) := by
    rw [show ((3334229390681 / 250000000000) : ℝ) = ((250000000000 / 3334229390681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2615051357 / 1000000000) ≤ -Real.log (125000000000 / 1708489791129) ∧
    -Real.log (125000000000 / 1708489791129) ≤ (2615051361 / 1000000000) := by
  have h := checkLog_sound (w := (708489791129 / 2708489791129)) (n := 12)
    (lo := (535609817 / 1000000000)) (hi := (267804909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1708489791129 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1708489791129 / 1000000000000) = 1/(125000000000 / 1708489791129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2615051357 / 1000000000) (2615051361 / 1000000000) (Real.log (1708489791129 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1708489791129 / 125000000000) = -Real.log (125000000000 / 1708489791129) := by
    rw [show ((1708489791129 / 125000000000) : ℝ) = ((125000000000 / 1708489791129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (623755123 / 250000000) ≤ -Real.log (125000000000 / 1515247743019) ∧
    -Real.log (125000000000 / 1515247743019) ≤ (155938781 / 62500000) := by
  have h := checkLog_sound (w := (515247743019 / 2515247743019)) (n := 12)
    (lo := (51947369 / 125000000)) (hi := (415578953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1515247743019 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1515247743019 / 1000000000000) = 1/(125000000000 / 1515247743019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (623755123 / 250000000) (155938781 / 62500000) (Real.log (1515247743019 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1515247743019 / 125000000000) = -Real.log (125000000000 / 1515247743019) := by
    rw [show ((1515247743019 / 125000000000) : ℝ) = ((125000000000 / 1515247743019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (315510417 / 125000000) ≤ -Real.log (250000000000 / 3119862644399) ∧
    -Real.log (250000000000 / 3119862644399) ≤ (126204167 / 50000000) := by
  have h := checkLog_sound (w := (1119862644399 / 5119862644399)) (n := 12)
    (lo := (111160449 / 250000000)) (hi := (444641797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3119862644399 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3119862644399 / 2000000000000) = 1/(250000000000 / 3119862644399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (315510417 / 125000000) (126204167 / 50000000) (Real.log (3119862644399 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3119862644399 / 250000000000) = -Real.log (250000000000 / 3119862644399) := by
    rw [show ((3119862644399 / 250000000000) : ℝ) = ((250000000000 / 3119862644399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0201

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0202Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0202
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

theorem reflection_log_1_neg : (585527169 / 1000000000) ≤ -Real.log (3200 / 5747) ∧
    -Real.log (3200 / 5747) ≤ (58552717 / 100000000) := by
  have h := checkLog_sound (w := (2547 / 8947)) (n := 12)
    (lo := (585527169 / 1000000000)) (hi := (58552717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5747 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5747 / 3200) = 1/(3200 / 5747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (585527169 / 1000000000) (58552717 / 100000000) (Real.log (5747 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5747 / 3200) = -Real.log (3200 / 5747) := by
    rw [show ((5747 / 3200) : ℝ) = ((3200 / 5747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (794664479 / 500000000) ≤ -Real.log (653 / 3200) ∧
    -Real.log (653 / 3200) ≤ (1589328961 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 1453)) (n := 12)
    (lo := (101517299 / 500000000)) (hi := (203034599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 653) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 653) = 1/(653 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1589328961 / 1000000000) (-794664479 / 500000000) (Real.log (653 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (582215619 / 1000000000) ≤ -Real.log (100 / 179) ∧
    -Real.log (100 / 179) ≤ (29110781 / 50000000) := by
  have h := checkLog_sound (w := (79 / 279)) (n := 12)
    (lo := (582215619 / 1000000000)) (hi := (29110781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179 / 100) = 1/(100 / 179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (582215619 / 1000000000) (29110781 / 50000000) (Real.log (179 / 100)) := by
  have h := reflection_log_3_neg
  have he : Real.log (179 / 100) = -Real.log (100 / 179) := by
    rw [show ((179 / 100) : ℝ) = ((100 / 179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1560647747 / 1000000000) ≤ -Real.log (21 / 100) ∧
    -Real.log (21 / 100) ≤ (6242591 / 4000000) := by
  have h := checkLog_sound (w := (2 / 23)) (n := 12)
    (lo := (174353387 / 1000000000)) (hi := (43588347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 21) = 1/(21 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6242591 / 4000000) (-1560647747 / 1000000000) (Real.log (21 / 100)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (232456283 / 500000000) ≤ -Real.log (1600 / 2547) ∧
    -Real.log (1600 / 2547) ≤ (464912567 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 4147)) (n := 12)
    (lo := (232456283 / 500000000)) (hi := (464912567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 1600) = 1/(1600 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (232456283 / 500000000) (464912567 / 1000000000) (Real.log (2547 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2547 / 1600) = -Real.log (1600 / 2547) := by
    rw [show ((2547 / 1600) : ℝ) = ((1600 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (448090889 / 500000000) ≤ -Real.log (653 / 1600) ∧
    -Real.log (653 / 1600) ≤ (44809089 / 50000000) := by
  have h := checkLog_sound (w := (147 / 1453)) (n := 12)
    (lo := (101517299 / 500000000)) (hi := (203034599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 653) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 653) = 1/(653 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-44809089 / 50000000) (-448090889 / 500000000) (Real.log (653 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (457424847 / 1000000000) ≤ -Real.log (50 / 79) ∧
    -Real.log (50 / 79) ≤ (28589053 / 62500000) := by
  have h := checkLog_sound (w := (29 / 129)) (n := 12)
    (lo := (457424847 / 1000000000)) (hi := (28589053 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79 / 50) = 1/(50 / 79) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (457424847 / 1000000000) (28589053 / 62500000) (Real.log (79 / 50)) := by
  have h := reflection_log_7_neg
  have he : Real.log (79 / 50) = -Real.log (50 / 79) := by
    rw [show ((79 / 50) : ℝ) = ((50 / 79) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (867500567 / 1000000000) ≤ -Real.log (21 / 50) ∧
    -Real.log (21 / 50) ≤ (867500569 / 1000000000) := by
  have h := checkLog_sound (w := (2 / 23)) (n := 12)
    (lo := (174353387 / 1000000000)) (hi := (43588347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 21) = 1/(21 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-867500569 / 1000000000) (-867500567 / 1000000000) (Real.log (21 / 50)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (619181967 / 1000000000) ≤ -Real.log (15625 / 29022) ∧
    -Real.log (15625 / 29022) ≤ (38698873 / 62500000) := by
  have h := checkLog_sound (w := (13397 / 44647)) (n := 12)
    (lo := (619181967 / 1000000000)) (hi := (38698873 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29022 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29022 / 15625) = 1/(15625 / 29022) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (619181967 / 1000000000) (38698873 / 62500000) (Real.log (29022 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (29022 / 15625) = -Real.log (15625 / 29022) := by
    rw [show ((29022 / 15625) : ℝ) = ((15625 / 29022) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (30433873 / 15625000) ≤ -Real.log (2228 / 15625) ∧
    -Real.log (2228 / 15625) ≤ (15582143 / 8000000) := by
  have h := checkLog_sound (w := (6713 / 24537)) (n := 12)
    (lo := (70184189 / 125000000)) (hi := (561473513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8912) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 8912) = 1/(2228 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-15582143 / 8000000) (-30433873 / 15625000) (Real.log (2228 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (310422903 / 500000000) ≤ -Real.log (1000000 / 1860501) ∧
    -Real.log (1000000 / 1860501) ≤ (620845807 / 1000000000) := by
  have h := checkLog_sound (w := (860501 / 2860501)) (n := 12)
    (lo := (310422903 / 500000000)) (hi := (620845807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1860501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1860501 / 1000000) = 1/(1000000 / 1860501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (310422903 / 500000000) (620845807 / 1000000000) (Real.log (1860501 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1860501 / 1000000) = -Real.log (1000000 / 1860501) := by
    rw [show ((1860501 / 1000000) : ℝ) = ((1000000 / 1860501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (393939569 / 200000000) ≤ -Real.log (139499 / 1000000) ∧
    -Real.log (139499 / 1000000) ≤ (246212231 / 125000000) := by
  have h := checkLog_sound (w := (110501 / 389499)) (n := 12)
    (lo := (116680697 / 200000000)) (hi := (291701743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 139499) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 139499) = 1/(139499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-246212231 / 125000000) (-393939569 / 200000000) (Real.log (139499 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (305848971 / 500000000) ≤ -Real.log (1000000 / 1843559) ∧
    -Real.log (1000000 / 1843559) ≤ (611697943 / 1000000000) := by
  have h := checkLog_sound (w := (843559 / 2843559)) (n := 12)
    (lo := (305848971 / 500000000)) (hi := (611697943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1843559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1843559 / 1000000) = 1/(1000000 / 1843559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (305848971 / 500000000) (611697943 / 1000000000) (Real.log (1843559 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1843559 / 1000000) = -Real.log (1000000 / 1843559) := by
    rw [show ((1843559 / 1000000) : ℝ) = ((1000000 / 1843559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (371015267 / 200000000) ≤ -Real.log (156441 / 1000000) ∧
    -Real.log (156441 / 1000000) ≤ (927538169 / 500000000) := by
  have h := checkLog_sound (w := (93559 / 406441)) (n := 12)
    (lo := (18751279 / 40000000)) (hi := (58597747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 156441) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 156441) = 1/(156441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-927538169 / 500000000) (-371015267 / 200000000) (Real.log (156441 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (30693969 / 50000000) ≤ -Real.log (200000 / 369517) ∧
    -Real.log (200000 / 369517) ≤ (613879381 / 1000000000) := by
  have h := checkLog_sound (w := (169517 / 569517)) (n := 12)
    (lo := (30693969 / 50000000)) (hi := (613879381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369517 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369517 / 200000) = 1/(200000 / 369517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (30693969 / 50000000) (613879381 / 1000000000) (Real.log (369517 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (369517 / 200000) = -Real.log (200000 / 369517) := by
    rw [show ((369517 / 200000) : ℝ) = ((200000 / 369517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (940574107 / 500000000) ≤ -Real.log (30483 / 200000) ∧
    -Real.log (30483 / 200000) ≤ (1881148217 / 1000000000) := by
  have h := checkLog_sound (w := (19517 / 80483)) (n := 12)
    (lo := (247426927 / 500000000)) (hi := (98970771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30483) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 30483) = 1/(30483 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1881148217 / 1000000000) (-940574107 / 500000000) (Real.log (30483 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2566949839 / 1000000000) ≤ -Real.log (500000000000 / 6513016157989) ∧
    -Real.log (500000000000 / 6513016157989) ≤ (2566949843 / 1000000000) := by
  have h := checkLog_sound (w := (2513016157989 / 10513016157989)) (n := 12)
    (lo := (487508299 / 1000000000)) (hi := (4875083 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6513016157989 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6513016157989 / 4000000000000) = 1/(500000000000 / 6513016157989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2566949839 / 1000000000) (2566949843 / 1000000000) (Real.log (6513016157989 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6513016157989 / 500000000000) = -Real.log (500000000000 / 6513016157989) := by
    rw [show ((6513016157989 / 500000000000) : ℝ) = ((500000000000 / 6513016157989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (51810873 / 20000000) ≤ -Real.log (125000000000 / 1667127542133) ∧
    -Real.log (125000000000 / 1667127542133) ≤ (1295271827 / 500000000) := by
  have h := checkLog_sound (w := (667127542133 / 2667127542133)) (n := 12)
    (lo := (51110211 / 100000000)) (hi := (511102111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1667127542133 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1667127542133 / 1000000000000) = 1/(125000000000 / 1667127542133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (51810873 / 20000000) (1295271827 / 500000000) (Real.log (1667127542133 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1667127542133 / 125000000000) = -Real.log (125000000000 / 1667127542133) := by
    rw [show ((1667127542133 / 125000000000) : ℝ) = ((125000000000 / 1667127542133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2466774277 / 1000000000) ≤ -Real.log (500000000000 / 5892186191599) ∧
    -Real.log (500000000000 / 5892186191599) ≤ (2466774281 / 1000000000) := by
  have h := checkLog_sound (w := (1892186191599 / 9892186191599)) (n := 12)
    (lo := (387332737 / 1000000000)) (hi := (193666369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5892186191599 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5892186191599 / 4000000000000) = 1/(500000000000 / 5892186191599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2466774277 / 1000000000) (2466774281 / 1000000000) (Real.log (5892186191599 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5892186191599 / 500000000000) = -Real.log (500000000000 / 5892186191599) := by
    rw [show ((5892186191599 / 500000000000) : ℝ) = ((500000000000 / 5892186191599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1247513797 / 500000000) ≤ -Real.log (250000000000 / 3030517009481) ∧
    -Real.log (250000000000 / 3030517009481) ≤ (1247513799 / 500000000) := by
  have h := checkLog_sound (w := (1030517009481 / 5030517009481)) (n := 12)
    (lo := (207793027 / 500000000)) (hi := (83117211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3030517009481 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3030517009481 / 2000000000000) = 1/(250000000000 / 3030517009481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1247513797 / 500000000) (1247513799 / 500000000) (Real.log (3030517009481 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3030517009481 / 250000000000) = -Real.log (250000000000 / 3030517009481) := by
    rw [show ((3030517009481 / 250000000000) : ℝ) = ((250000000000 / 3030517009481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0202

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0203Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0203
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

theorem reflection_log_1_neg : (582215619 / 1000000000) ≤ -Real.log (100 / 179) ∧
    -Real.log (100 / 179) ≤ (29110781 / 50000000) := by
  have h := checkLog_sound (w := (79 / 279)) (n := 12)
    (lo := (582215619 / 1000000000)) (hi := (29110781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179 / 100) = 1/(100 / 179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (582215619 / 1000000000) (29110781 / 50000000) (Real.log (179 / 100)) := by
  have h := reflection_log_1_neg
  have he : Real.log (179 / 100) = -Real.log (100 / 179) := by
    rw [show ((179 / 100) : ℝ) = ((100 / 179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1560647747 / 1000000000) ≤ -Real.log (21 / 100) ∧
    -Real.log (21 / 100) ≤ (6242591 / 4000000) := by
  have h := checkLog_sound (w := (2 / 23)) (n := 12)
    (lo := (174353387 / 1000000000)) (hi := (43588347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 21) = 1/(21 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6242591 / 4000000) (-1560647747 / 1000000000) (Real.log (21 / 100)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (578893067 / 1000000000) ≤ -Real.log (3200 / 5709) ∧
    -Real.log (3200 / 5709) ≤ (144723267 / 250000000) := by
  have h := checkLog_sound (w := (2509 / 8909)) (n := 12)
    (lo := (578893067 / 1000000000)) (hi := (144723267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5709 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5709 / 3200) = 1/(3200 / 5709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (578893067 / 1000000000) (144723267 / 250000000) (Real.log (5709 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5709 / 3200) = -Real.log (3200 / 5709) := by
    rw [show ((5709 / 3200) : ℝ) = ((3200 / 5709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1532766263 / 1000000000) ≤ -Real.log (691 / 3200) ∧
    -Real.log (691 / 3200) ≤ (766383133 / 500000000) := by
  have h := checkLog_sound (w := (109 / 1491)) (n := 12)
    (lo := (146471903 / 1000000000)) (hi := (4577247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 691) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 691) = 1/(691 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-766383133 / 500000000) (-1532766263 / 1000000000) (Real.log (691 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (457424847 / 1000000000) ≤ -Real.log (50 / 79) ∧
    -Real.log (50 / 79) ≤ (28589053 / 62500000) := by
  have h := checkLog_sound (w := (29 / 129)) (n := 12)
    (lo := (457424847 / 1000000000)) (hi := (28589053 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79 / 50) = 1/(50 / 79) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (457424847 / 1000000000) (28589053 / 62500000) (Real.log (79 / 50)) := by
  have h := reflection_log_5_neg
  have he : Real.log (79 / 50) = -Real.log (50 / 79) := by
    rw [show ((79 / 50) : ℝ) = ((50 / 79) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (867500567 / 1000000000) ≤ -Real.log (21 / 50) ∧
    -Real.log (21 / 50) ≤ (867500569 / 1000000000) := by
  have h := checkLog_sound (w := (2 / 23)) (n := 12)
    (lo := (174353387 / 1000000000)) (hi := (43588347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 21) = 1/(21 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-867500569 / 1000000000) (-867500567 / 1000000000) (Real.log (21 / 50)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (224940319 / 500000000) ≤ -Real.log (1600 / 2509) ∧
    -Real.log (1600 / 2509) ≤ (449880639 / 1000000000) := by
  have h := checkLog_sound (w := (909 / 4109)) (n := 12)
    (lo := (224940319 / 500000000)) (hi := (449880639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2509 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2509 / 1600) = 1/(1600 / 2509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (224940319 / 500000000) (449880639 / 1000000000) (Real.log (2509 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2509 / 1600) = -Real.log (1600 / 2509) := by
    rw [show ((2509 / 1600) : ℝ) = ((1600 / 2509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (839619083 / 1000000000) ≤ -Real.log (691 / 1600) ∧
    -Real.log (691 / 1600) ≤ (167923817 / 200000000) := by
  have h := checkLog_sound (w := (109 / 1491)) (n := 12)
    (lo := (146471903 / 1000000000)) (hi := (4577247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 691) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 691) = 1/(691 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-167923817 / 200000000) (-839619083 / 1000000000) (Real.log (691 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (308772777 / 500000000) ≤ -Real.log (1000000 / 1854371) ∧
    -Real.log (1000000 / 1854371) ≤ (123509111 / 200000000) := by
  have h := checkLog_sound (w := (854371 / 2854371)) (n := 12)
    (lo := (308772777 / 500000000)) (hi := (123509111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1854371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1854371 / 1000000) = 1/(1000000 / 1854371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (308772777 / 500000000) (123509111 / 200000000) (Real.log (1854371 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1854371 / 1000000) = -Real.log (1000000 / 1854371) := by
    rw [show ((1854371 / 1000000) : ℝ) = ((1000000 / 1854371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (963346493 / 500000000) ≤ -Real.log (145629 / 1000000) ∧
    -Real.log (145629 / 1000000) ≤ (1926692989 / 1000000000) := by
  have h := checkLog_sound (w := (104371 / 395629)) (n := 12)
    (lo := (270199313 / 500000000)) (hi := (540398627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145629) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 145629) = 1/(145629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1926692989 / 1000000000) (-963346493 / 500000000) (Real.log (145629 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (123836501 / 200000000) ≤ -Real.log (1000000 / 1857409) ∧
    -Real.log (1000000 / 1857409) ≤ (309591253 / 500000000) := by
  have h := checkLog_sound (w := (857409 / 2857409)) (n := 12)
    (lo := (123836501 / 200000000)) (hi := (309591253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1857409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1857409 / 1000000) = 1/(1000000 / 1857409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (123836501 / 200000000) (309591253 / 500000000) (Real.log (1857409 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1857409 / 1000000) = -Real.log (1000000 / 1857409) := by
    rw [show ((1857409 / 1000000) : ℝ) = ((1000000 / 1857409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (389554977 / 200000000) ≤ -Real.log (142591 / 1000000) ∧
    -Real.log (142591 / 1000000) ≤ (243471861 / 125000000) := by
  have h := checkLog_sound (w := (107409 / 392591)) (n := 12)
    (lo := (22459221 / 40000000)) (hi := (280740263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 142591) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 142591) = 1/(142591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-243471861 / 125000000) (-389554977 / 200000000) (Real.log (142591 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38095027 / 62500000) ≤ -Real.log (1000000 / 1839549) ∧
    -Real.log (1000000 / 1839549) ≤ (609520433 / 1000000000) := by
  have h := checkLog_sound (w := (839549 / 2839549)) (n := 12)
    (lo := (38095027 / 62500000)) (hi := (609520433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839549 / 1000000) = 1/(1000000 / 1839549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38095027 / 62500000) (609520433 / 1000000000) (Real.log (1839549 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1839549 / 1000000) = -Real.log (1000000 / 1839549) := by
    rw [show ((1839549 / 1000000) : ℝ) = ((1000000 / 1839549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1829766677 / 1000000000) ≤ -Real.log (160451 / 1000000) ∧
    -Real.log (160451 / 1000000) ≤ (45744167 / 25000000) := by
  have h := checkLog_sound (w := (89549 / 410451)) (n := 12)
    (lo := (443472317 / 1000000000)) (hi := (221736159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160451) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 160451) = 1/(160451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-45744167 / 25000000) (-1829766677 / 1000000000) (Real.log (160451 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (152924621 / 250000000) ≤ -Real.log (25000 / 46089) ∧
    -Real.log (25000 / 46089) ≤ (122339697 / 200000000) := by
  have h := checkLog_sound (w := (21089 / 71089)) (n := 12)
    (lo := (152924621 / 250000000)) (hi := (122339697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46089 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46089 / 25000) = 1/(25000 / 46089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (152924621 / 250000000) (122339697 / 200000000) (Real.log (46089 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (46089 / 25000) = -Real.log (25000 / 46089) := by
    rw [show ((46089 / 25000) : ℝ) = ((25000 / 46089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1855082727 / 1000000000) ≤ -Real.log (3911 / 25000) ∧
    -Real.log (3911 / 25000) ≤ (185508273 / 100000000) := by
  have h := checkLog_sound (w := (2339 / 10161)) (n := 12)
    (lo := (468788367 / 1000000000)) (hi := (29299273 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3911) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(6250 / 3911) = 1/(3911 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-185508273 / 100000000) (-1855082727 / 1000000000) (Real.log (3911 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (127211927 / 50000000) ≤ -Real.log (500000000000 / 6366764174717) ∧
    -Real.log (500000000000 / 6366764174717) ≤ (159014909 / 62500000) := by
  have h := checkLog_sound (w := (2366764174717 / 10366764174717)) (n := 12)
    (lo := (464797 / 1000000)) (hi := (464797001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6366764174717 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6366764174717 / 4000000000000) = 1/(500000000000 / 6366764174717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127211927 / 50000000) (159014909 / 62500000) (Real.log (6366764174717 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6366764174717 / 500000000000) = -Real.log (500000000000 / 6366764174717) := by
    rw [show ((6366764174717 / 500000000000) : ℝ) = ((500000000000 / 6366764174717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (256695739 / 100000000) ≤ -Real.log (50000000000 / 651306534073) ∧
    -Real.log (50000000000 / 651306534073) ≤ (1283478697 / 500000000) := by
  have h := checkLog_sound (w := (251306534073 / 1051306534073)) (n := 12)
    (lo := (9750317 / 20000000)) (hi := (487515851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651306534073 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(651306534073 / 400000000000) = 1/(50000000000 / 651306534073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (256695739 / 100000000) (1283478697 / 500000000) (Real.log (651306534073 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (651306534073 / 50000000000) = -Real.log (50000000000 / 651306534073) := by
    rw [show ((651306534073 / 50000000000) : ℝ) = ((50000000000 / 651306534073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (243928711 / 100000000) ≤ -Real.log (100000000000 / 1146486466273) ∧
    -Real.log (100000000000 / 1146486466273) ≤ (1219643557 / 500000000) := by
  have h := checkLog_sound (w := (346486466273 / 1946486466273)) (n := 12)
    (lo := (35984557 / 100000000)) (hi := (359845571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146486466273 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1146486466273 / 800000000000) = 1/(100000000000 / 1146486466273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (243928711 / 100000000) (1219643557 / 500000000) (Real.log (1146486466273 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1146486466273 / 100000000000) = -Real.log (100000000000 / 1146486466273) := by
    rw [show ((1146486466273 / 100000000000) : ℝ) = ((100000000000 / 1146486466273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (616695303 / 250000000) ≤ -Real.log (100000000000 / 1178445410381) ∧
    -Real.log (100000000000 / 1178445410381) ≤ (77086913 / 31250000) := by
  have h := checkLog_sound (w := (378445410381 / 1978445410381)) (n := 12)
    (lo := (48417459 / 125000000)) (hi := (387339673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178445410381 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1178445410381 / 800000000000) = 1/(100000000000 / 1178445410381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (616695303 / 250000000) (77086913 / 31250000) (Real.log (1178445410381 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1178445410381 / 100000000000) = -Real.log (100000000000 / 1178445410381) := by
    rw [show ((1178445410381 / 100000000000) : ℝ) = ((100000000000 / 1178445410381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0203

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0204Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0204
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

theorem reflection_log_1_neg : (578893067 / 1000000000) ≤ -Real.log (3200 / 5709) ∧
    -Real.log (3200 / 5709) ≤ (144723267 / 250000000) := by
  have h := checkLog_sound (w := (2509 / 8909)) (n := 12)
    (lo := (578893067 / 1000000000)) (hi := (144723267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5709 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5709 / 3200) = 1/(3200 / 5709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (578893067 / 1000000000) (144723267 / 250000000) (Real.log (5709 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5709 / 3200) = -Real.log (3200 / 5709) := by
    rw [show ((5709 / 3200) : ℝ) = ((3200 / 5709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1532766263 / 1000000000) ≤ -Real.log (691 / 3200) ∧
    -Real.log (691 / 3200) ≤ (766383133 / 500000000) := by
  have h := checkLog_sound (w := (109 / 1491)) (n := 12)
    (lo := (146471903 / 1000000000)) (hi := (4577247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 691) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 691) = 1/(691 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-766383133 / 500000000) (-1532766263 / 1000000000) (Real.log (691 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (287779719 / 500000000) ≤ -Real.log (320 / 569) ∧
    -Real.log (320 / 569) ≤ (575559439 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 889)) (n := 12)
    (lo := (287779719 / 500000000)) (hi := (575559439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569 / 320) = 1/(320 / 569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (287779719 / 500000000) (575559439 / 1000000000) (Real.log (569 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (569 / 320) = -Real.log (320 / 569) := by
    rw [show ((569 / 320) : ℝ) = ((320 / 569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1505641117 / 1000000000) ≤ -Real.log (71 / 320) ∧
    -Real.log (71 / 320) ≤ (9410257 / 6250000) := by
  have h := checkLog_sound (w := (9 / 151)) (n := 12)
    (lo := (119346757 / 1000000000)) (hi := (59673379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 71) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 71) = 1/(71 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-9410257 / 6250000) (-1505641117 / 1000000000) (Real.log (71 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (224940319 / 500000000) ≤ -Real.log (1600 / 2509) ∧
    -Real.log (1600 / 2509) ≤ (449880639 / 1000000000) := by
  have h := checkLog_sound (w := (909 / 4109)) (n := 12)
    (lo := (224940319 / 500000000)) (hi := (449880639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2509 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2509 / 1600) = 1/(1600 / 2509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (224940319 / 500000000) (449880639 / 1000000000) (Real.log (2509 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2509 / 1600) = -Real.log (1600 / 2509) := by
    rw [show ((2509 / 1600) : ℝ) = ((1600 / 2509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (839619083 / 1000000000) ≤ -Real.log (691 / 1600) ∧
    -Real.log (691 / 1600) ≤ (167923817 / 200000000) := by
  have h := checkLog_sound (w := (109 / 1491)) (n := 12)
    (lo := (146471903 / 1000000000)) (hi := (4577247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 691) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 691) = 1/(691 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-167923817 / 200000000) (-839619083 / 1000000000) (Real.log (691 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (442279081 / 1000000000) ≤ -Real.log (160 / 249) ∧
    -Real.log (160 / 249) ≤ (221139541 / 500000000) := by
  have h := checkLog_sound (w := (89 / 409)) (n := 12)
    (lo := (442279081 / 1000000000)) (hi := (221139541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249 / 160) = 1/(160 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (442279081 / 1000000000) (221139541 / 500000000) (Real.log (249 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (249 / 160) = -Real.log (160 / 249) := by
    rw [show ((249 / 160) : ℝ) = ((160 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (812493937 / 1000000000) ≤ -Real.log (71 / 160) ∧
    -Real.log (71 / 160) ≤ (812493939 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 151)) (n := 12)
    (lo := (119346757 / 1000000000)) (hi := (59673379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 71) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 71) = 1/(71 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-812493939 / 1000000000) (-812493937 / 1000000000) (Real.log (71 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (76992021 / 125000000) ≤ -Real.log (1000000 / 1851389) ∧
    -Real.log (1000000 / 1851389) ≤ (615936169 / 1000000000) := by
  have h := checkLog_sound (w := (851389 / 2851389)) (n := 12)
    (lo := (76992021 / 125000000)) (hi := (615936169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1851389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1851389 / 1000000) = 1/(1000000 / 1851389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (76992021 / 125000000) (615936169 / 1000000000) (Real.log (1851389 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1851389 / 1000000) = -Real.log (1000000 / 1851389) := by
    rw [show ((1851389 / 1000000) : ℝ) = ((1000000 / 1851389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (476605781 / 250000000) ≤ -Real.log (148611 / 1000000) ∧
    -Real.log (148611 / 1000000) ≤ (1906423127 / 1000000000) := by
  have h := checkLog_sound (w := (101389 / 398611)) (n := 12)
    (lo := (130032191 / 250000000)) (hi := (104025753 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148611) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 148611) = 1/(148611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1906423127 / 1000000000) (-476605781 / 250000000) (Real.log (148611 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (308773047 / 500000000) ≤ -Real.log (250000 / 463593) ∧
    -Real.log (250000 / 463593) ≤ (123509219 / 200000000) := by
  have h := checkLog_sound (w := (213593 / 713593)) (n := 12)
    (lo := (308773047 / 500000000)) (hi := (123509219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463593 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463593 / 250000) = 1/(250000 / 463593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (308773047 / 500000000) (123509219 / 200000000) (Real.log (463593 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (463593 / 250000) = -Real.log (250000 / 463593) := by
    rw [show ((463593 / 250000) : ℝ) = ((250000 / 463593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (481674963 / 250000000) ≤ -Real.log (36407 / 250000) ∧
    -Real.log (36407 / 250000) ≤ (385339971 / 200000000) := by
  have h := checkLog_sound (w := (26093 / 98907)) (n := 12)
    (lo := (135101373 / 250000000)) (hi := (540405493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36407) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 36407) = 1/(36407 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-385339971 / 200000000) (-481674963 / 250000000) (Real.log (36407 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (303672899 / 500000000) ≤ -Real.log (1000000 / 1835553) ∧
    -Real.log (1000000 / 1835553) ≤ (607345799 / 1000000000) := by
  have h := checkLog_sound (w := (835553 / 2835553)) (n := 12)
    (lo := (303672899 / 500000000)) (hi := (607345799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1835553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1835553 / 1000000) = 1/(1000000 / 1835553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (303672899 / 500000000) (607345799 / 1000000000) (Real.log (1835553 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1835553 / 1000000) = -Real.log (1000000 / 1835553) := by
    rw [show ((1835553 / 1000000) : ℝ) = ((1000000 / 1835553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (451291737 / 250000000) ≤ -Real.log (164447 / 1000000) ∧
    -Real.log (164447 / 1000000) ≤ (1805166951 / 1000000000) := by
  have h := checkLog_sound (w := (85553 / 414447)) (n := 12)
    (lo := (104718147 / 250000000)) (hi := (418872589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164447) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 164447) = 1/(164447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1805166951 / 1000000000) (-451291737 / 250000000) (Real.log (164447 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38095061 / 62500000) ≤ -Real.log (20000 / 36791) ∧
    -Real.log (20000 / 36791) ≤ (609520977 / 1000000000) := by
  have h := checkLog_sound (w := (16791 / 56791)) (n := 12)
    (lo := (38095061 / 62500000)) (hi := (609520977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36791 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36791 / 20000) = 1/(20000 / 36791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38095061 / 62500000) (609520977 / 1000000000) (Real.log (36791 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (36791 / 20000) = -Real.log (20000 / 36791) := by
    rw [show ((36791 / 20000) : ℝ) = ((20000 / 36791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (182977291 / 100000000) ≤ -Real.log (3209 / 20000) ∧
    -Real.log (3209 / 20000) ≤ (1829772913 / 1000000000) := by
  have h := checkLog_sound (w := (1791 / 8209)) (n := 12)
    (lo := (8869571 / 20000000)) (hi := (443478551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3209) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(5000 / 3209) = 1/(3209 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1829772913 / 1000000000) (-182977291 / 100000000) (Real.log (3209 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2522359291 / 1000000000) ≤ -Real.log (500000000000 / 6228976993627) ∧
    -Real.log (500000000000 / 6228976993627) ≤ (504471859 / 200000000) := by
  have h := checkLog_sound (w := (2228976993627 / 10228976993627)) (n := 12)
    (lo := (442917751 / 1000000000)) (hi := (55364719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6228976993627 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6228976993627 / 4000000000000) = 1/(500000000000 / 6228976993627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2522359291 / 1000000000) (504471859 / 200000000) (Real.log (6228976993627 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6228976993627 / 500000000000) = -Real.log (500000000000 / 6228976993627) := by
    rw [show ((6228976993627 / 500000000000) : ℝ) = ((500000000000 / 6228976993627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1272122973 / 500000000) ≤ -Real.log (125000000000 / 1591702831873) ∧
    -Real.log (125000000000 / 1591702831873) ≤ (50884919 / 20000000) := by
  have h := checkLog_sound (w := (591702831873 / 2591702831873)) (n := 12)
    (lo := (232402203 / 500000000)) (hi := (464804407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1591702831873 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1591702831873 / 1000000000000) = 1/(125000000000 / 1591702831873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1272122973 / 500000000) (50884919 / 20000000) (Real.log (1591702831873 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1591702831873 / 125000000000) = -Real.log (125000000000 / 1591702831873) := by
    rw [show ((1591702831873 / 125000000000) : ℝ) = ((125000000000 / 1591702831873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (482502549 / 200000000) ≤ -Real.log (250000000000 / 2790493289631) ∧
    -Real.log (250000000000 / 2790493289631) ≤ (2412512749 / 1000000000) := by
  have h := checkLog_sound (w := (790493289631 / 4790493289631)) (n := 12)
    (lo := (66614241 / 200000000)) (hi := (166535603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2790493289631 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2790493289631 / 2000000000000) = 1/(250000000000 / 2790493289631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (482502549 / 200000000) (2412512749 / 1000000000) (Real.log (2790493289631 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2790493289631 / 250000000000) = -Real.log (250000000000 / 2790493289631) := by
    rw [show ((2790493289631 / 250000000000) : ℝ) = ((250000000000 / 2790493289631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1219646943 / 500000000) ≤ -Real.log (500000000000 / 5732471174821) ∧
    -Real.log (500000000000 / 5732471174821) ≤ (243929389 / 100000000) := by
  have h := checkLog_sound (w := (1732471174821 / 9732471174821)) (n := 12)
    (lo := (179926173 / 500000000)) (hi := (359852347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5732471174821 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5732471174821 / 4000000000000) = 1/(500000000000 / 5732471174821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1219646943 / 500000000) (243929389 / 100000000) (Real.log (5732471174821 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5732471174821 / 500000000000) = -Real.log (500000000000 / 5732471174821) := by
    rw [show ((5732471174821 / 500000000000) : ℝ) = ((500000000000 / 5732471174821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0204

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0205Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0205
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

theorem reflection_log_1_neg : (287779719 / 500000000) ≤ -Real.log (320 / 569) ∧
    -Real.log (320 / 569) ≤ (575559439 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 889)) (n := 12)
    (lo := (287779719 / 500000000)) (hi := (575559439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569 / 320) = 1/(320 / 569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (287779719 / 500000000) (575559439 / 1000000000) (Real.log (569 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (569 / 320) = -Real.log (320 / 569) := by
    rw [show ((569 / 320) : ℝ) = ((320 / 569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1505641117 / 1000000000) ≤ -Real.log (71 / 320) ∧
    -Real.log (71 / 320) ≤ (9410257 / 6250000) := by
  have h := checkLog_sound (w := (9 / 151)) (n := 12)
    (lo := (119346757 / 1000000000)) (hi := (59673379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 71) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 71) = 1/(71 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-9410257 / 6250000) (-1505641117 / 1000000000) (Real.log (71 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (572214659 / 1000000000) ≤ -Real.log (3200 / 5671) ∧
    -Real.log (3200 / 5671) ≤ (28610733 / 50000000) := by
  have h := checkLog_sound (w := (2471 / 8871)) (n := 12)
    (lo := (572214659 / 1000000000)) (hi := (28610733 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5671 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5671 / 3200) = 1/(3200 / 5671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (572214659 / 1000000000) (28610733 / 50000000) (Real.log (5671 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5671 / 3200) = -Real.log (3200 / 5671) := by
    rw [show ((5671 / 3200) : ℝ) = ((3200 / 5671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (295846471 / 200000000) ≤ -Real.log (729 / 3200) ∧
    -Real.log (729 / 3200) ≤ (739616179 / 500000000) := by
  have h := checkLog_sound (w := (71 / 1529)) (n := 12)
    (lo := (18587599 / 200000000)) (hi := (23234499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 729) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 729) = 1/(729 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-739616179 / 500000000) (-295846471 / 200000000) (Real.log (729 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (442279081 / 1000000000) ≤ -Real.log (160 / 249) ∧
    -Real.log (160 / 249) ≤ (221139541 / 500000000) := by
  have h := checkLog_sound (w := (89 / 409)) (n := 12)
    (lo := (442279081 / 1000000000)) (hi := (221139541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249 / 160) = 1/(160 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (442279081 / 1000000000) (221139541 / 500000000) (Real.log (249 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (249 / 160) = -Real.log (160 / 249) := by
    rw [show ((249 / 160) : ℝ) = ((160 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (812493937 / 1000000000) ≤ -Real.log (71 / 160) ∧
    -Real.log (71 / 160) ≤ (812493939 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 151)) (n := 12)
    (lo := (119346757 / 1000000000)) (hi := (59673379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 71) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 71) = 1/(71 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-812493939 / 1000000000) (-812493937 / 1000000000) (Real.log (71 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (434619297 / 1000000000) ≤ -Real.log (1600 / 2471) ∧
    -Real.log (1600 / 2471) ≤ (217309649 / 500000000) := by
  have h := checkLog_sound (w := (871 / 4071)) (n := 12)
    (lo := (434619297 / 1000000000)) (hi := (217309649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2471 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2471 / 1600) = 1/(1600 / 2471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (434619297 / 1000000000) (217309649 / 500000000) (Real.log (2471 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2471 / 1600) = -Real.log (1600 / 2471) := by
    rw [show ((2471 / 1600) : ℝ) = ((1600 / 2471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (31443407 / 40000000) ≤ -Real.log (729 / 1600) ∧
    -Real.log (729 / 1600) ≤ (786085177 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 1529)) (n := 12)
    (lo := (18587599 / 200000000)) (hi := (23234499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 729) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 729) = 1/(729 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-786085177 / 1000000000) (-31443407 / 40000000) (Real.log (729 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (307177241 / 500000000) ≤ -Real.log (1000000 / 1848463) ∧
    -Real.log (1000000 / 1848463) ≤ (614354483 / 1000000000) := by
  have h := checkLog_sound (w := (848463 / 2848463)) (n := 12)
    (lo := (307177241 / 500000000)) (hi := (614354483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1848463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1848463 / 1000000) = 1/(1000000 / 1848463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (307177241 / 500000000) (614354483 / 1000000000) (Real.log (1848463 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1848463 / 1000000) = -Real.log (1000000 / 1848463) := by
    rw [show ((1848463 / 1000000) : ℝ) = ((1000000 / 1848463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (943462729 / 500000000) ≤ -Real.log (151537 / 1000000) ∧
    -Real.log (151537 / 1000000) ≤ (1886925461 / 1000000000) := by
  have h := checkLog_sound (w := (98463 / 401537)) (n := 12)
    (lo := (250315549 / 500000000)) (hi := (500631099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 151537) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 151537) = 1/(151537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1886925461 / 1000000000) (-943462729 / 500000000) (Real.log (151537 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153984177 / 250000000) ≤ -Real.log (100000 / 185139) ∧
    -Real.log (100000 / 185139) ≤ (615936709 / 1000000000) := by
  have h := checkLog_sound (w := (85139 / 285139)) (n := 12)
    (lo := (153984177 / 250000000)) (hi := (615936709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185139 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185139 / 100000) = 1/(100000 / 185139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153984177 / 250000000) (615936709 / 1000000000) (Real.log (185139 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (185139 / 100000) = -Real.log (100000 / 185139) := by
    rw [show ((185139 / 100000) : ℝ) = ((100000 / 185139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1906429853 / 1000000000) ≤ -Real.log (14861 / 100000) ∧
    -Real.log (14861 / 100000) ≤ (59575933 / 31250000) := by
  have h := checkLog_sound (w := (10139 / 39861)) (n := 12)
    (lo := (520135493 / 1000000000)) (hi := (260067747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 14861) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 14861) = 1/(14861 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-59575933 / 31250000) (-1906429853 / 1000000000) (Real.log (14861 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (151293517 / 250000000) ≤ -Real.log (1000000 / 1831571) ∧
    -Real.log (1000000 / 1831571) ≤ (605174069 / 1000000000) := by
  have h := checkLog_sound (w := (831571 / 2831571)) (n := 12)
    (lo := (151293517 / 250000000)) (hi := (605174069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1831571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1831571 / 1000000) = 1/(1000000 / 1831571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (151293517 / 250000000) (605174069 / 1000000000) (Real.log (1831571 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1831571 / 1000000) = -Real.log (1000000 / 1831571) := by
    rw [show ((1831571 / 1000000) : ℝ) = ((1000000 / 1831571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1781240981 / 1000000000) ≤ -Real.log (168429 / 1000000) ∧
    -Real.log (168429 / 1000000) ≤ (222655123 / 125000000) := by
  have h := checkLog_sound (w := (81571 / 418429)) (n := 12)
    (lo := (394946621 / 1000000000)) (hi := (197473311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 168429) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 168429) = 1/(168429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-222655123 / 125000000) (-1781240981 / 1000000000) (Real.log (168429 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (607346343 / 1000000000) ≤ -Real.log (500000 / 917777) ∧
    -Real.log (500000 / 917777) ≤ (75918293 / 125000000) := by
  have h := checkLog_sound (w := (417777 / 1417777)) (n := 12)
    (lo := (607346343 / 1000000000)) (hi := (75918293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917777 / 500000) = 1/(500000 / 917777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (607346343 / 1000000000) (75918293 / 125000000) (Real.log (917777 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (917777 / 500000) = -Real.log (500000 / 917777) := by
    rw [show ((917777 / 500000) : ℝ) = ((500000 / 917777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1805173029 / 1000000000) ≤ -Real.log (82223 / 500000) ∧
    -Real.log (82223 / 500000) ≤ (225646629 / 125000000) := by
  have h := checkLog_sound (w := (42777 / 207223)) (n := 12)
    (lo := (418878669 / 1000000000)) (hi := (41887867 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82223) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 82223) = 1/(82223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-225646629 / 125000000) (-1805173029 / 1000000000) (Real.log (82223 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (125063997 / 50000000) ≤ -Real.log (250000000000 / 3049524208609) ∧
    -Real.log (250000000000 / 3049524208609) ≤ (312659993 / 125000000) := by
  have h := checkLog_sound (w := (1049524208609 / 5049524208609)) (n := 12)
    (lo := (263649 / 625000)) (hi := (421838401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3049524208609 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3049524208609 / 2000000000000) = 1/(250000000000 / 3049524208609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (125063997 / 50000000) (312659993 / 125000000) (Real.log (3049524208609 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3049524208609 / 250000000000) = -Real.log (250000000000 / 3049524208609) := by
    rw [show ((3049524208609 / 250000000000) : ℝ) = ((250000000000 / 3049524208609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (15764791 / 6250000) ≤ -Real.log (62500000000 / 778627784133) ∧
    -Real.log (62500000000 / 778627784133) ≤ (630591641 / 250000000) := by
  have h := checkLog_sound (w := (278627784133 / 1278627784133)) (n := 12)
    (lo := (22146251 / 50000000)) (hi := (442925021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((778627784133 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(778627784133 / 500000000000) = 1/(62500000000 / 778627784133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (15764791 / 6250000) (630591641 / 250000000) (Real.log (778627784133 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (778627784133 / 62500000000) = -Real.log (62500000000 / 778627784133) := by
    rw [show ((778627784133 / 62500000000) : ℝ) = ((62500000000 / 778627784133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2386415049 / 1000000000) ≤ -Real.log (250000000000 / 2718609918719) ∧
    -Real.log (250000000000 / 2718609918719) ≤ (2386415053 / 1000000000) := by
  have h := checkLog_sound (w := (718609918719 / 4718609918719)) (n := 12)
    (lo := (306973509 / 1000000000)) (hi := (30697351 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2718609918719 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2718609918719 / 2000000000000) = 1/(250000000000 / 2718609918719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2386415049 / 1000000000) (2386415053 / 1000000000) (Real.log (2718609918719 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2718609918719 / 250000000000) = -Real.log (250000000000 / 2718609918719) := by
    rw [show ((2718609918719 / 250000000000) : ℝ) = ((250000000000 / 2718609918719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2412519371 / 1000000000) ≤ -Real.log (250000000000 / 2790511778943) ∧
    -Real.log (250000000000 / 2790511778943) ≤ (3860031 / 1600000) := by
  have h := checkLog_sound (w := (790511778943 / 4790511778943)) (n := 12)
    (lo := (333077831 / 1000000000)) (hi := (41634729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2790511778943 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2790511778943 / 2000000000000) = 1/(250000000000 / 2790511778943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2412519371 / 1000000000) (3860031 / 1600000) (Real.log (2790511778943 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2790511778943 / 250000000000) = -Real.log (250000000000 / 2790511778943) := by
    rw [show ((2790511778943 / 250000000000) : ℝ) = ((250000000000 / 2790511778943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0205

end


