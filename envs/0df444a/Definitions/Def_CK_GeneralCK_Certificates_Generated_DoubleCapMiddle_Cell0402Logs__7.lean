-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0402Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0402Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:10:08.224997+00:00
-- url     : https://prove2.me/theorems/52d0e63a-4be3-4351-9dcd-3a6d02e20884
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0402Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0403Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0402Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0403Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0404Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0405Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0406Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0407Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0408Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0402Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0403Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0404Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0405Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0406Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0407Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0408Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0402Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0403Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0404Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0405Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0406Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0407Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0408Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0402Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0403Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0404Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0405Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0406Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0407Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0408Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0402Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0402
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

theorem reflection_log_1_neg : (199746973 / 1000000000) ≤ -Real.log (1280 / 1563) ∧
    -Real.log (1280 / 1563) ≤ (99873487 / 500000000) := by
  have h := checkLog_sound (w := (283 / 2843)) (n := 12)
    (lo := (199746973 / 1000000000)) (hi := (99873487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1563 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1563 / 1280) = 1/(1280 / 1563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199746973 / 1000000000) (99873487 / 500000000) (Real.log (1563 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1563 / 1280) = -Real.log (1280 / 1563) := by
    rw [show ((1563 / 1280) : ℝ) = ((1280 / 1563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (124932293 / 500000000) ≤ -Real.log (997 / 1280) ∧
    -Real.log (997 / 1280) ≤ (249864587 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 2277)) (n := 12)
    (lo := (124932293 / 500000000)) (hi := (249864587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 997) = 1/(997 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-249864587 / 1000000000) (-124932293 / 500000000) (Real.log (997 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199507021 / 1000000000) ≤ -Real.log (10240 / 12501) ∧
    -Real.log (10240 / 12501) ≤ (99753511 / 500000000) := by
  have h := checkLog_sound (w := (2261 / 22741)) (n := 12)
    (lo := (199507021 / 1000000000)) (hi := (99753511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12501 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12501 / 10240) = 1/(10240 / 12501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199507021 / 1000000000) (99753511 / 500000000) (Real.log (12501 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12501 / 10240) = -Real.log (10240 / 12501) := by
    rw [show ((12501 / 10240) : ℝ) = ((10240 / 12501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (249488529 / 1000000000) ≤ -Real.log (7979 / 10240) ∧
    -Real.log (7979 / 10240) ≤ (24948853 / 100000000) := by
  have h := checkLog_sound (w := (2261 / 18219)) (n := 12)
    (lo := (249488529 / 1000000000)) (hi := (24948853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7979) = 1/(7979 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-24948853 / 100000000) (-249488529 / 1000000000) (Real.log (7979 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (183080529 / 500000000) ≤ -Real.log (640 / 923) ∧
    -Real.log (640 / 923) ≤ (366161059 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1563)) (n := 12)
    (lo := (183080529 / 500000000)) (hi := (366161059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923 / 640) = 1/(640 / 923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (183080529 / 500000000) (366161059 / 1000000000) (Real.log (923 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (923 / 640) = -Real.log (640 / 923) := by
    rw [show ((923 / 640) : ℝ) = ((640 / 923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (291866197 / 500000000) ≤ -Real.log (357 / 640) ∧
    -Real.log (357 / 640) ≤ (116746479 / 200000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 357) = 1/(357 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-116746479 / 200000000) (-291866197 / 500000000) (Real.log (357 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (365754691 / 1000000000) ≤ -Real.log (5120 / 7381) ∧
    -Real.log (5120 / 7381) ≤ (91438673 / 250000000) := by
  have h := checkLog_sound (w := (2261 / 12501)) (n := 12)
    (lo := (365754691 / 1000000000)) (hi := (91438673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7381 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7381 / 5120) = 1/(5120 / 7381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (365754691 / 1000000000) (91438673 / 250000000) (Real.log (7381 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7381 / 5120) = -Real.log (5120 / 7381) := by
    rw [show ((7381 / 5120) : ℝ) = ((5120 / 7381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (23307301 / 40000000) ≤ -Real.log (2859 / 5120) ∧
    -Real.log (2859 / 5120) ≤ (291341263 / 500000000) := by
  have h := checkLog_sound (w := (2261 / 7979)) (n := 12)
    (lo := (23307301 / 40000000)) (hi := (291341263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2859) = 1/(2859 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-291341263 / 500000000) (-23307301 / 40000000) (Real.log (2859 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (273856437 / 1000000000) ≤ -Real.log (500000 / 657513) ∧
    -Real.log (500000 / 657513) ≤ (136928219 / 500000000) := by
  have h := checkLog_sound (w := (157513 / 1157513)) (n := 12)
    (lo := (273856437 / 1000000000)) (hi := (136928219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657513 / 500000) = 1/(500000 / 657513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (273856437 / 1000000000) (136928219 / 500000000) (Real.log (657513 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (657513 / 500000) = -Real.log (500000 / 657513) := by
    rw [show ((657513 / 500000) : ℝ) = ((500000 / 657513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (378374397 / 1000000000) ≤ -Real.log (342487 / 500000) ∧
    -Real.log (342487 / 500000) ≤ (189187199 / 500000000) := by
  have h := checkLog_sound (w := (157513 / 842487)) (n := 12)
    (lo := (378374397 / 1000000000)) (hi := (189187199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342487) = 1/(342487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-189187199 / 500000000) (-378374397 / 1000000000) (Real.log (342487 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68545273 / 250000000) ≤ -Real.log (1000000 / 1315453) ∧
    -Real.log (1000000 / 1315453) ≤ (274181093 / 1000000000) := by
  have h := checkLog_sound (w := (315453 / 2315453)) (n := 12)
    (lo := (68545273 / 250000000)) (hi := (274181093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1315453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1315453 / 1000000) = 1/(1000000 / 1315453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68545273 / 250000000) (274181093 / 1000000000) (Real.log (1315453 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1315453 / 1000000) = -Real.log (1000000 / 1315453) := by
    rw [show ((1315453 / 1000000) : ℝ) = ((1000000 / 1315453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (378997973 / 1000000000) ≤ -Real.log (684547 / 1000000) ∧
    -Real.log (684547 / 1000000) ≤ (189498987 / 500000000) := by
  have h := checkLog_sound (w := (315453 / 1684547)) (n := 12)
    (lo := (378997973 / 1000000000)) (hi := (189498987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 684547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 684547) = 1/(684547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-189498987 / 500000000) (-378997973 / 1000000000) (Real.log (684547 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (206240699 / 1000000000) ≤ -Real.log (1000000 / 1229049) ∧
    -Real.log (1000000 / 1229049) ≤ (2062407 / 10000000) := by
  have h := checkLog_sound (w := (229049 / 2229049)) (n := 12)
    (lo := (206240699 / 1000000000)) (hi := (2062407 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229049 / 1000000) = 1/(1000000 / 1229049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (206240699 / 1000000000) (2062407 / 10000000) (Real.log (1229049 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1229049 / 1000000) = -Real.log (1000000 / 1229049) := by
    rw [show ((1229049 / 1000000) : ℝ) = ((1000000 / 1229049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (260130461 / 1000000000) ≤ -Real.log (770951 / 1000000) ∧
    -Real.log (770951 / 1000000) ≤ (130065231 / 500000000) := by
  have h := checkLog_sound (w := (229049 / 1770951)) (n := 12)
    (lo := (260130461 / 1000000000)) (hi := (130065231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770951) = 1/(770951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-130065231 / 500000000) (-260130461 / 1000000000) (Real.log (770951 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (206507537 / 1000000000) ≤ -Real.log (1000000 / 1229377) ∧
    -Real.log (1000000 / 1229377) ≤ (103253769 / 500000000) := by
  have h := checkLog_sound (w := (229377 / 2229377)) (n := 12)
    (lo := (206507537 / 1000000000)) (hi := (103253769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229377 / 1000000) = 1/(1000000 / 1229377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (206507537 / 1000000000) (103253769 / 500000000) (Real.log (1229377 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1229377 / 1000000) = -Real.log (1000000 / 1229377) := by
    rw [show ((1229377 / 1000000) : ℝ) = ((1000000 / 1229377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (65139 / 250000) ≤ -Real.log (770623 / 1000000) ∧
    -Real.log (770623 / 1000000) ≤ (260556001 / 1000000000) := by
  have h := checkLog_sound (w := (229377 / 1770623)) (n := 12)
    (lo := (65139 / 250000)) (hi := (260556001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770623) = 1/(770623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-260556001 / 1000000000) (-65139 / 250000) (Real.log (770623 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (326115417 / 500000000) ≤ -Real.log (500000000000 / 959909427219) ∧
    -Real.log (500000000000 / 959909427219) ≤ (130446167 / 200000000) := by
  have h := checkLog_sound (w := (459909427219 / 1459909427219)) (n := 12)
    (lo := (326115417 / 500000000)) (hi := (130446167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959909427219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959909427219 / 500000000000) = 1/(500000000000 / 959909427219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (326115417 / 500000000) (130446167 / 200000000) (Real.log (959909427219 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (959909427219 / 500000000000) = -Real.log (500000000000 / 959909427219) := by
    rw [show ((959909427219 / 500000000000) : ℝ) = ((500000000000 / 959909427219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (326589533 / 500000000) ≤ -Real.log (250000000000 / 480410037587) ∧
    -Real.log (250000000000 / 480410037587) ≤ (653179067 / 1000000000) := by
  have h := checkLog_sound (w := (230410037587 / 730410037587)) (n := 12)
    (lo := (326589533 / 500000000)) (hi := (653179067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((480410037587 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(480410037587 / 250000000000) = 1/(250000000000 / 480410037587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (326589533 / 500000000) (653179067 / 1000000000) (Real.log (480410037587 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (480410037587 / 250000000000) = -Real.log (250000000000 / 480410037587) := by
    rw [show ((480410037587 / 250000000000) : ℝ) = ((250000000000 / 480410037587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (11659279 / 25000000) ≤ -Real.log (250000000000 / 398549648421) ∧
    -Real.log (250000000000 / 398549648421) ≤ (466371161 / 1000000000) := by
  have h := checkLog_sound (w := (148549648421 / 648549648421)) (n := 12)
    (lo := (11659279 / 25000000)) (hi := (466371161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398549648421 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398549648421 / 250000000000) = 1/(250000000000 / 398549648421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (11659279 / 25000000) (466371161 / 1000000000) (Real.log (398549648421 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (398549648421 / 250000000000) = -Real.log (250000000000 / 398549648421) := by
    rw [show ((398549648421 / 250000000000) : ℝ) = ((250000000000 / 398549648421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (467063537 / 1000000000) ≤ -Real.log (250000000000 / 398825690383) ∧
    -Real.log (250000000000 / 398825690383) ≤ (233531769 / 500000000) := by
  have h := checkLog_sound (w := (148825690383 / 648825690383)) (n := 12)
    (lo := (467063537 / 1000000000)) (hi := (233531769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398825690383 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398825690383 / 250000000000) = 1/(250000000000 / 398825690383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (467063537 / 1000000000) (233531769 / 500000000) (Real.log (398825690383 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (398825690383 / 250000000000) = -Real.log (250000000000 / 398825690383) := by
    rw [show ((398825690383 / 250000000000) : ℝ) = ((250000000000 / 398825690383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0402

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0403Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0403
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

theorem reflection_log_1_neg : (199507021 / 1000000000) ≤ -Real.log (10240 / 12501) ∧
    -Real.log (10240 / 12501) ≤ (99753511 / 500000000) := by
  have h := checkLog_sound (w := (2261 / 22741)) (n := 12)
    (lo := (199507021 / 1000000000)) (hi := (99753511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12501 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12501 / 10240) = 1/(10240 / 12501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199507021 / 1000000000) (99753511 / 500000000) (Real.log (12501 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12501 / 10240) = -Real.log (10240 / 12501) := by
    rw [show ((12501 / 10240) : ℝ) = ((10240 / 12501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (249488529 / 1000000000) ≤ -Real.log (7979 / 10240) ∧
    -Real.log (7979 / 10240) ≤ (24948853 / 100000000) := by
  have h := checkLog_sound (w := (2261 / 18219)) (n := 12)
    (lo := (249488529 / 1000000000)) (hi := (24948853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7979) = 1/(7979 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-24948853 / 100000000) (-249488529 / 1000000000) (Real.log (7979 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199267011 / 1000000000) ≤ -Real.log (5120 / 6249) ∧
    -Real.log (5120 / 6249) ≤ (49816753 / 250000000) := by
  have h := checkLog_sound (w := (1129 / 11369)) (n := 12)
    (lo := (199267011 / 1000000000)) (hi := (49816753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6249 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6249 / 5120) = 1/(5120 / 6249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199267011 / 1000000000) (49816753 / 250000000) (Real.log (6249 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6249 / 5120) = -Real.log (5120 / 6249) := by
    rw [show ((6249 / 5120) : ℝ) = ((5120 / 6249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (62278153 / 250000000) ≤ -Real.log (3991 / 5120) ∧
    -Real.log (3991 / 5120) ≤ (249112613 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 9111)) (n := 12)
    (lo := (62278153 / 250000000)) (hi := (249112613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3991) = 1/(3991 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-249112613 / 1000000000) (-62278153 / 250000000) (Real.log (3991 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (365754691 / 1000000000) ≤ -Real.log (5120 / 7381) ∧
    -Real.log (5120 / 7381) ≤ (91438673 / 250000000) := by
  have h := checkLog_sound (w := (2261 / 12501)) (n := 12)
    (lo := (365754691 / 1000000000)) (hi := (91438673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7381 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7381 / 5120) = 1/(5120 / 7381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (365754691 / 1000000000) (91438673 / 250000000) (Real.log (7381 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7381 / 5120) = -Real.log (5120 / 7381) := by
    rw [show ((7381 / 5120) : ℝ) = ((5120 / 7381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (23307301 / 40000000) ≤ -Real.log (2859 / 5120) ∧
    -Real.log (2859 / 5120) ≤ (291341263 / 500000000) := by
  have h := checkLog_sound (w := (2261 / 7979)) (n := 12)
    (lo := (23307301 / 40000000)) (hi := (291341263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2859) = 1/(2859 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-291341263 / 500000000) (-23307301 / 40000000) (Real.log (2859 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1141713 / 3125000) ≤ -Real.log (2560 / 3689) ∧
    -Real.log (2560 / 3689) ≤ (365348161 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 6249)) (n := 12)
    (lo := (1141713 / 3125000)) (hi := (365348161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3689 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3689 / 2560) = 1/(2560 / 3689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1141713 / 3125000) (365348161 / 1000000000) (Real.log (3689 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3689 / 2560) = -Real.log (2560 / 3689) := by
    rw [show ((3689 / 2560) : ℝ) = ((2560 / 3689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (581633757 / 1000000000) ≤ -Real.log (1431 / 2560) ∧
    -Real.log (1431 / 2560) ≤ (290816879 / 500000000) := by
  have h := checkLog_sound (w := (1129 / 3991)) (n := 12)
    (lo := (581633757 / 1000000000)) (hi := (290816879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1431) = 1/(1431 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-290816879 / 500000000) (-581633757 / 1000000000) (Real.log (1431 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68383109 / 250000000) ≤ -Real.log (5000 / 6573) ∧
    -Real.log (5000 / 6573) ≤ (273532437 / 1000000000) := by
  have h := checkLog_sound (w := (1573 / 11573)) (n := 12)
    (lo := (68383109 / 250000000)) (hi := (273532437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6573 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6573 / 5000) = 1/(5000 / 6573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68383109 / 250000000) (273532437 / 1000000000) (Real.log (6573 / 5000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (6573 / 5000) = -Real.log (5000 / 6573) := by
    rw [show ((6573 / 5000) : ℝ) = ((5000 / 6573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (377752669 / 1000000000) ≤ -Real.log (3427 / 5000) ∧
    -Real.log (3427 / 5000) ≤ (37775267 / 100000000) := by
  have h := checkLog_sound (w := (1573 / 8427)) (n := 12)
    (lo := (377752669 / 1000000000)) (hi := (37775267 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 3427) = 1/(3427 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37775267 / 100000000) (-377752669 / 1000000000) (Real.log (3427 / 5000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (273857197 / 1000000000) ≤ -Real.log (1000000 / 1315027) ∧
    -Real.log (1000000 / 1315027) ≤ (136928599 / 500000000) := by
  have h := checkLog_sound (w := (315027 / 2315027)) (n := 12)
    (lo := (273857197 / 1000000000)) (hi := (136928599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1315027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1315027 / 1000000) = 1/(1000000 / 1315027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (273857197 / 1000000000) (136928599 / 500000000) (Real.log (1315027 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1315027 / 1000000) = -Real.log (1000000 / 1315027) := by
    rw [show ((1315027 / 1000000) : ℝ) = ((1000000 / 1315027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (378375857 / 1000000000) ≤ -Real.log (684973 / 1000000) ∧
    -Real.log (684973 / 1000000) ≤ (189187929 / 500000000) := by
  have h := checkLog_sound (w := (315027 / 1684973)) (n := 12)
    (lo := (378375857 / 1000000000)) (hi := (189187929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 684973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 684973) = 1/(684973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-189187929 / 500000000) (-378375857 / 1000000000) (Real.log (684973 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51493651 / 250000000) ≤ -Real.log (500000 / 614361) ∧
    -Real.log (500000 / 614361) ≤ (41194921 / 200000000) := by
  have h := checkLog_sound (w := (114361 / 1114361)) (n := 12)
    (lo := (51493651 / 250000000)) (hi := (41194921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614361 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614361 / 500000) = 1/(500000 / 614361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51493651 / 250000000) (41194921 / 200000000) (Real.log (614361 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (614361 / 500000) = -Real.log (500000 / 614361) := by
    rw [show ((614361 / 500000) : ℝ) = ((500000 / 614361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (259706399 / 1000000000) ≤ -Real.log (385639 / 500000) ∧
    -Real.log (385639 / 500000) ≤ (324633 / 1250000) := by
  have h := checkLog_sound (w := (114361 / 885639)) (n := 12)
    (lo := (259706399 / 1000000000)) (hi := (324633 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 385639) = 1/(385639 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-324633 / 1250000) (-259706399 / 1000000000) (Real.log (385639 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (206241513 / 1000000000) ≤ -Real.log (20000 / 24581) ∧
    -Real.log (20000 / 24581) ≤ (103120757 / 500000000) := by
  have h := checkLog_sound (w := (4581 / 44581)) (n := 12)
    (lo := (206241513 / 1000000000)) (hi := (103120757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24581 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24581 / 20000) = 1/(20000 / 24581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (206241513 / 1000000000) (103120757 / 500000000) (Real.log (24581 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (24581 / 20000) = -Real.log (20000 / 24581) := by
    rw [show ((24581 / 20000) : ℝ) = ((20000 / 24581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (130065879 / 500000000) ≤ -Real.log (15419 / 20000) ∧
    -Real.log (15419 / 20000) ≤ (260131759 / 1000000000) := by
  have h := checkLog_sound (w := (4581 / 35419)) (n := 12)
    (lo := (130065879 / 500000000)) (hi := (260131759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15419) = 1/(15419 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-260131759 / 1000000000) (-130065879 / 500000000) (Real.log (15419 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (325642553 / 500000000) ≤ -Real.log (250000000000 / 479501021301) ∧
    -Real.log (250000000000 / 479501021301) ≤ (651285107 / 1000000000) := by
  have h := checkLog_sound (w := (229501021301 / 729501021301)) (n := 12)
    (lo := (325642553 / 500000000)) (hi := (651285107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479501021301 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479501021301 / 250000000000) = 1/(250000000000 / 479501021301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (325642553 / 500000000) (651285107 / 1000000000) (Real.log (479501021301 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (479501021301 / 250000000000) = -Real.log (250000000000 / 479501021301) := by
    rw [show ((479501021301 / 250000000000) : ℝ) = ((250000000000 / 479501021301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (130446611 / 200000000) ≤ -Real.log (250000000000 / 479955779279) ∧
    -Real.log (250000000000 / 479955779279) ≤ (20382283 / 31250000) := by
  have h := checkLog_sound (w := (229955779279 / 729955779279)) (n := 12)
    (lo := (130446611 / 200000000)) (hi := (20382283 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479955779279 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479955779279 / 250000000000) = 1/(250000000000 / 479955779279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (130446611 / 200000000) (20382283 / 31250000) (Real.log (479955779279 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (479955779279 / 250000000000) = -Real.log (250000000000 / 479955779279) := by
    rw [show ((479955779279 / 250000000000) : ℝ) = ((250000000000 / 479955779279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (116420251 / 250000000) ≤ -Real.log (500000000000 / 796549363523) ∧
    -Real.log (500000000000 / 796549363523) ≤ (93136201 / 200000000) := by
  have h := checkLog_sound (w := (296549363523 / 1296549363523)) (n := 12)
    (lo := (116420251 / 250000000)) (hi := (93136201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((796549363523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(796549363523 / 500000000000) = 1/(500000000000 / 796549363523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (116420251 / 250000000) (93136201 / 200000000) (Real.log (796549363523 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (796549363523 / 500000000000) = -Real.log (500000000000 / 796549363523) := by
    rw [show ((796549363523 / 500000000000) : ℝ) = ((500000000000 / 796549363523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (466373271 / 1000000000) ≤ -Real.log (31250000000 / 49818811207) ∧
    -Real.log (31250000000 / 49818811207) ≤ (58296659 / 125000000) := by
  have h := checkLog_sound (w := (18568811207 / 81068811207)) (n := 12)
    (lo := (466373271 / 1000000000)) (hi := (58296659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49818811207 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49818811207 / 31250000000) = 1/(31250000000 / 49818811207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (466373271 / 1000000000) (58296659 / 125000000) (Real.log (49818811207 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (49818811207 / 31250000000) = -Real.log (31250000000 / 49818811207) := by
    rw [show ((49818811207 / 31250000000) : ℝ) = ((31250000000 / 49818811207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0403

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0404Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0404
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

theorem reflection_log_1_neg : (199267011 / 1000000000) ≤ -Real.log (5120 / 6249) ∧
    -Real.log (5120 / 6249) ≤ (49816753 / 250000000) := by
  have h := checkLog_sound (w := (1129 / 11369)) (n := 12)
    (lo := (199267011 / 1000000000)) (hi := (49816753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6249 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6249 / 5120) = 1/(5120 / 6249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199267011 / 1000000000) (49816753 / 250000000) (Real.log (6249 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6249 / 5120) = -Real.log (5120 / 6249) := by
    rw [show ((6249 / 5120) : ℝ) = ((5120 / 6249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (62278153 / 250000000) ≤ -Real.log (3991 / 5120) ∧
    -Real.log (3991 / 5120) ≤ (249112613 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 9111)) (n := 12)
    (lo := (62278153 / 250000000)) (hi := (249112613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3991) = 1/(3991 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-249112613 / 1000000000) (-62278153 / 250000000) (Real.log (3991 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (777449 / 3906250) ≤ -Real.log (2048 / 2499) ∧
    -Real.log (2048 / 2499) ≤ (39805389 / 200000000) := by
  have h := checkLog_sound (w := (451 / 4547)) (n := 12)
    (lo := (777449 / 3906250)) (hi := (39805389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2499 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2499 / 2048) = 1/(2048 / 2499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (777449 / 3906250) (39805389 / 200000000) (Real.log (2499 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2499 / 2048) = -Real.log (2048 / 2499) := by
    rw [show ((2499 / 2048) : ℝ) = ((2048 / 2499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (248736837 / 1000000000) ≤ -Real.log (1597 / 2048) ∧
    -Real.log (1597 / 2048) ≤ (124368419 / 500000000) := by
  have h := checkLog_sound (w := (451 / 3645)) (n := 12)
    (lo := (248736837 / 1000000000)) (hi := (124368419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1597) = 1/(1597 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-124368419 / 500000000) (-248736837 / 1000000000) (Real.log (1597 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1141713 / 3125000) ≤ -Real.log (2560 / 3689) ∧
    -Real.log (2560 / 3689) ≤ (365348161 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 6249)) (n := 12)
    (lo := (1141713 / 3125000)) (hi := (365348161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3689 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3689 / 2560) = 1/(2560 / 3689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1141713 / 3125000) (365348161 / 1000000000) (Real.log (3689 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3689 / 2560) = -Real.log (2560 / 3689) := by
    rw [show ((3689 / 2560) : ℝ) = ((2560 / 3689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (581633757 / 1000000000) ≤ -Real.log (1431 / 2560) ∧
    -Real.log (1431 / 2560) ≤ (290816879 / 500000000) := by
  have h := checkLog_sound (w := (1129 / 3991)) (n := 12)
    (lo := (581633757 / 1000000000)) (hi := (290816879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1431) = 1/(1431 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-290816879 / 500000000) (-581633757 / 1000000000) (Real.log (1431 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (364941463 / 1000000000) ≤ -Real.log (1024 / 1475) ∧
    -Real.log (1024 / 1475) ≤ (45617683 / 125000000) := by
  have h := checkLog_sound (w := (451 / 2499)) (n := 12)
    (lo := (364941463 / 1000000000)) (hi := (45617683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1475 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1475 / 1024) = 1/(1024 / 1475) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (364941463 / 1000000000) (45617683 / 125000000) (Real.log (1475 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1475 / 1024) = -Real.log (1024 / 1475) := by
    rw [show ((1475 / 1024) : ℝ) = ((1024 / 1475) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (72573261 / 125000000) ≤ -Real.log (573 / 1024) ∧
    -Real.log (573 / 1024) ≤ (580586089 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 1597)) (n := 12)
    (lo := (72573261 / 125000000)) (hi := (580586089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 573) = 1/(573 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-580586089 / 1000000000) (-72573261 / 125000000) (Real.log (573 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (273208331 / 1000000000) ≤ -Real.log (500000 / 657087) ∧
    -Real.log (500000 / 657087) ≤ (68302083 / 250000000) := by
  have h := checkLog_sound (w := (157087 / 1157087)) (n := 12)
    (lo := (273208331 / 1000000000)) (hi := (68302083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657087 / 500000) = 1/(500000 / 657087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (273208331 / 1000000000) (68302083 / 250000000) (Real.log (657087 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (657087 / 500000) = -Real.log (500000 / 657087) := by
    rw [show ((657087 / 500000) : ℝ) = ((500000 / 657087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (377131327 / 1000000000) ≤ -Real.log (342913 / 500000) ∧
    -Real.log (342913 / 500000) ≤ (5892677 / 15625000) := by
  have h := checkLog_sound (w := (157087 / 842913)) (n := 12)
    (lo := (377131327 / 1000000000)) (hi := (5892677 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342913) = 1/(342913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5892677 / 15625000) (-377131327 / 1000000000) (Real.log (342913 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (273533197 / 1000000000) ≤ -Real.log (1000000 / 1314601) ∧
    -Real.log (1000000 / 1314601) ≤ (136766599 / 500000000) := by
  have h := checkLog_sound (w := (314601 / 2314601)) (n := 12)
    (lo := (273533197 / 1000000000)) (hi := (136766599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1314601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1314601 / 1000000) = 1/(1000000 / 1314601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (273533197 / 1000000000) (136766599 / 500000000) (Real.log (1314601 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1314601 / 1000000) = -Real.log (1000000 / 1314601) := by
    rw [show ((1314601 / 1000000) : ℝ) = ((1000000 / 1314601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (23609633 / 62500000) ≤ -Real.log (685399 / 1000000) ∧
    -Real.log (685399 / 1000000) ≤ (377754129 / 1000000000) := by
  have h := checkLog_sound (w := (314601 / 1685399)) (n := 12)
    (lo := (23609633 / 62500000)) (hi := (377754129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 685399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 685399) = 1/(685399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-377754129 / 1000000000) (-23609633 / 62500000) (Real.log (685399 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (205708439 / 1000000000) ≤ -Real.log (200000 / 245679) ∧
    -Real.log (200000 / 245679) ≤ (5142711 / 25000000) := by
  have h := checkLog_sound (w := (45679 / 445679)) (n := 12)
    (lo := (205708439 / 1000000000)) (hi := (5142711 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245679 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245679 / 200000) = 1/(200000 / 245679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (205708439 / 1000000000) (5142711 / 25000000) (Real.log (245679 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (245679 / 200000) = -Real.log (200000 / 245679) := by
    rw [show ((245679 / 200000) : ℝ) = ((200000 / 245679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (259282517 / 1000000000) ≤ -Real.log (154321 / 200000) ∧
    -Real.log (154321 / 200000) ≤ (129641259 / 500000000) := by
  have h := checkLog_sound (w := (45679 / 354321)) (n := 12)
    (lo := (259282517 / 1000000000)) (hi := (129641259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154321) = 1/(154321 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-129641259 / 500000000) (-259282517 / 1000000000) (Real.log (154321 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (102987709 / 500000000) ≤ -Real.log (1000000 / 1228723) ∧
    -Real.log (1000000 / 1228723) ≤ (205975419 / 1000000000) := by
  have h := checkLog_sound (w := (228723 / 2228723)) (n := 12)
    (lo := (102987709 / 500000000)) (hi := (205975419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228723 / 1000000) = 1/(1000000 / 1228723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102987709 / 500000000) (205975419 / 1000000000) (Real.log (1228723 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1228723 / 1000000) = -Real.log (1000000 / 1228723) := by
    rw [show ((1228723 / 1000000) : ℝ) = ((1000000 / 1228723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16231731 / 62500000) ≤ -Real.log (771277 / 1000000) ∧
    -Real.log (771277 / 1000000) ≤ (259707697 / 1000000000) := by
  have h := checkLog_sound (w := (228723 / 1771277)) (n := 12)
    (lo := (16231731 / 62500000)) (hi := (259707697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 771277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 771277) = 1/(771277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-259707697 / 1000000000) (-16231731 / 62500000) (Real.log (771277 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (650339659 / 1000000000) ≤ -Real.log (125000000000 / 239523946307) ∧
    -Real.log (125000000000 / 239523946307) ≤ (32516983 / 50000000) := by
  have h := checkLog_sound (w := (114523946307 / 364523946307)) (n := 12)
    (lo := (650339659 / 1000000000)) (hi := (32516983 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239523946307 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239523946307 / 125000000000) = 1/(125000000000 / 239523946307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (650339659 / 1000000000) (32516983 / 50000000) (Real.log (239523946307 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239523946307 / 125000000000) = -Real.log (125000000000 / 239523946307) := by
    rw [show ((239523946307 / 125000000000) : ℝ) = ((125000000000 / 239523946307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (325643663 / 500000000) ≤ -Real.log (500000000000 / 959004171293) ∧
    -Real.log (500000000000 / 959004171293) ≤ (651287327 / 1000000000) := by
  have h := checkLog_sound (w := (459004171293 / 1459004171293)) (n := 12)
    (lo := (325643663 / 500000000)) (hi := (651287327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959004171293 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959004171293 / 500000000000) = 1/(500000000000 / 959004171293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (325643663 / 500000000) (651287327 / 1000000000) (Real.log (959004171293 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (959004171293 / 500000000000) = -Real.log (500000000000 / 959004171293) := by
    rw [show ((959004171293 / 500000000000) : ℝ) = ((500000000000 / 959004171293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (464990957 / 1000000000) ≤ -Real.log (390625000 / 621874919) ∧
    -Real.log (390625000 / 621874919) ≤ (232495479 / 500000000) := by
  have h := checkLog_sound (w := (231249919 / 1012499919)) (n := 12)
    (lo := (464990957 / 1000000000)) (hi := (232495479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621874919 / 390625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621874919 / 390625000) = 1/(390625000 / 621874919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (464990957 / 1000000000) (232495479 / 500000000) (Real.log (621874919 / 390625000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (621874919 / 390625000) = -Real.log (390625000 / 621874919) := by
    rw [show ((621874919 / 390625000) : ℝ) = ((390625000 / 621874919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (232841557 / 500000000) ≤ -Real.log (500000000000 / 796551044567) ∧
    -Real.log (500000000000 / 796551044567) ≤ (93136623 / 200000000) := by
  have h := checkLog_sound (w := (296551044567 / 1296551044567)) (n := 12)
    (lo := (232841557 / 500000000)) (hi := (93136623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((796551044567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(796551044567 / 500000000000) = 1/(500000000000 / 796551044567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (232841557 / 500000000) (93136623 / 200000000) (Real.log (796551044567 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (796551044567 / 500000000000) = -Real.log (500000000000 / 796551044567) := by
    rw [show ((796551044567 / 500000000000) : ℝ) = ((500000000000 / 796551044567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0404

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0405Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0405
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

theorem reflection_log_1_neg : (777449 / 3906250) ≤ -Real.log (2048 / 2499) ∧
    -Real.log (2048 / 2499) ≤ (39805389 / 200000000) := by
  have h := checkLog_sound (w := (451 / 4547)) (n := 12)
    (lo := (777449 / 3906250)) (hi := (39805389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2499 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2499 / 2048) = 1/(2048 / 2499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (777449 / 3906250) (39805389 / 200000000) (Real.log (2499 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2499 / 2048) = -Real.log (2048 / 2499) := by
    rw [show ((2499 / 2048) : ℝ) = ((2048 / 2499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (248736837 / 1000000000) ≤ -Real.log (1597 / 2048) ∧
    -Real.log (1597 / 2048) ≤ (124368419 / 500000000) := by
  have h := checkLog_sound (w := (451 / 3645)) (n := 12)
    (lo := (248736837 / 1000000000)) (hi := (124368419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1597) = 1/(1597 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-124368419 / 500000000) (-248736837 / 1000000000) (Real.log (1597 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198786819 / 1000000000) ≤ -Real.log (2560 / 3123) ∧
    -Real.log (2560 / 3123) ≤ (9939341 / 50000000) := by
  have h := checkLog_sound (w := (563 / 5683)) (n := 12)
    (lo := (198786819 / 1000000000)) (hi := (9939341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3123 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3123 / 2560) = 1/(2560 / 3123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198786819 / 1000000000) (9939341 / 50000000) (Real.log (3123 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3123 / 2560) = -Real.log (2560 / 3123) := by
    rw [show ((3123 / 2560) : ℝ) = ((2560 / 3123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (62090301 / 250000000) ≤ -Real.log (1997 / 2560) ∧
    -Real.log (1997 / 2560) ≤ (49672241 / 200000000) := by
  have h := checkLog_sound (w := (563 / 4557)) (n := 12)
    (lo := (62090301 / 250000000)) (hi := (49672241 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1997) = 1/(1997 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-49672241 / 200000000) (-62090301 / 250000000) (Real.log (1997 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (364941463 / 1000000000) ≤ -Real.log (1024 / 1475) ∧
    -Real.log (1024 / 1475) ≤ (45617683 / 125000000) := by
  have h := checkLog_sound (w := (451 / 2499)) (n := 12)
    (lo := (364941463 / 1000000000)) (hi := (45617683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1475 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1475 / 1024) = 1/(1024 / 1475) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (364941463 / 1000000000) (45617683 / 125000000) (Real.log (1475 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1475 / 1024) = -Real.log (1024 / 1475) := by
    rw [show ((1475 / 1024) : ℝ) = ((1024 / 1475) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (72573261 / 125000000) ≤ -Real.log (573 / 1024) ∧
    -Real.log (573 / 1024) ≤ (580586089 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 1597)) (n := 12)
    (lo := (72573261 / 125000000)) (hi := (580586089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 573) = 1/(573 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-580586089 / 1000000000) (-72573261 / 125000000) (Real.log (573 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1822673 / 5000000) ≤ -Real.log (1280 / 1843) ∧
    -Real.log (1280 / 1843) ≤ (364534601 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 3123)) (n := 12)
    (lo := (1822673 / 5000000)) (hi := (364534601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1843 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1843 / 1280) = 1/(1280 / 1843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1822673 / 5000000) (364534601 / 1000000000) (Real.log (1843 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1843 / 1280) = -Real.log (1280 / 1843) := by
    rw [show ((1843 / 1280) : ℝ) = ((1280 / 1843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (144884879 / 250000000) ≤ -Real.log (717 / 1280) ∧
    -Real.log (717 / 1280) ≤ (579539517 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 1997)) (n := 12)
    (lo := (144884879 / 250000000)) (hi := (579539517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 717) = 1/(717 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-579539517 / 1000000000) (-144884879 / 250000000) (Real.log (717 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6822103 / 25000000) ≤ -Real.log (250000 / 328437) ∧
    -Real.log (250000 / 328437) ≤ (272884121 / 1000000000) := by
  have h := checkLog_sound (w := (78437 / 578437)) (n := 12)
    (lo := (6822103 / 25000000)) (hi := (272884121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328437 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328437 / 250000) = 1/(250000 / 328437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6822103 / 25000000) (272884121 / 1000000000) (Real.log (328437 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (328437 / 250000) = -Real.log (250000 / 328437) := by
    rw [show ((328437 / 250000) : ℝ) = ((250000 / 328437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (376510371 / 1000000000) ≤ -Real.log (171563 / 250000) ∧
    -Real.log (171563 / 250000) ≤ (94127593 / 250000000) := by
  have h := checkLog_sound (w := (78437 / 421563)) (n := 12)
    (lo := (376510371 / 1000000000)) (hi := (94127593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171563) = 1/(171563 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-94127593 / 250000000) (-376510371 / 1000000000) (Real.log (171563 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68302273 / 250000000) ≤ -Real.log (40000 / 52567) ∧
    -Real.log (40000 / 52567) ≤ (273209093 / 1000000000) := by
  have h := checkLog_sound (w := (12567 / 92567)) (n := 12)
    (lo := (68302273 / 250000000)) (hi := (273209093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52567 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52567 / 40000) = 1/(40000 / 52567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68302273 / 250000000) (273209093 / 1000000000) (Real.log (52567 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (52567 / 40000) = -Real.log (40000 / 52567) := by
    rw [show ((52567 / 40000) : ℝ) = ((40000 / 52567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (75426557 / 200000000) ≤ -Real.log (27433 / 40000) ∧
    -Real.log (27433 / 40000) ≤ (188566393 / 500000000) := by
  have h := checkLog_sound (w := (12567 / 67433)) (n := 12)
    (lo := (75426557 / 200000000)) (hi := (188566393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 27433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 27433) = 1/(27433 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-188566393 / 500000000) (-75426557 / 200000000) (Real.log (27433 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102721101 / 500000000) ≤ -Real.log (250000 / 307017) ∧
    -Real.log (250000 / 307017) ≤ (205442203 / 1000000000) := by
  have h := checkLog_sound (w := (57017 / 557017)) (n := 12)
    (lo := (102721101 / 500000000)) (hi := (205442203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307017 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307017 / 250000) = 1/(250000 / 307017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102721101 / 500000000) (205442203 / 1000000000) (Real.log (307017 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (307017 / 250000) = -Real.log (250000 / 307017) := by
    rw [show ((307017 / 250000) : ℝ) = ((250000 / 307017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (51771763 / 200000000) ≤ -Real.log (192983 / 250000) ∧
    -Real.log (192983 / 250000) ≤ (4044669 / 15625000) := by
  have h := checkLog_sound (w := (57017 / 442983)) (n := 12)
    (lo := (51771763 / 200000000)) (hi := (4044669 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192983) = 1/(192983 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4044669 / 15625000) (-51771763 / 200000000) (Real.log (192983 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (205709253 / 1000000000) ≤ -Real.log (250000 / 307099) ∧
    -Real.log (250000 / 307099) ≤ (102854627 / 500000000) := by
  have h := checkLog_sound (w := (57099 / 557099)) (n := 12)
    (lo := (205709253 / 1000000000)) (hi := (102854627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307099 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307099 / 250000) = 1/(250000 / 307099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (205709253 / 1000000000) (102854627 / 500000000) (Real.log (307099 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (307099 / 250000) = -Real.log (250000 / 307099) := by
    rw [show ((307099 / 250000) : ℝ) = ((250000 / 307099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (259283813 / 1000000000) ≤ -Real.log (192901 / 250000) ∧
    -Real.log (192901 / 250000) ≤ (129641907 / 500000000) := by
  have h := checkLog_sound (w := (57099 / 442901)) (n := 12)
    (lo := (259283813 / 1000000000)) (hi := (129641907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192901) = 1/(192901 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-129641907 / 500000000) (-259283813 / 1000000000) (Real.log (192901 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (162348623 / 250000000) ≤ -Real.log (125000000000 / 239297663249) ∧
    -Real.log (125000000000 / 239297663249) ≤ (649394493 / 1000000000) := by
  have h := checkLog_sound (w := (114297663249 / 364297663249)) (n := 12)
    (lo := (162348623 / 250000000)) (hi := (649394493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239297663249 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239297663249 / 125000000000) = 1/(125000000000 / 239297663249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (162348623 / 250000000) (649394493 / 1000000000) (Real.log (239297663249 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239297663249 / 125000000000) = -Real.log (125000000000 / 239297663249) := by
    rw [show ((239297663249 / 125000000000) : ℝ) = ((125000000000 / 239297663249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (325170939 / 500000000) ≤ -Real.log (20000000000 / 38323916451) ∧
    -Real.log (20000000000 / 38323916451) ≤ (650341879 / 1000000000) := by
  have h := checkLog_sound (w := (18323916451 / 58323916451)) (n := 12)
    (lo := (325170939 / 500000000)) (hi := (650341879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38323916451 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38323916451 / 20000000000) = 1/(20000000000 / 38323916451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (325170939 / 500000000) (650341879 / 1000000000) (Real.log (38323916451 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (38323916451 / 20000000000) = -Real.log (20000000000 / 38323916451) := by
    rw [show ((38323916451 / 20000000000) : ℝ) = ((20000000000 / 38323916451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (232150509 / 500000000) ≤ -Real.log (250000000000 / 397725447319) ∧
    -Real.log (250000000000 / 397725447319) ≤ (464301019 / 1000000000) := by
  have h := checkLog_sound (w := (147725447319 / 647725447319)) (n := 12)
    (lo := (232150509 / 500000000)) (hi := (464301019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397725447319 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397725447319 / 250000000000) = 1/(250000000000 / 397725447319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (232150509 / 500000000) (464301019 / 1000000000) (Real.log (397725447319 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (397725447319 / 250000000000) = -Real.log (250000000000 / 397725447319) := by
    rw [show ((397725447319 / 250000000000) : ℝ) = ((250000000000 / 397725447319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (464993067 / 1000000000) ≤ -Real.log (250000000000 / 398000787969) ∧
    -Real.log (250000000000 / 398000787969) ≤ (116248267 / 250000000) := by
  have h := checkLog_sound (w := (148000787969 / 648000787969)) (n := 12)
    (lo := (464993067 / 1000000000)) (hi := (116248267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398000787969 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398000787969 / 250000000000) = 1/(250000000000 / 398000787969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (464993067 / 1000000000) (116248267 / 250000000) (Real.log (398000787969 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (398000787969 / 250000000000) = -Real.log (250000000000 / 398000787969) := by
    rw [show ((398000787969 / 250000000000) : ℝ) = ((250000000000 / 398000787969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0405

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0406Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0406
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

theorem reflection_log_1_neg : (198786819 / 1000000000) ≤ -Real.log (2560 / 3123) ∧
    -Real.log (2560 / 3123) ≤ (9939341 / 50000000) := by
  have h := checkLog_sound (w := (563 / 5683)) (n := 12)
    (lo := (198786819 / 1000000000)) (hi := (9939341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3123 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3123 / 2560) = 1/(2560 / 3123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198786819 / 1000000000) (9939341 / 50000000) (Real.log (3123 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3123 / 2560) = -Real.log (2560 / 3123) := by
    rw [show ((3123 / 2560) : ℝ) = ((2560 / 3123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (62090301 / 250000000) ≤ -Real.log (1997 / 2560) ∧
    -Real.log (1997 / 2560) ≤ (49672241 / 200000000) := by
  have h := checkLog_sound (w := (563 / 4557)) (n := 12)
    (lo := (62090301 / 250000000)) (hi := (49672241 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1997) = 1/(1997 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-49672241 / 200000000) (-62090301 / 250000000) (Real.log (1997 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198546637 / 1000000000) ≤ -Real.log (10240 / 12489) ∧
    -Real.log (10240 / 12489) ≤ (99273319 / 500000000) := by
  have h := checkLog_sound (w := (2249 / 22729)) (n := 12)
    (lo := (198546637 / 1000000000)) (hi := (99273319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12489 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12489 / 10240) = 1/(10240 / 12489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198546637 / 1000000000) (99273319 / 500000000) (Real.log (12489 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12489 / 10240) = -Real.log (10240 / 12489) := by
    rw [show ((12489 / 10240) : ℝ) = ((10240 / 12489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (247985711 / 1000000000) ≤ -Real.log (7991 / 10240) ∧
    -Real.log (7991 / 10240) ≤ (15499107 / 62500000) := by
  have h := checkLog_sound (w := (2249 / 18231)) (n := 12)
    (lo := (247985711 / 1000000000)) (hi := (15499107 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7991) = 1/(7991 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-15499107 / 62500000) (-247985711 / 1000000000) (Real.log (7991 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1822673 / 5000000) ≤ -Real.log (1280 / 1843) ∧
    -Real.log (1280 / 1843) ≤ (364534601 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 3123)) (n := 12)
    (lo := (1822673 / 5000000)) (hi := (364534601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1843 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1843 / 1280) = 1/(1280 / 1843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1822673 / 5000000) (364534601 / 1000000000) (Real.log (1843 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1843 / 1280) = -Real.log (1280 / 1843) := by
    rw [show ((1843 / 1280) : ℝ) = ((1280 / 1843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (144884879 / 250000000) ≤ -Real.log (717 / 1280) ∧
    -Real.log (717 / 1280) ≤ (579539517 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 1997)) (n := 12)
    (lo := (144884879 / 250000000)) (hi := (579539517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 717) = 1/(717 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-579539517 / 1000000000) (-144884879 / 250000000) (Real.log (717 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (91031893 / 250000000) ≤ -Real.log (5120 / 7369) ∧
    -Real.log (5120 / 7369) ≤ (364127573 / 1000000000) := by
  have h := checkLog_sound (w := (2249 / 12489)) (n := 12)
    (lo := (91031893 / 250000000)) (hi := (364127573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7369 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7369 / 5120) = 1/(5120 / 7369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (91031893 / 250000000) (364127573 / 1000000000) (Real.log (7369 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7369 / 5120) = -Real.log (5120 / 7369) := by
    rw [show ((7369 / 5120) : ℝ) = ((5120 / 7369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (578494037 / 1000000000) ≤ -Real.log (2871 / 5120) ∧
    -Real.log (2871 / 5120) ≤ (289247019 / 500000000) := by
  have h := checkLog_sound (w := (2249 / 7991)) (n := 12)
    (lo := (578494037 / 1000000000)) (hi := (289247019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2871) = 1/(2871 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-289247019 / 500000000) (-578494037 / 1000000000) (Real.log (2871 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (54511961 / 200000000) ≤ -Real.log (500000 / 656661) ∧
    -Real.log (500000 / 656661) ≤ (136279903 / 500000000) := by
  have h := checkLog_sound (w := (156661 / 1156661)) (n := 12)
    (lo := (54511961 / 200000000)) (hi := (136279903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656661 / 500000) = 1/(500000 / 656661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (54511961 / 200000000) (136279903 / 500000000) (Real.log (656661 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (656661 / 500000) = -Real.log (500000 / 656661) := by
    rw [show ((656661 / 500000) : ℝ) = ((500000 / 656661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (375889801 / 1000000000) ≤ -Real.log (343339 / 500000) ∧
    -Real.log (343339 / 500000) ≤ (187944901 / 500000000) := by
  have h := checkLog_sound (w := (156661 / 843339)) (n := 12)
    (lo := (375889801 / 1000000000)) (hi := (187944901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 343339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 343339) = 1/(343339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-187944901 / 500000000) (-375889801 / 1000000000) (Real.log (343339 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136442441 / 500000000) ≤ -Real.log (1000000 / 1313749) ∧
    -Real.log (1000000 / 1313749) ≤ (272884883 / 1000000000) := by
  have h := checkLog_sound (w := (313749 / 2313749)) (n := 12)
    (lo := (136442441 / 500000000)) (hi := (272884883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313749 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313749 / 1000000) = 1/(1000000 / 1313749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136442441 / 500000000) (272884883 / 1000000000) (Real.log (1313749 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1313749 / 1000000) = -Real.log (1000000 / 1313749) := by
    rw [show ((1313749 / 1000000) : ℝ) = ((1000000 / 1313749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (94127957 / 250000000) ≤ -Real.log (686251 / 1000000) ∧
    -Real.log (686251 / 1000000) ≤ (376511829 / 1000000000) := by
  have h := checkLog_sound (w := (313749 / 1686251)) (n := 12)
    (lo := (94127957 / 250000000)) (hi := (376511829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 686251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 686251) = 1/(686251 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-376511829 / 1000000000) (-94127957 / 250000000) (Real.log (686251 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (41035179 / 200000000) ≤ -Real.log (1000000 / 1227741) ∧
    -Real.log (1000000 / 1227741) ≤ (25646987 / 125000000) := by
  have h := checkLog_sound (w := (227741 / 2227741)) (n := 12)
    (lo := (41035179 / 200000000)) (hi := (25646987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227741 / 1000000) = 1/(1000000 / 1227741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (41035179 / 200000000) (25646987 / 125000000) (Real.log (1227741 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1227741 / 1000000) = -Real.log (1000000 / 1227741) := by
    rw [show ((1227741 / 1000000) : ℝ) = ((1000000 / 1227741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (64608823 / 250000000) ≤ -Real.log (772259 / 1000000) ∧
    -Real.log (772259 / 1000000) ≤ (258435293 / 1000000000) := by
  have h := checkLog_sound (w := (227741 / 1772259)) (n := 12)
    (lo := (64608823 / 250000000)) (hi := (258435293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772259) = 1/(772259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-258435293 / 1000000000) (-64608823 / 250000000) (Real.log (772259 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (205443017 / 1000000000) ≤ -Real.log (1000000 / 1228069) ∧
    -Real.log (1000000 / 1228069) ≤ (102721509 / 500000000) := by
  have h := checkLog_sound (w := (228069 / 2228069)) (n := 12)
    (lo := (205443017 / 1000000000)) (hi := (102721509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228069 / 1000000) = 1/(1000000 / 1228069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (205443017 / 1000000000) (102721509 / 500000000) (Real.log (1228069 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1228069 / 1000000) = -Real.log (1000000 / 1228069) := by
    rw [show ((1228069 / 1000000) : ℝ) = ((1000000 / 1228069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (258860111 / 1000000000) ≤ -Real.log (771931 / 1000000) ∧
    -Real.log (771931 / 1000000) ≤ (16178757 / 62500000) := by
  have h := checkLog_sound (w := (228069 / 1771931)) (n := 12)
    (lo := (258860111 / 1000000000)) (hi := (16178757 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 771931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 771931) = 1/(771931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-16178757 / 62500000) (-258860111 / 1000000000) (Real.log (771931 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (324224803 / 500000000) ≤ -Real.log (125000000000 / 239071660953) ∧
    -Real.log (125000000000 / 239071660953) ≤ (648449607 / 1000000000) := by
  have h := checkLog_sound (w := (114071660953 / 364071660953)) (n := 12)
    (lo := (324224803 / 500000000)) (hi := (648449607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239071660953 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239071660953 / 125000000000) = 1/(125000000000 / 239071660953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (324224803 / 500000000) (648449607 / 1000000000) (Real.log (239071660953 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239071660953 / 125000000000) = -Real.log (125000000000 / 239071660953) := by
    rw [show ((239071660953 / 125000000000) : ℝ) = ((125000000000 / 239071660953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (64939671 / 100000000) ≤ -Real.log (125000000000 / 239298194101) ∧
    -Real.log (125000000000 / 239298194101) ≤ (649396711 / 1000000000) := by
  have h := checkLog_sound (w := (114298194101 / 364298194101)) (n := 12)
    (lo := (64939671 / 100000000)) (hi := (649396711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239298194101 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239298194101 / 125000000000) = 1/(125000000000 / 239298194101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (64939671 / 100000000) (649396711 / 1000000000) (Real.log (239298194101 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (239298194101 / 125000000000) = -Real.log (125000000000 / 239298194101) := by
    rw [show ((239298194101 / 125000000000) : ℝ) = ((125000000000 / 239298194101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (115902797 / 250000000) ≤ -Real.log (500000000000 / 794902357887) ∧
    -Real.log (500000000000 / 794902357887) ≤ (463611189 / 1000000000) := by
  have h := checkLog_sound (w := (294902357887 / 1294902357887)) (n := 12)
    (lo := (115902797 / 250000000)) (hi := (463611189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794902357887 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794902357887 / 500000000000) = 1/(500000000000 / 794902357887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (115902797 / 250000000) (463611189 / 1000000000) (Real.log (794902357887 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (794902357887 / 500000000000) = -Real.log (500000000000 / 794902357887) := by
    rw [show ((794902357887 / 500000000000) : ℝ) = ((500000000000 / 794902357887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (58037891 / 125000000) ≤ -Real.log (250000000000 / 397726286417) ∧
    -Real.log (250000000000 / 397726286417) ≤ (464303129 / 1000000000) := by
  have h := checkLog_sound (w := (147726286417 / 647726286417)) (n := 12)
    (lo := (58037891 / 125000000)) (hi := (464303129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397726286417 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397726286417 / 250000000000) = 1/(250000000000 / 397726286417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (58037891 / 125000000) (464303129 / 1000000000) (Real.log (397726286417 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (397726286417 / 250000000000) = -Real.log (250000000000 / 397726286417) := by
    rw [show ((397726286417 / 250000000000) : ℝ) = ((250000000000 / 397726286417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0406

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0407Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0407
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

theorem reflection_log_1_neg : (198546637 / 1000000000) ≤ -Real.log (10240 / 12489) ∧
    -Real.log (10240 / 12489) ≤ (99273319 / 500000000) := by
  have h := checkLog_sound (w := (2249 / 22729)) (n := 12)
    (lo := (198546637 / 1000000000)) (hi := (99273319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12489 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12489 / 10240) = 1/(10240 / 12489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198546637 / 1000000000) (99273319 / 500000000) (Real.log (12489 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12489 / 10240) = -Real.log (10240 / 12489) := by
    rw [show ((12489 / 10240) : ℝ) = ((10240 / 12489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (247985711 / 1000000000) ≤ -Real.log (7991 / 10240) ∧
    -Real.log (7991 / 10240) ≤ (15499107 / 62500000) := by
  have h := checkLog_sound (w := (2249 / 18231)) (n := 12)
    (lo := (247985711 / 1000000000)) (hi := (15499107 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7991) = 1/(7991 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-15499107 / 62500000) (-247985711 / 1000000000) (Real.log (7991 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198306397 / 1000000000) ≤ -Real.log (5120 / 6243) ∧
    -Real.log (5120 / 6243) ≤ (99153199 / 500000000) := by
  have h := checkLog_sound (w := (1123 / 11363)) (n := 12)
    (lo := (198306397 / 1000000000)) (hi := (99153199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6243 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6243 / 5120) = 1/(5120 / 6243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198306397 / 1000000000) (99153199 / 500000000) (Real.log (6243 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6243 / 5120) = -Real.log (5120 / 6243) := by
    rw [show ((6243 / 5120) : ℝ) = ((5120 / 6243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (247610359 / 1000000000) ≤ -Real.log (3997 / 5120) ∧
    -Real.log (3997 / 5120) ≤ (6190259 / 25000000) := by
  have h := checkLog_sound (w := (1123 / 9117)) (n := 12)
    (lo := (247610359 / 1000000000)) (hi := (6190259 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3997) = 1/(3997 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6190259 / 25000000) (-247610359 / 1000000000) (Real.log (3997 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (91031893 / 250000000) ≤ -Real.log (5120 / 7369) ∧
    -Real.log (5120 / 7369) ≤ (364127573 / 1000000000) := by
  have h := checkLog_sound (w := (2249 / 12489)) (n := 12)
    (lo := (91031893 / 250000000)) (hi := (364127573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7369 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7369 / 5120) = 1/(5120 / 7369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (91031893 / 250000000) (364127573 / 1000000000) (Real.log (7369 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7369 / 5120) = -Real.log (5120 / 7369) := by
    rw [show ((7369 / 5120) : ℝ) = ((5120 / 7369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (578494037 / 1000000000) ≤ -Real.log (2871 / 5120) ∧
    -Real.log (2871 / 5120) ≤ (289247019 / 500000000) := by
  have h := checkLog_sound (w := (2249 / 7991)) (n := 12)
    (lo := (578494037 / 1000000000)) (hi := (289247019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2871) = 1/(2871 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-289247019 / 500000000) (-578494037 / 1000000000) (Real.log (2871 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (181860189 / 500000000) ≤ -Real.log (2560 / 3683) ∧
    -Real.log (2560 / 3683) ≤ (363720379 / 1000000000) := by
  have h := checkLog_sound (w := (1123 / 6243)) (n := 12)
    (lo := (181860189 / 500000000)) (hi := (363720379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3683 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3683 / 2560) = 1/(2560 / 3683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (181860189 / 500000000) (363720379 / 1000000000) (Real.log (3683 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3683 / 2560) = -Real.log (2560 / 3683) := by
    rw [show ((3683 / 2560) : ℝ) = ((2560 / 3683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (577449651 / 1000000000) ≤ -Real.log (1437 / 2560) ∧
    -Real.log (1437 / 2560) ≤ (144362413 / 250000000) := by
  have h := checkLog_sound (w := (1123 / 3997)) (n := 12)
    (lo := (577449651 / 1000000000)) (hi := (144362413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1437) = 1/(1437 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-144362413 / 250000000) (-577449651 / 1000000000) (Real.log (1437 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (34029423 / 125000000) ≤ -Real.log (15625 / 20514) ∧
    -Real.log (15625 / 20514) ≤ (54447077 / 200000000) := by
  have h := checkLog_sound (w := (4889 / 36139)) (n := 12)
    (lo := (34029423 / 125000000)) (hi := (54447077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20514 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20514 / 15625) = 1/(15625 / 20514) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (34029423 / 125000000) (54447077 / 200000000) (Real.log (20514 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (20514 / 15625) = -Real.log (15625 / 20514) := by
    rw [show ((20514 / 15625) : ℝ) = ((15625 / 20514) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (75053923 / 200000000) ≤ -Real.log (10736 / 15625) ∧
    -Real.log (10736 / 15625) ≤ (23454351 / 62500000) := by
  have h := checkLog_sound (w := (4889 / 26361)) (n := 12)
    (lo := (75053923 / 200000000)) (hi := (23454351 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10736) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10736) = 1/(10736 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23454351 / 62500000) (-75053923 / 200000000) (Real.log (10736 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136280283 / 500000000) ≤ -Real.log (1000000 / 1313323) ∧
    -Real.log (1000000 / 1313323) ≤ (272560567 / 1000000000) := by
  have h := checkLog_sound (w := (313323 / 2313323)) (n := 12)
    (lo := (136280283 / 500000000)) (hi := (272560567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313323 / 1000000) = 1/(1000000 / 1313323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136280283 / 500000000) (272560567 / 1000000000) (Real.log (1313323 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1313323 / 1000000) = -Real.log (1000000 / 1313323) := by
    rw [show ((1313323 / 1000000) : ℝ) = ((1000000 / 1313323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (375891257 / 1000000000) ≤ -Real.log (686677 / 1000000) ∧
    -Real.log (686677 / 1000000) ≤ (187945629 / 500000000) := by
  have h := checkLog_sound (w := (313323 / 1686677)) (n := 12)
    (lo := (375891257 / 1000000000)) (hi := (187945629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 686677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 686677) = 1/(686677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-187945629 / 500000000) (-375891257 / 1000000000) (Real.log (686677 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (204909517 / 1000000000) ≤ -Real.log (500000 / 613707) ∧
    -Real.log (500000 / 613707) ≤ (102454759 / 500000000) := by
  have h := checkLog_sound (w := (113707 / 1113707)) (n := 12)
    (lo := (204909517 / 1000000000)) (hi := (102454759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613707 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613707 / 500000) = 1/(500000 / 613707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (204909517 / 1000000000) (102454759 / 500000000) (Real.log (613707 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (613707 / 500000) = -Real.log (500000 / 613707) := by
    rw [show ((613707 / 500000) : ℝ) = ((500000 / 613707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (258011949 / 1000000000) ≤ -Real.log (386293 / 500000) ∧
    -Real.log (386293 / 500000) ≤ (5160239 / 20000000) := by
  have h := checkLog_sound (w := (113707 / 886293)) (n := 12)
    (lo := (258011949 / 1000000000)) (hi := (5160239 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386293) = 1/(386293 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5160239 / 20000000) (-258011949 / 1000000000) (Real.log (386293 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (205176709 / 1000000000) ≤ -Real.log (500000 / 613871) ∧
    -Real.log (500000 / 613871) ≤ (20517671 / 100000000) := by
  have h := checkLog_sound (w := (113871 / 1113871)) (n := 12)
    (lo := (205176709 / 1000000000)) (hi := (20517671 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613871 / 500000) = 1/(500000 / 613871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (205176709 / 1000000000) (20517671 / 100000000) (Real.log (613871 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (613871 / 500000) = -Real.log (500000 / 613871) := by
    rw [show ((613871 / 500000) : ℝ) = ((500000 / 613871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (258436587 / 1000000000) ≤ -Real.log (386129 / 500000) ∧
    -Real.log (386129 / 500000) ≤ (64609147 / 250000000) := by
  have h := checkLog_sound (w := (113871 / 886129)) (n := 12)
    (lo := (258436587 / 1000000000)) (hi := (64609147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386129) = 1/(386129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-64609147 / 250000000) (-258436587 / 1000000000) (Real.log (386129 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (647504999 / 1000000000) ≤ -Real.log (125000000000 / 238845938897) ∧
    -Real.log (125000000000 / 238845938897) ≤ (129501 / 200000) := by
  have h := checkLog_sound (w := (113845938897 / 363845938897)) (n := 12)
    (lo := (647504999 / 1000000000)) (hi := (129501 / 200000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238845938897 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238845938897 / 125000000000) = 1/(125000000000 / 238845938897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (647504999 / 1000000000) (129501 / 200000) (Real.log (238845938897 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (238845938897 / 125000000000) = -Real.log (125000000000 / 238845938897) := by
    rw [show ((238845938897 / 125000000000) : ℝ) = ((125000000000 / 238845938897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (40528239 / 62500000) ≤ -Real.log (500000000000 / 956288764587) ∧
    -Real.log (500000000000 / 956288764587) ≤ (25938073 / 40000000) := by
  have h := checkLog_sound (w := (456288764587 / 1456288764587)) (n := 12)
    (lo := (40528239 / 62500000)) (hi := (25938073 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956288764587 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956288764587 / 500000000000) = 1/(500000000000 / 956288764587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (40528239 / 62500000) (25938073 / 40000000) (Real.log (956288764587 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (956288764587 / 500000000000) = -Real.log (500000000000 / 956288764587) := by
    rw [show ((956288764587 / 500000000000) : ℝ) = ((500000000000 / 956288764587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (231460733 / 500000000) ≤ -Real.log (500000000000 / 794354285477) ∧
    -Real.log (500000000000 / 794354285477) ≤ (462921467 / 1000000000) := by
  have h := checkLog_sound (w := (294354285477 / 1294354285477)) (n := 12)
    (lo := (231460733 / 500000000)) (hi := (462921467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794354285477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794354285477 / 500000000000) = 1/(500000000000 / 794354285477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (231460733 / 500000000) (462921467 / 1000000000) (Real.log (794354285477 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (794354285477 / 500000000000) = -Real.log (500000000000 / 794354285477) := by
    rw [show ((794354285477 / 500000000000) : ℝ) = ((500000000000 / 794354285477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (463613297 / 1000000000) ≤ -Real.log (250000000000 / 397452017331) ∧
    -Real.log (250000000000 / 397452017331) ≤ (231806649 / 500000000) := by
  have h := checkLog_sound (w := (147452017331 / 647452017331)) (n := 12)
    (lo := (463613297 / 1000000000)) (hi := (231806649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397452017331 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397452017331 / 250000000000) = 1/(250000000000 / 397452017331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (463613297 / 1000000000) (231806649 / 500000000) (Real.log (397452017331 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (397452017331 / 250000000000) = -Real.log (250000000000 / 397452017331) := by
    rw [show ((397452017331 / 250000000000) : ℝ) = ((250000000000 / 397452017331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0407

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0408Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0408
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

theorem reflection_log_1_neg : (198306397 / 1000000000) ≤ -Real.log (5120 / 6243) ∧
    -Real.log (5120 / 6243) ≤ (99153199 / 500000000) := by
  have h := checkLog_sound (w := (1123 / 11363)) (n := 12)
    (lo := (198306397 / 1000000000)) (hi := (99153199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6243 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6243 / 5120) = 1/(5120 / 6243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198306397 / 1000000000) (99153199 / 500000000) (Real.log (6243 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6243 / 5120) = -Real.log (5120 / 6243) := by
    rw [show ((6243 / 5120) : ℝ) = ((5120 / 6243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (247610359 / 1000000000) ≤ -Real.log (3997 / 5120) ∧
    -Real.log (3997 / 5120) ≤ (6190259 / 25000000) := by
  have h := checkLog_sound (w := (1123 / 9117)) (n := 12)
    (lo := (247610359 / 1000000000)) (hi := (6190259 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3997) = 1/(3997 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6190259 / 25000000) (-247610359 / 1000000000) (Real.log (3997 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198066099 / 1000000000) ≤ -Real.log (10240 / 12483) ∧
    -Real.log (10240 / 12483) ≤ (1980661 / 10000000) := by
  have h := checkLog_sound (w := (2243 / 22723)) (n := 12)
    (lo := (198066099 / 1000000000)) (hi := (1980661 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12483 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12483 / 10240) = 1/(10240 / 12483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198066099 / 1000000000) (1980661 / 10000000) (Real.log (12483 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12483 / 10240) = -Real.log (10240 / 12483) := by
    rw [show ((12483 / 10240) : ℝ) = ((10240 / 12483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (61808787 / 250000000) ≤ -Real.log (7997 / 10240) ∧
    -Real.log (7997 / 10240) ≤ (247235149 / 1000000000) := by
  have h := checkLog_sound (w := (2243 / 18237)) (n := 12)
    (lo := (61808787 / 250000000)) (hi := (247235149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7997) = 1/(7997 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-247235149 / 1000000000) (-61808787 / 250000000) (Real.log (7997 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (181860189 / 500000000) ≤ -Real.log (2560 / 3683) ∧
    -Real.log (2560 / 3683) ≤ (363720379 / 1000000000) := by
  have h := checkLog_sound (w := (1123 / 6243)) (n := 12)
    (lo := (181860189 / 500000000)) (hi := (363720379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3683 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3683 / 2560) = 1/(2560 / 3683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (181860189 / 500000000) (363720379 / 1000000000) (Real.log (3683 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3683 / 2560) = -Real.log (2560 / 3683) := by
    rw [show ((3683 / 2560) : ℝ) = ((2560 / 3683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (577449651 / 1000000000) ≤ -Real.log (1437 / 2560) ∧
    -Real.log (1437 / 2560) ≤ (144362413 / 250000000) := by
  have h := checkLog_sound (w := (1123 / 3997)) (n := 12)
    (lo := (577449651 / 1000000000)) (hi := (144362413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1437) = 1/(1437 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-144362413 / 250000000) (-577449651 / 1000000000) (Real.log (1437 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (363313019 / 1000000000) ≤ -Real.log (5120 / 7363) ∧
    -Real.log (5120 / 7363) ≤ (18165651 / 50000000) := by
  have h := checkLog_sound (w := (2243 / 12483)) (n := 12)
    (lo := (363313019 / 1000000000)) (hi := (18165651 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7363 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7363 / 5120) = 1/(5120 / 7363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (363313019 / 1000000000) (18165651 / 50000000) (Real.log (7363 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7363 / 5120) = -Real.log (5120 / 7363) := by
    rw [show ((7363 / 5120) : ℝ) = ((5120 / 7363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (288203177 / 500000000) ≤ -Real.log (2877 / 5120) ∧
    -Real.log (2877 / 5120) ≤ (115281271 / 200000000) := by
  have h := checkLog_sound (w := (2243 / 7997)) (n := 12)
    (lo := (288203177 / 500000000)) (hi := (115281271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2877) = 1/(2877 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115281271 / 200000000) (-288203177 / 500000000) (Real.log (2877 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135955429 / 500000000) ≤ -Real.log (100000 / 131247) ∧
    -Real.log (100000 / 131247) ≤ (271910859 / 1000000000) := by
  have h := checkLog_sound (w := (31247 / 231247)) (n := 12)
    (lo := (135955429 / 500000000)) (hi := (271910859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131247 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131247 / 100000) = 1/(100000 / 131247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135955429 / 500000000) (271910859 / 1000000000) (Real.log (131247 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (131247 / 100000) = -Real.log (100000 / 131247) := by
    rw [show ((131247 / 100000) : ℝ) = ((100000 / 131247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (187324907 / 500000000) ≤ -Real.log (68753 / 100000) ∧
    -Real.log (68753 / 100000) ≤ (74929963 / 200000000) := by
  have h := checkLog_sound (w := (31247 / 168753)) (n := 12)
    (lo := (187324907 / 500000000)) (hi := (74929963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 68753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 68753) = 1/(68753 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-74929963 / 200000000) (-187324907 / 500000000) (Real.log (68753 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (54447229 / 200000000) ≤ -Real.log (1000000 / 1312897) ∧
    -Real.log (1000000 / 1312897) ≤ (136118073 / 500000000) := by
  have h := checkLog_sound (w := (312897 / 2312897)) (n := 12)
    (lo := (54447229 / 200000000)) (hi := (136118073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1312897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1312897 / 1000000) = 1/(1000000 / 1312897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (54447229 / 200000000) (136118073 / 500000000) (Real.log (1312897 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1312897 / 1000000) = -Real.log (1000000 / 1312897) := by
    rw [show ((1312897 / 1000000) : ℝ) = ((1000000 / 1312897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (37527107 / 100000000) ≤ -Real.log (687103 / 1000000) ∧
    -Real.log (687103 / 1000000) ≤ (375271071 / 1000000000) := by
  have h := checkLog_sound (w := (312897 / 1687103)) (n := 12)
    (lo := (37527107 / 100000000)) (hi := (375271071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 687103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 687103) = 1/(687103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-375271071 / 1000000000) (-37527107 / 100000000) (Real.log (687103 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102321941 / 500000000) ≤ -Real.log (62500 / 76693) ∧
    -Real.log (62500 / 76693) ≤ (204643883 / 1000000000) := by
  have h := checkLog_sound (w := (14193 / 139193)) (n := 12)
    (lo := (102321941 / 500000000)) (hi := (204643883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76693 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76693 / 62500) = 1/(62500 / 76693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102321941 / 500000000) (204643883 / 1000000000) (Real.log (76693 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (76693 / 62500) = -Real.log (62500 / 76693) := by
    rw [show ((76693 / 62500) : ℝ) = ((62500 / 76693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (257590079 / 1000000000) ≤ -Real.log (48307 / 62500) ∧
    -Real.log (48307 / 62500) ≤ (804969 / 3125000) := by
  have h := checkLog_sound (w := (14193 / 110807)) (n := 12)
    (lo := (257590079 / 1000000000)) (hi := (804969 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48307) = 1/(48307 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-804969 / 3125000) (-257590079 / 1000000000) (Real.log (48307 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (204910331 / 1000000000) ≤ -Real.log (200000 / 245483) ∧
    -Real.log (200000 / 245483) ≤ (51227583 / 250000000) := by
  have h := checkLog_sound (w := (45483 / 445483)) (n := 12)
    (lo := (204910331 / 1000000000)) (hi := (51227583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245483 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245483 / 200000) = 1/(200000 / 245483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204910331 / 1000000000) (51227583 / 250000000) (Real.log (245483 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (245483 / 200000) = -Real.log (200000 / 245483) := by
    rw [show ((245483 / 200000) : ℝ) = ((200000 / 245483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (258013243 / 1000000000) ≤ -Real.log (154517 / 200000) ∧
    -Real.log (154517 / 200000) ≤ (64503311 / 250000000) := by
  have h := checkLog_sound (w := (45483 / 354517)) (n := 12)
    (lo := (258013243 / 1000000000)) (hi := (64503311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154517) = 1/(154517 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-64503311 / 250000000) (-258013243 / 1000000000) (Real.log (154517 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (20205021 / 31250000) ≤ -Real.log (1562500000 / 2982756207) ∧
    -Real.log (1562500000 / 2982756207) ≤ (646560673 / 1000000000) := by
  have h := checkLog_sound (w := (1420256207 / 4545256207)) (n := 12)
    (lo := (20205021 / 31250000)) (hi := (646560673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2982756207 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2982756207 / 1562500000) = 1/(1562500000 / 2982756207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (20205021 / 31250000) (646560673 / 1000000000) (Real.log (2982756207 / 1562500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2982756207 / 1562500000) = -Real.log (1562500000 / 2982756207) := by
    rw [show ((2982756207 / 1562500000) : ℝ) = ((1562500000 / 2982756207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (40469201 / 62500000) ≤ -Real.log (250000000000 / 477692936867) ∧
    -Real.log (250000000000 / 477692936867) ≤ (647507217 / 1000000000) := by
  have h := checkLog_sound (w := (227692936867 / 727692936867)) (n := 12)
    (lo := (40469201 / 62500000)) (hi := (647507217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477692936867 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477692936867 / 250000000000) = 1/(250000000000 / 477692936867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (40469201 / 62500000) (647507217 / 1000000000) (Real.log (477692936867 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (477692936867 / 250000000000) = -Real.log (250000000000 / 477692936867) := by
    rw [show ((477692936867 / 250000000000) : ℝ) = ((250000000000 / 477692936867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (462233961 / 1000000000) ≤ -Real.log (125000000000 / 198452087689) ∧
    -Real.log (125000000000 / 198452087689) ≤ (231116981 / 500000000) := by
  have h := checkLog_sound (w := (73452087689 / 323452087689)) (n := 12)
    (lo := (462233961 / 1000000000)) (hi := (231116981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198452087689 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198452087689 / 125000000000) = 1/(125000000000 / 198452087689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (462233961 / 1000000000) (231116981 / 500000000) (Real.log (198452087689 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (198452087689 / 125000000000) = -Real.log (125000000000 / 198452087689) := by
    rw [show ((198452087689 / 125000000000) : ℝ) = ((125000000000 / 198452087689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18516943 / 40000000) ≤ -Real.log (500000000000 / 794355960833) ∧
    -Real.log (500000000000 / 794355960833) ≤ (57865447 / 125000000) := by
  have h := checkLog_sound (w := (294355960833 / 1294355960833)) (n := 12)
    (lo := (18516943 / 40000000)) (hi := (57865447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794355960833 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794355960833 / 500000000000) = 1/(500000000000 / 794355960833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18516943 / 40000000) (57865447 / 125000000) (Real.log (794355960833 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (794355960833 / 500000000000) = -Real.log (500000000000 / 794355960833) := by
    rw [show ((794355960833 / 500000000000) : ℝ) = ((500000000000 / 794355960833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0408

end


