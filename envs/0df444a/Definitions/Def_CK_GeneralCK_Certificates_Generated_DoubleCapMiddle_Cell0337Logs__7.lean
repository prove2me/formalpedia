-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0337Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0337Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:24:20.899026+00:00
-- url     : https://prove2.me/theorems/76e94ce4-da02-4b66-889e-5b09746accb7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0337Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0338Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0337Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0338Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0339Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0340Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0341Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0342Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0343Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0337Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0338Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0339Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0340Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0341Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0342Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0343Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0337Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0338Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0339Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0340Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0341Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0342Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0343Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0337Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0338Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0339Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0340Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0341Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0342Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0343Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0337Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0337
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

theorem reflection_log_1_neg : (21522163 / 100000000) ≤ -Real.log (10240 / 12699) ∧
    -Real.log (10240 / 12699) ≤ (215221631 / 1000000000) := by
  have h := checkLog_sound (w := (2459 / 22939)) (n := 12)
    (lo := (21522163 / 100000000)) (hi := (215221631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12699 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12699 / 10240) = 1/(10240 / 12699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21522163 / 100000000) (215221631 / 1000000000) (Real.log (12699 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12699 / 10240) = -Real.log (10240 / 12699) := by
    rw [show ((12699 / 10240) : ℝ) = ((10240 / 12699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (137308377 / 500000000) ≤ -Real.log (7781 / 10240) ∧
    -Real.log (7781 / 10240) ≤ (54923351 / 200000000) := by
  have h := checkLog_sound (w := (2459 / 18021)) (n := 12)
    (lo := (137308377 / 500000000)) (hi := (54923351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7781) = 1/(7781 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-54923351 / 200000000) (-137308377 / 500000000) (Real.log (7781 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (214985363 / 1000000000) ≤ -Real.log (1280 / 1587) ∧
    -Real.log (1280 / 1587) ≤ (53746341 / 250000000) := by
  have h := checkLog_sound (w := (307 / 2867)) (n := 12)
    (lo := (214985363 / 1000000000)) (hi := (53746341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1587 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1587 / 1280) = 1/(1280 / 1587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (214985363 / 1000000000) (53746341 / 250000000) (Real.log (1587 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1587 / 1280) = -Real.log (1280 / 1587) := by
    rw [show ((1587 / 1280) : ℝ) = ((1280 / 1587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (137115637 / 500000000) ≤ -Real.log (973 / 1280) ∧
    -Real.log (973 / 1280) ≤ (10969251 / 40000000) := by
  have h := checkLog_sound (w := (307 / 2253)) (n := 12)
    (lo := (137115637 / 500000000)) (hi := (10969251 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 973) = 1/(973 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10969251 / 40000000) (-137115637 / 500000000) (Real.log (973 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15689073 / 40000000) ≤ -Real.log (5120 / 7579) ∧
    -Real.log (5120 / 7579) ≤ (196113413 / 500000000) := by
  have h := checkLog_sound (w := (2459 / 12699)) (n := 12)
    (lo := (15689073 / 40000000)) (hi := (196113413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7579 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7579 / 5120) = 1/(5120 / 7579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15689073 / 40000000) (196113413 / 500000000) (Real.log (7579 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7579 / 5120) = -Real.log (5120 / 7579) := by
    rw [show ((7579 / 5120) : ℝ) = ((5120 / 7579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (654452447 / 1000000000) ≤ -Real.log (2661 / 5120) ∧
    -Real.log (2661 / 5120) ≤ (20451639 / 31250000) := by
  have h := checkLog_sound (w := (2459 / 7781)) (n := 12)
    (lo := (654452447 / 1000000000)) (hi := (20451639 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2661) = 1/(2661 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-20451639 / 31250000) (-654452447 / 1000000000) (Real.log (2661 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97957729 / 250000000) ≤ -Real.log (640 / 947) ∧
    -Real.log (640 / 947) ≤ (391830917 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 1587)) (n := 12)
    (lo := (97957729 / 250000000)) (hi := (391830917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((947 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(947 / 640) = 1/(640 / 947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97957729 / 250000000) (391830917 / 1000000000) (Real.log (947 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (947 / 640) = -Real.log (640 / 947) := by
    rw [show ((947 / 640) : ℝ) = ((640 / 947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (326662843 / 500000000) ≤ -Real.log (333 / 640) ∧
    -Real.log (333 / 640) ≤ (653325687 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 973)) (n := 12)
    (lo := (326662843 / 500000000)) (hi := (653325687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 333) = 1/(333 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-653325687 / 1000000000) (-326662843 / 500000000) (Real.log (333 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (294754751 / 1000000000) ≤ -Real.log (1000000 / 1342797) ∧
    -Real.log (1000000 / 1342797) ≤ (4605543 / 15625000) := by
  have h := checkLog_sound (w := (342797 / 2342797)) (n := 12)
    (lo := (294754751 / 1000000000)) (hi := (4605543 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1342797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1342797 / 1000000) = 1/(1000000 / 1342797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (294754751 / 1000000000) (4605543 / 15625000) (Real.log (1342797 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1342797 / 1000000) = -Real.log (1000000 / 1342797) := by
    rw [show ((1342797 / 1000000) : ℝ) = ((1000000 / 1342797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52470291 / 125000000) ≤ -Real.log (657203 / 1000000) ∧
    -Real.log (657203 / 1000000) ≤ (419762329 / 1000000000) := by
  have h := checkLog_sound (w := (342797 / 1657203)) (n := 12)
    (lo := (52470291 / 125000000)) (hi := (419762329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 657203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 657203) = 1/(657203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-419762329 / 1000000000) (-52470291 / 125000000) (Real.log (657203 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (295074183 / 1000000000) ≤ -Real.log (500000 / 671613) ∧
    -Real.log (500000 / 671613) ≤ (36884273 / 125000000) := by
  have h := checkLog_sound (w := (171613 / 1171613)) (n := 12)
    (lo := (295074183 / 1000000000)) (hi := (36884273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671613 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671613 / 500000) = 1/(500000 / 671613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (295074183 / 1000000000) (36884273 / 125000000) (Real.log (671613 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (671613 / 500000) = -Real.log (500000 / 671613) := by
    rw [show ((671613 / 500000) : ℝ) = ((500000 / 671613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (420415307 / 1000000000) ≤ -Real.log (328387 / 500000) ∧
    -Real.log (328387 / 500000) ≤ (105103827 / 250000000) := by
  have h := checkLog_sound (w := (171613 / 828387)) (n := 12)
    (lo := (420415307 / 1000000000)) (hi := (105103827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 328387) = 1/(328387 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-105103827 / 250000000) (-420415307 / 1000000000) (Real.log (328387 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (223576257 / 1000000000) ≤ -Real.log (1000000 / 1250541) ∧
    -Real.log (1000000 / 1250541) ≤ (111788129 / 500000000) := by
  have h := checkLog_sound (w := (250541 / 2250541)) (n := 12)
    (lo := (223576257 / 1000000000)) (hi := (111788129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250541 / 1000000) = 1/(1000000 / 1250541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (223576257 / 1000000000) (111788129 / 500000000) (Real.log (1250541 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1250541 / 1000000) = -Real.log (1000000 / 1250541) := by
    rw [show ((1250541 / 1000000) : ℝ) = ((1000000 / 1250541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (144201833 / 500000000) ≤ -Real.log (749459 / 1000000) ∧
    -Real.log (749459 / 1000000) ≤ (288403667 / 1000000000) := by
  have h := checkLog_sound (w := (250541 / 1749459)) (n := 12)
    (lo := (144201833 / 500000000)) (hi := (288403667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 749459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 749459) = 1/(749459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-288403667 / 1000000000) (-144201833 / 500000000) (Real.log (749459 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (44768821 / 200000000) ≤ -Real.log (250000 / 312719) ∧
    -Real.log (250000 / 312719) ≤ (111922053 / 500000000) := by
  have h := checkLog_sound (w := (62719 / 562719)) (n := 12)
    (lo := (44768821 / 200000000)) (hi := (111922053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312719 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312719 / 250000) = 1/(250000 / 312719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (44768821 / 200000000) (111922053 / 500000000) (Real.log (312719 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (312719 / 250000) = -Real.log (250000 / 312719) := by
    rw [show ((312719 / 250000) : ℝ) = ((250000 / 312719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57770151 / 200000000) ≤ -Real.log (187281 / 250000) ∧
    -Real.log (187281 / 250000) ≤ (72212689 / 250000000) := by
  have h := checkLog_sound (w := (62719 / 437281)) (n := 12)
    (lo := (57770151 / 200000000)) (hi := (72212689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187281) = 1/(187281 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-72212689 / 250000000) (-57770151 / 200000000) (Real.log (187281 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (714517079 / 1000000000) ≤ -Real.log (62500000000 / 127699983871) ∧
    -Real.log (62500000000 / 127699983871) ≤ (714517081 / 1000000000) := by
  have h := checkLog_sound (w := (2699983871 / 252699983871)) (n := 12)
    (lo := (21369899 / 1000000000)) (hi := (213699 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127699983871 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(127699983871 / 125000000000) = 1/(62500000000 / 127699983871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (714517079 / 1000000000) (714517081 / 1000000000) (Real.log (127699983871 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (127699983871 / 62500000000) = -Real.log (62500000000 / 127699983871) := by
    rw [show ((127699983871 / 62500000000) : ℝ) = ((62500000000 / 127699983871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (71548949 / 100000000) ≤ -Real.log (250000000000 / 511296884469) ∧
    -Real.log (250000000000 / 511296884469) ≤ (178872373 / 250000000) := by
  have h := checkLog_sound (w := (11296884469 / 1011296884469)) (n := 12)
    (lo := (2234231 / 100000000)) (hi := (22342311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511296884469 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(511296884469 / 500000000000) = 1/(250000000000 / 511296884469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (71548949 / 100000000) (178872373 / 250000000) (Real.log (511296884469 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (511296884469 / 250000000000) = -Real.log (250000000000 / 511296884469) := by
    rw [show ((511296884469 / 250000000000) : ℝ) = ((250000000000 / 511296884469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (511979923 / 1000000000) ≤ -Real.log (250000000000 / 417147902687) ∧
    -Real.log (250000000000 / 417147902687) ≤ (127994981 / 250000000) := by
  have h := checkLog_sound (w := (167147902687 / 667147902687)) (n := 12)
    (lo := (511979923 / 1000000000)) (hi := (127994981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417147902687 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417147902687 / 250000000000) = 1/(250000000000 / 417147902687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (511979923 / 1000000000) (127994981 / 250000000) (Real.log (417147902687 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (417147902687 / 250000000000) = -Real.log (250000000000 / 417147902687) := by
    rw [show ((417147902687 / 250000000000) : ℝ) = ((250000000000 / 417147902687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (25634743 / 50000000) ≤ -Real.log (6250000000 / 10436156097) ∧
    -Real.log (6250000000 / 10436156097) ≤ (512694861 / 1000000000) := by
  have h := checkLog_sound (w := (4186156097 / 16686156097)) (n := 12)
    (lo := (25634743 / 50000000)) (hi := (512694861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10436156097 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10436156097 / 6250000000) = 1/(6250000000 / 10436156097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (25634743 / 50000000) (512694861 / 1000000000) (Real.log (10436156097 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10436156097 / 6250000000) = -Real.log (6250000000 / 10436156097) := by
    rw [show ((10436156097 / 6250000000) : ℝ) = ((6250000000 / 10436156097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0337

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0338Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0338
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

theorem reflection_log_1_neg : (214985363 / 1000000000) ≤ -Real.log (1280 / 1587) ∧
    -Real.log (1280 / 1587) ≤ (53746341 / 250000000) := by
  have h := checkLog_sound (w := (307 / 2867)) (n := 12)
    (lo := (214985363 / 1000000000)) (hi := (53746341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1587 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1587 / 1280) = 1/(1280 / 1587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (214985363 / 1000000000) (53746341 / 250000000) (Real.log (1587 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1587 / 1280) = -Real.log (1280 / 1587) := by
    rw [show ((1587 / 1280) : ℝ) = ((1280 / 1587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (137115637 / 500000000) ≤ -Real.log (973 / 1280) ∧
    -Real.log (973 / 1280) ≤ (10969251 / 40000000) := by
  have h := checkLog_sound (w := (307 / 2253)) (n := 12)
    (lo := (137115637 / 500000000)) (hi := (10969251 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 973) = 1/(973 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10969251 / 40000000) (-137115637 / 500000000) (Real.log (973 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2684363 / 12500000) ≤ -Real.log (10240 / 12693) ∧
    -Real.log (10240 / 12693) ≤ (214749041 / 1000000000) := by
  have h := checkLog_sound (w := (2453 / 22933)) (n := 12)
    (lo := (2684363 / 12500000)) (hi := (214749041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12693 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12693 / 10240) = 1/(10240 / 12693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2684363 / 12500000) (214749041 / 1000000000) (Real.log (12693 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12693 / 10240) = -Real.log (10240 / 12693) := by
    rw [show ((12693 / 10240) : ℝ) = ((10240 / 12693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (273845943 / 1000000000) ≤ -Real.log (7787 / 10240) ∧
    -Real.log (7787 / 10240) ≤ (34230743 / 125000000) := by
  have h := checkLog_sound (w := (2453 / 18027)) (n := 12)
    (lo := (273845943 / 1000000000)) (hi := (34230743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7787) = 1/(7787 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-34230743 / 125000000) (-273845943 / 1000000000) (Real.log (7787 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97957729 / 250000000) ≤ -Real.log (640 / 947) ∧
    -Real.log (640 / 947) ≤ (391830917 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 1587)) (n := 12)
    (lo := (97957729 / 250000000)) (hi := (391830917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((947 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(947 / 640) = 1/(640 / 947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (97957729 / 250000000) (391830917 / 1000000000) (Real.log (947 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (947 / 640) = -Real.log (640 / 947) := by
    rw [show ((947 / 640) : ℝ) = ((640 / 947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (326662843 / 500000000) ≤ -Real.log (333 / 640) ∧
    -Real.log (333 / 640) ≤ (653325687 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 973)) (n := 12)
    (lo := (326662843 / 500000000)) (hi := (653325687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 333) = 1/(333 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-653325687 / 1000000000) (-326662843 / 500000000) (Real.log (333 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (391434851 / 1000000000) ≤ -Real.log (5120 / 7573) ∧
    -Real.log (5120 / 7573) ≤ (97858713 / 250000000) := by
  have h := checkLog_sound (w := (2453 / 12693)) (n := 12)
    (lo := (391434851 / 1000000000)) (hi := (97858713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7573 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7573 / 5120) = 1/(5120 / 7573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (391434851 / 1000000000) (97858713 / 250000000) (Real.log (7573 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7573 / 5120) = -Real.log (5120 / 7573) := by
    rw [show ((7573 / 5120) : ℝ) = ((5120 / 7573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (652200193 / 1000000000) ≤ -Real.log (2667 / 5120) ∧
    -Real.log (2667 / 5120) ≤ (326100097 / 500000000) := by
  have h := checkLog_sound (w := (2453 / 7787)) (n := 12)
    (lo := (652200193 / 1000000000)) (hi := (326100097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2667) = 1/(2667 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-326100097 / 500000000) (-652200193 / 1000000000) (Real.log (2667 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (147217609 / 500000000) ≤ -Real.log (31250 / 41949) ∧
    -Real.log (31250 / 41949) ≤ (294435219 / 1000000000) := by
  have h := checkLog_sound (w := (10699 / 73199)) (n := 12)
    (lo := (147217609 / 500000000)) (hi := (294435219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41949 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41949 / 31250) = 1/(31250 / 41949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (147217609 / 500000000) (294435219 / 1000000000) (Real.log (41949 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (41949 / 31250) = -Real.log (31250 / 41949) := by
    rw [show ((41949 / 31250) : ℝ) = ((31250 / 41949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (209554887 / 500000000) ≤ -Real.log (20551 / 31250) ∧
    -Real.log (20551 / 31250) ≤ (16764391 / 40000000) := by
  have h := checkLog_sound (w := (10699 / 51801)) (n := 12)
    (lo := (209554887 / 500000000)) (hi := (16764391 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 20551) = 1/(20551 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-16764391 / 40000000) (-209554887 / 500000000) (Real.log (20551 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (36844437 / 125000000) ≤ -Real.log (500000 / 671399) ∧
    -Real.log (500000 / 671399) ≤ (294755497 / 1000000000) := by
  have h := checkLog_sound (w := (171399 / 1171399)) (n := 12)
    (lo := (36844437 / 125000000)) (hi := (294755497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671399 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671399 / 500000) = 1/(500000 / 671399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (36844437 / 125000000) (294755497 / 1000000000) (Real.log (671399 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (671399 / 500000) = -Real.log (500000 / 671399) := by
    rw [show ((671399 / 500000) : ℝ) = ((500000 / 671399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (419763849 / 1000000000) ≤ -Real.log (328601 / 500000) ∧
    -Real.log (328601 / 500000) ≤ (8395277 / 20000000) := by
  have h := checkLog_sound (w := (171399 / 828601)) (n := 12)
    (lo := (419763849 / 1000000000)) (hi := (8395277 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 328601) = 1/(328601 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8395277 / 20000000) (-419763849 / 1000000000) (Real.log (328601 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (223309137 / 1000000000) ≤ -Real.log (1000000 / 1250207) ∧
    -Real.log (1000000 / 1250207) ≤ (111654569 / 500000000) := by
  have h := checkLog_sound (w := (250207 / 2250207)) (n := 12)
    (lo := (223309137 / 1000000000)) (hi := (111654569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250207 / 1000000) = 1/(1000000 / 1250207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (223309137 / 1000000000) (111654569 / 500000000) (Real.log (1250207 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1250207 / 1000000) = -Real.log (1000000 / 1250207) := by
    rw [show ((1250207 / 1000000) : ℝ) = ((1000000 / 1250207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (28795811 / 100000000) ≤ -Real.log (749793 / 1000000) ∧
    -Real.log (749793 / 1000000) ≤ (287958111 / 1000000000) := by
  have h := checkLog_sound (w := (250207 / 1749793)) (n := 12)
    (lo := (28795811 / 100000000)) (hi := (287958111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 749793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 749793) = 1/(749793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-287958111 / 1000000000) (-28795811 / 100000000) (Real.log (749793 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (223577057 / 1000000000) ≤ -Real.log (500000 / 625271) ∧
    -Real.log (500000 / 625271) ≤ (111788529 / 500000000) := by
  have h := checkLog_sound (w := (125271 / 1125271)) (n := 12)
    (lo := (223577057 / 1000000000)) (hi := (111788529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625271 / 500000) = 1/(500000 / 625271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (223577057 / 1000000000) (111788529 / 500000000) (Real.log (625271 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (625271 / 500000) = -Real.log (500000 / 625271) := by
    rw [show ((625271 / 500000) : ℝ) = ((500000 / 625271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57681 / 200000) ≤ -Real.log (374729 / 500000) ∧
    -Real.log (374729 / 500000) ≤ (288405001 / 1000000000) := by
  have h := checkLog_sound (w := (125271 / 874729)) (n := 12)
    (lo := (57681 / 200000)) (hi := (288405001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 374729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 374729) = 1/(374729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-288405001 / 1000000000) (-57681 / 200000) (Real.log (374729 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (22298281 / 31250000) ≤ -Real.log (500000000000 / 1020607269719) ∧
    -Real.log (500000000000 / 1020607269719) ≤ (356772497 / 500000000) := by
  have h := checkLog_sound (w := (20607269719 / 2020607269719)) (n := 12)
    (lo := (5099453 / 250000000)) (hi := (20397813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1020607269719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1020607269719 / 1000000000000) = 1/(500000000000 / 1020607269719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (22298281 / 31250000) (356772497 / 500000000) (Real.log (1020607269719 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1020607269719 / 500000000000) = -Real.log (500000000000 / 1020607269719) := by
    rw [show ((1020607269719 / 500000000000) : ℝ) = ((500000000000 / 1020607269719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (142903869 / 200000000) ≤ -Real.log (500000000000 / 1021602186239) ∧
    -Real.log (500000000000 / 1021602186239) ≤ (714519347 / 1000000000) := by
  have h := checkLog_sound (w := (21602186239 / 2021602186239)) (n := 12)
    (lo := (4274433 / 200000000)) (hi := (10686083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1021602186239 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1021602186239 / 1000000000000) = 1/(500000000000 / 1021602186239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (142903869 / 200000000) (714519347 / 1000000000) (Real.log (1021602186239 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1021602186239 / 500000000000) = -Real.log (500000000000 / 1021602186239) := by
    rw [show ((1021602186239 / 500000000000) : ℝ) = ((500000000000 / 1021602186239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (31954203 / 62500000) ≤ -Real.log (500000000000 / 833701434929) ∧
    -Real.log (500000000000 / 833701434929) ≤ (511267249 / 1000000000) := by
  have h := checkLog_sound (w := (333701434929 / 1333701434929)) (n := 12)
    (lo := (31954203 / 62500000)) (hi := (511267249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833701434929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833701434929 / 500000000000) = 1/(500000000000 / 833701434929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (31954203 / 62500000) (511267249 / 1000000000) (Real.log (833701434929 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (833701434929 / 500000000000) = -Real.log (500000000000 / 833701434929) := by
    rw [show ((833701434929 / 500000000000) : ℝ) = ((500000000000 / 833701434929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (511982057 / 1000000000) ≤ -Real.log (250000000000 / 417148792861) ∧
    -Real.log (250000000000 / 417148792861) ≤ (255991029 / 500000000) := by
  have h := checkLog_sound (w := (167148792861 / 667148792861)) (n := 12)
    (lo := (511982057 / 1000000000)) (hi := (255991029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417148792861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417148792861 / 250000000000) = 1/(250000000000 / 417148792861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (511982057 / 1000000000) (255991029 / 500000000) (Real.log (417148792861 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (417148792861 / 250000000000) = -Real.log (250000000000 / 417148792861) := by
    rw [show ((417148792861 / 250000000000) : ℝ) = ((250000000000 / 417148792861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0338

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0339Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0339
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

theorem reflection_log_1_neg : (2684363 / 12500000) ≤ -Real.log (10240 / 12693) ∧
    -Real.log (10240 / 12693) ≤ (214749041 / 1000000000) := by
  have h := checkLog_sound (w := (2453 / 22933)) (n := 12)
    (lo := (2684363 / 12500000)) (hi := (214749041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12693 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12693 / 10240) = 1/(10240 / 12693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2684363 / 12500000) (214749041 / 1000000000) (Real.log (12693 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12693 / 10240) = -Real.log (10240 / 12693) := by
    rw [show ((12693 / 10240) : ℝ) = ((10240 / 12693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (273845943 / 1000000000) ≤ -Real.log (7787 / 10240) ∧
    -Real.log (7787 / 10240) ≤ (34230743 / 125000000) := by
  have h := checkLog_sound (w := (2453 / 18027)) (n := 12)
    (lo := (273845943 / 1000000000)) (hi := (34230743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7787) = 1/(7787 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-34230743 / 125000000) (-273845943 / 1000000000) (Real.log (7787 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (107256331 / 500000000) ≤ -Real.log (1024 / 1269) ∧
    -Real.log (1024 / 1269) ≤ (214512663 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 2293)) (n := 12)
    (lo := (107256331 / 500000000)) (hi := (214512663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269 / 1024) = 1/(1024 / 1269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (107256331 / 500000000) (214512663 / 1000000000) (Real.log (1269 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1269 / 1024) = -Real.log (1024 / 1269) := by
    rw [show ((1269 / 1024) : ℝ) = ((1024 / 1269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (273460759 / 1000000000) ≤ -Real.log (779 / 1024) ∧
    -Real.log (779 / 1024) ≤ (6836519 / 25000000) := by
  have h := checkLog_sound (w := (245 / 1803)) (n := 12)
    (lo := (273460759 / 1000000000)) (hi := (6836519 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 779) = 1/(779 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6836519 / 25000000) (-273460759 / 1000000000) (Real.log (779 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (391434851 / 1000000000) ≤ -Real.log (5120 / 7573) ∧
    -Real.log (5120 / 7573) ≤ (97858713 / 250000000) := by
  have h := checkLog_sound (w := (2453 / 12693)) (n := 12)
    (lo := (391434851 / 1000000000)) (hi := (97858713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7573 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7573 / 5120) = 1/(5120 / 7573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (391434851 / 1000000000) (97858713 / 250000000) (Real.log (7573 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7573 / 5120) = -Real.log (5120 / 7573) := by
    rw [show ((7573 / 5120) : ℝ) = ((5120 / 7573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (652200193 / 1000000000) ≤ -Real.log (2667 / 5120) ∧
    -Real.log (2667 / 5120) ≤ (326100097 / 500000000) := by
  have h := checkLog_sound (w := (2453 / 7787)) (n := 12)
    (lo := (652200193 / 1000000000)) (hi := (326100097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2667) = 1/(2667 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-326100097 / 500000000) (-652200193 / 1000000000) (Real.log (2667 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97759657 / 250000000) ≤ -Real.log (512 / 757) ∧
    -Real.log (512 / 757) ≤ (391038629 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 1269)) (n := 12)
    (lo := (97759657 / 250000000)) (hi := (391038629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757 / 512) = 1/(512 / 757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97759657 / 250000000) (391038629 / 1000000000) (Real.log (757 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (757 / 512) = -Real.log (512 / 757) := by
    rw [show ((757 / 512) : ℝ) = ((512 / 757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (325537983 / 500000000) ≤ -Real.log (267 / 512) ∧
    -Real.log (267 / 512) ≤ (651075967 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 779)) (n := 12)
    (lo := (325537983 / 500000000)) (hi := (651075967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 267) = 1/(267 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-651075967 / 1000000000) (-325537983 / 500000000) (Real.log (267 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36764541 / 125000000) ≤ -Real.log (50000 / 67097) ∧
    -Real.log (50000 / 67097) ≤ (294116329 / 1000000000) := by
  have h := checkLog_sound (w := (17097 / 117097)) (n := 12)
    (lo := (36764541 / 125000000)) (hi := (294116329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67097 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67097 / 50000) = 1/(50000 / 67097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36764541 / 125000000) (294116329 / 1000000000) (Real.log (67097 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (67097 / 50000) = -Real.log (50000 / 67097) := by
    rw [show ((67097 / 50000) : ℝ) = ((50000 / 67097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (209229583 / 500000000) ≤ -Real.log (32903 / 50000) ∧
    -Real.log (32903 / 50000) ≤ (418459167 / 1000000000) := by
  have h := checkLog_sound (w := (17097 / 82903)) (n := 12)
    (lo := (209229583 / 500000000)) (hi := (418459167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 32903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 32903) = 1/(32903 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-418459167 / 1000000000) (-209229583 / 500000000) (Real.log (32903 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (294435963 / 1000000000) ≤ -Real.log (1000000 / 1342369) ∧
    -Real.log (1000000 / 1342369) ≤ (73608991 / 250000000) := by
  have h := checkLog_sound (w := (342369 / 2342369)) (n := 12)
    (lo := (294435963 / 1000000000)) (hi := (73608991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1342369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1342369 / 1000000) = 1/(1000000 / 1342369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (294435963 / 1000000000) (73608991 / 250000000) (Real.log (1342369 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1342369 / 1000000) = -Real.log (1000000 / 1342369) := by
    rw [show ((1342369 / 1000000) : ℝ) = ((1000000 / 1342369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (83822259 / 200000000) ≤ -Real.log (657631 / 1000000) ∧
    -Real.log (657631 / 1000000) ≤ (3274307 / 7812500) := by
  have h := checkLog_sound (w := (342369 / 1657631)) (n := 12)
    (lo := (83822259 / 200000000)) (hi := (3274307 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 657631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 657631) = 1/(657631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3274307 / 7812500) (-83822259 / 200000000) (Real.log (657631 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (111520973 / 500000000) ≤ -Real.log (1000000 / 1249873) ∧
    -Real.log (1000000 / 1249873) ≤ (223041947 / 1000000000) := by
  have h := checkLog_sound (w := (249873 / 2249873)) (n := 12)
    (lo := (111520973 / 500000000)) (hi := (223041947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249873 / 1000000) = 1/(1000000 / 1249873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (111520973 / 500000000) (223041947 / 1000000000) (Real.log (1249873 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1249873 / 1000000) = -Real.log (1000000 / 1249873) := by
    rw [show ((1249873 / 1000000) : ℝ) = ((1000000 / 1249873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (287512753 / 1000000000) ≤ -Real.log (750127 / 1000000) ∧
    -Real.log (750127 / 1000000) ≤ (143756377 / 500000000) := by
  have h := checkLog_sound (w := (249873 / 1750127)) (n := 12)
    (lo := (287512753 / 1000000000)) (hi := (143756377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750127) = 1/(750127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-143756377 / 500000000) (-287512753 / 1000000000) (Real.log (750127 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (223309937 / 1000000000) ≤ -Real.log (31250 / 39069) ∧
    -Real.log (31250 / 39069) ≤ (111654969 / 500000000) := by
  have h := checkLog_sound (w := (7819 / 70319)) (n := 12)
    (lo := (223309937 / 1000000000)) (hi := (111654969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39069 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39069 / 31250) = 1/(31250 / 39069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (223309937 / 1000000000) (111654969 / 500000000) (Real.log (39069 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (39069 / 31250) = -Real.log (31250 / 39069) := by
    rw [show ((39069 / 31250) : ℝ) = ((31250 / 39069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (71989861 / 250000000) ≤ -Real.log (23431 / 31250) ∧
    -Real.log (23431 / 31250) ≤ (57591889 / 200000000) := by
  have h := checkLog_sound (w := (7819 / 54681)) (n := 12)
    (lo := (71989861 / 250000000)) (hi := (57591889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23431) = 1/(23431 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-57591889 / 200000000) (-71989861 / 250000000) (Real.log (23431 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (356287747 / 500000000) ≤ -Real.log (50000000000 / 101961827189) ∧
    -Real.log (50000000000 / 101961827189) ≤ (89071937 / 125000000) := by
  have h := checkLog_sound (w := (1961827189 / 201961827189)) (n := 12)
    (lo := (9714157 / 500000000)) (hi := (3885663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101961827189 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(101961827189 / 100000000000) = 1/(50000000000 / 101961827189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (356287747 / 500000000) (89071937 / 125000000) (Real.log (101961827189 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (101961827189 / 50000000000) = -Real.log (50000000000 / 101961827189) := by
    rw [show ((101961827189 / 50000000000) : ℝ) = ((50000000000 / 101961827189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (356773629 / 500000000) ≤ -Real.log (50000000000 / 102060958197) ∧
    -Real.log (50000000000 / 102060958197) ≤ (35677363 / 50000000) := by
  have h := checkLog_sound (w := (2060958197 / 202060958197)) (n := 12)
    (lo := (10200039 / 500000000)) (hi := (20400079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102060958197 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102060958197 / 100000000000) = 1/(50000000000 / 102060958197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (356773629 / 500000000) (35677363 / 50000000) (Real.log (102060958197 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (102060958197 / 50000000000) = -Real.log (50000000000 / 102060958197) := by
    rw [show ((102060958197 / 50000000000) : ℝ) = ((50000000000 / 102060958197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (510554699 / 1000000000) ≤ -Real.log (25000000000 / 41655379689) ∧
    -Real.log (25000000000 / 41655379689) ≤ (5105547 / 10000000) := by
  have h := checkLog_sound (w := (16655379689 / 66655379689)) (n := 12)
    (lo := (510554699 / 1000000000)) (hi := (5105547 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41655379689 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41655379689 / 25000000000) = 1/(25000000000 / 41655379689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (510554699 / 1000000000) (5105547 / 10000000) (Real.log (41655379689 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (41655379689 / 25000000000) = -Real.log (25000000000 / 41655379689) := by
    rw [show ((41655379689 / 25000000000) : ℝ) = ((25000000000 / 41655379689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (511269381 / 1000000000) ≤ -Real.log (125000000000 / 208425803423) ∧
    -Real.log (125000000000 / 208425803423) ≤ (255634691 / 500000000) := by
  have h := checkLog_sound (w := (83425803423 / 333425803423)) (n := 12)
    (lo := (511269381 / 1000000000)) (hi := (255634691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208425803423 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(208425803423 / 125000000000) = 1/(125000000000 / 208425803423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (511269381 / 1000000000) (255634691 / 500000000) (Real.log (208425803423 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (208425803423 / 125000000000) = -Real.log (125000000000 / 208425803423) := by
    rw [show ((208425803423 / 125000000000) : ℝ) = ((125000000000 / 208425803423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0339

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0340Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0340
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

theorem reflection_log_1_neg : (107256331 / 500000000) ≤ -Real.log (1024 / 1269) ∧
    -Real.log (1024 / 1269) ≤ (214512663 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 2293)) (n := 12)
    (lo := (107256331 / 500000000)) (hi := (214512663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269 / 1024) = 1/(1024 / 1269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (107256331 / 500000000) (214512663 / 1000000000) (Real.log (1269 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1269 / 1024) = -Real.log (1024 / 1269) := by
    rw [show ((1269 / 1024) : ℝ) = ((1024 / 1269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (273460759 / 1000000000) ≤ -Real.log (779 / 1024) ∧
    -Real.log (779 / 1024) ≤ (6836519 / 25000000) := by
  have h := checkLog_sound (w := (245 / 1803)) (n := 12)
    (lo := (273460759 / 1000000000)) (hi := (6836519 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 779) = 1/(779 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6836519 / 25000000) (-273460759 / 1000000000) (Real.log (779 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (214276227 / 1000000000) ≤ -Real.log (10240 / 12687) ∧
    -Real.log (10240 / 12687) ≤ (53569057 / 250000000) := by
  have h := checkLog_sound (w := (2447 / 22927)) (n := 12)
    (lo := (214276227 / 1000000000)) (hi := (53569057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12687 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12687 / 10240) = 1/(10240 / 12687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (214276227 / 1000000000) (53569057 / 250000000) (Real.log (12687 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12687 / 10240) = -Real.log (10240 / 12687) := by
    rw [show ((12687 / 10240) : ℝ) = ((10240 / 12687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (68268931 / 250000000) ≤ -Real.log (7793 / 10240) ∧
    -Real.log (7793 / 10240) ≤ (10923029 / 40000000) := by
  have h := checkLog_sound (w := (2447 / 18033)) (n := 12)
    (lo := (68268931 / 250000000)) (hi := (10923029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7793) = 1/(7793 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10923029 / 40000000) (-68268931 / 250000000) (Real.log (7793 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97759657 / 250000000) ≤ -Real.log (512 / 757) ∧
    -Real.log (512 / 757) ≤ (391038629 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 1269)) (n := 12)
    (lo := (97759657 / 250000000)) (hi := (391038629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757 / 512) = 1/(512 / 757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (97759657 / 250000000) (391038629 / 1000000000) (Real.log (757 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (757 / 512) = -Real.log (512 / 757) := by
    rw [show ((757 / 512) : ℝ) = ((512 / 757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (325537983 / 500000000) ≤ -Real.log (267 / 512) ∧
    -Real.log (267 / 512) ≤ (651075967 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 779)) (n := 12)
    (lo := (325537983 / 500000000)) (hi := (651075967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 267) = 1/(267 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-651075967 / 1000000000) (-325537983 / 500000000) (Real.log (267 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48830281 / 125000000) ≤ -Real.log (5120 / 7567) ∧
    -Real.log (5120 / 7567) ≤ (390642249 / 1000000000) := by
  have h := checkLog_sound (w := (2447 / 12687)) (n := 12)
    (lo := (48830281 / 125000000)) (hi := (390642249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7567 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7567 / 5120) = 1/(5120 / 7567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48830281 / 125000000) (390642249 / 1000000000) (Real.log (7567 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7567 / 5120) = -Real.log (5120 / 7567) := by
    rw [show ((7567 / 5120) : ℝ) = ((5120 / 7567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (649953001 / 1000000000) ≤ -Real.log (2673 / 5120) ∧
    -Real.log (2673 / 5120) ≤ (324976501 / 500000000) := by
  have h := checkLog_sound (w := (2447 / 7793)) (n := 12)
    (lo := (649953001 / 1000000000)) (hi := (324976501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2673) = 1/(2673 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-324976501 / 500000000) (-649953001 / 1000000000) (Real.log (2673 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29379659 / 100000000) ≤ -Real.log (1000000 / 1341511) ∧
    -Real.log (1000000 / 1341511) ≤ (293796591 / 1000000000) := by
  have h := checkLog_sound (w := (341511 / 2341511)) (n := 12)
    (lo := (29379659 / 100000000)) (hi := (293796591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341511 / 1000000) = 1/(1000000 / 1341511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29379659 / 100000000) (293796591 / 1000000000) (Real.log (1341511 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1341511 / 1000000) = -Real.log (1000000 / 1341511) := by
    rw [show ((1341511 / 1000000) : ℝ) = ((1000000 / 1341511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (208903731 / 500000000) ≤ -Real.log (658489 / 1000000) ∧
    -Real.log (658489 / 1000000) ≤ (417807463 / 1000000000) := by
  have h := checkLog_sound (w := (341511 / 1658489)) (n := 12)
    (lo := (208903731 / 500000000)) (hi := (417807463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658489) = 1/(658489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-417807463 / 1000000000) (-208903731 / 500000000) (Real.log (658489 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (294117073 / 1000000000) ≤ -Real.log (1000000 / 1341941) ∧
    -Real.log (1000000 / 1341941) ≤ (147058537 / 500000000) := by
  have h := checkLog_sound (w := (341941 / 2341941)) (n := 12)
    (lo := (294117073 / 1000000000)) (hi := (147058537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341941 / 1000000) = 1/(1000000 / 1341941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (294117073 / 1000000000) (147058537 / 500000000) (Real.log (1341941 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1341941 / 1000000) = -Real.log (1000000 / 1341941) := by
    rw [show ((1341941 / 1000000) : ℝ) = ((1000000 / 1341941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (209230343 / 500000000) ≤ -Real.log (658059 / 1000000) ∧
    -Real.log (658059 / 1000000) ≤ (418460687 / 1000000000) := by
  have h := checkLog_sound (w := (341941 / 1658059)) (n := 12)
    (lo := (209230343 / 500000000)) (hi := (418460687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658059) = 1/(658059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-418460687 / 1000000000) (-209230343 / 500000000) (Real.log (658059 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (222774683 / 1000000000) ≤ -Real.log (1000000 / 1249539) ∧
    -Real.log (1000000 / 1249539) ≤ (55693671 / 250000000) := by
  have h := checkLog_sound (w := (249539 / 2249539)) (n := 12)
    (lo := (222774683 / 1000000000)) (hi := (55693671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249539 / 1000000) = 1/(1000000 / 1249539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (222774683 / 1000000000) (55693671 / 250000000) (Real.log (1249539 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1249539 / 1000000) = -Real.log (1000000 / 1249539) := by
    rw [show ((1249539 / 1000000) : ℝ) = ((1000000 / 1249539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (143533797 / 500000000) ≤ -Real.log (750461 / 1000000) ∧
    -Real.log (750461 / 1000000) ≤ (57413519 / 200000000) := by
  have h := checkLog_sound (w := (249539 / 1750461)) (n := 12)
    (lo := (143533797 / 500000000)) (hi := (57413519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750461) = 1/(750461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-57413519 / 200000000) (-143533797 / 500000000) (Real.log (750461 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (111521373 / 500000000) ≤ -Real.log (500000 / 624937) ∧
    -Real.log (500000 / 624937) ≤ (223042747 / 1000000000) := by
  have h := checkLog_sound (w := (124937 / 1124937)) (n := 12)
    (lo := (111521373 / 500000000)) (hi := (223042747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624937 / 500000) = 1/(500000 / 624937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (111521373 / 500000000) (223042747 / 1000000000) (Real.log (624937 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (624937 / 500000) = -Real.log (500000 / 624937) := by
    rw [show ((624937 / 500000) : ℝ) = ((500000 / 624937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (143757043 / 500000000) ≤ -Real.log (375063 / 500000) ∧
    -Real.log (375063 / 500000) ≤ (287514087 / 1000000000) := by
  have h := checkLog_sound (w := (124937 / 875063)) (n := 12)
    (lo := (143757043 / 500000000)) (hi := (287514087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375063) = 1/(375063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-287514087 / 1000000000) (-143757043 / 500000000) (Real.log (375063 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (177901013 / 250000000) ≤ -Real.log (500000000000 / 1018628253471) ∧
    -Real.log (500000000000 / 1018628253471) ≤ (355802027 / 500000000) := by
  have h := checkLog_sound (w := (18628253471 / 2018628253471)) (n := 12)
    (lo := (2307109 / 125000000)) (hi := (18456873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1018628253471 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1018628253471 / 1000000000000) = 1/(500000000000 / 1018628253471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (177901013 / 250000000) (355802027 / 500000000) (Real.log (1018628253471 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1018628253471 / 500000000000) = -Real.log (500000000000 / 1018628253471) := by
    rw [show ((1018628253471 / 500000000000) : ℝ) = ((500000000000 / 1018628253471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (356288879 / 500000000) ≤ -Real.log (250000000000 / 509810290567) ∧
    -Real.log (250000000000 / 509810290567) ≤ (4453611 / 6250000) := by
  have h := checkLog_sound (w := (9810290567 / 1009810290567)) (n := 12)
    (lo := (9715289 / 500000000)) (hi := (19430579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509810290567 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(509810290567 / 500000000000) = 1/(250000000000 / 509810290567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (356288879 / 500000000) (4453611 / 6250000) (Real.log (509810290567 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (509810290567 / 250000000000) = -Real.log (250000000000 / 509810290567) := by
    rw [show ((509810290567 / 250000000000) : ℝ) = ((250000000000 / 509810290567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (509842277 / 1000000000) ≤ -Real.log (500000000000 / 832514281221) ∧
    -Real.log (500000000000 / 832514281221) ≤ (254921139 / 500000000) := by
  have h := checkLog_sound (w := (332514281221 / 1332514281221)) (n := 12)
    (lo := (509842277 / 1000000000)) (hi := (254921139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832514281221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832514281221 / 500000000000) = 1/(500000000000 / 832514281221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (509842277 / 1000000000) (254921139 / 500000000) (Real.log (832514281221 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (832514281221 / 500000000000) = -Real.log (500000000000 / 832514281221) := by
    rw [show ((832514281221 / 500000000000) : ℝ) = ((500000000000 / 832514281221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (15954901 / 31250000) ≤ -Real.log (6250000000 / 10413867137) ∧
    -Real.log (6250000000 / 10413867137) ≤ (510556833 / 1000000000) := by
  have h := checkLog_sound (w := (4163867137 / 16663867137)) (n := 12)
    (lo := (15954901 / 31250000)) (hi := (510556833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10413867137 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10413867137 / 6250000000) = 1/(6250000000 / 10413867137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (15954901 / 31250000) (510556833 / 1000000000) (Real.log (10413867137 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10413867137 / 6250000000) = -Real.log (6250000000 / 10413867137) := by
    rw [show ((10413867137 / 6250000000) : ℝ) = ((6250000000 / 10413867137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0340

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0341Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0341
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

theorem reflection_log_1_neg : (214276227 / 1000000000) ≤ -Real.log (10240 / 12687) ∧
    -Real.log (10240 / 12687) ≤ (53569057 / 250000000) := by
  have h := checkLog_sound (w := (2447 / 22927)) (n := 12)
    (lo := (214276227 / 1000000000)) (hi := (53569057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12687 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12687 / 10240) = 1/(10240 / 12687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (214276227 / 1000000000) (53569057 / 250000000) (Real.log (12687 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12687 / 10240) = -Real.log (10240 / 12687) := by
    rw [show ((12687 / 10240) : ℝ) = ((10240 / 12687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (68268931 / 250000000) ≤ -Real.log (7793 / 10240) ∧
    -Real.log (7793 / 10240) ≤ (10923029 / 40000000) := by
  have h := checkLog_sound (w := (2447 / 18033)) (n := 12)
    (lo := (68268931 / 250000000)) (hi := (10923029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7793) = 1/(7793 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10923029 / 40000000) (-68268931 / 250000000) (Real.log (7793 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (214039737 / 1000000000) ≤ -Real.log (2560 / 3171) ∧
    -Real.log (2560 / 3171) ≤ (107019869 / 500000000) := by
  have h := checkLog_sound (w := (611 / 5731)) (n := 12)
    (lo := (214039737 / 1000000000)) (hi := (107019869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3171 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3171 / 2560) = 1/(2560 / 3171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (214039737 / 1000000000) (107019869 / 500000000) (Real.log (3171 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3171 / 2560) = -Real.log (2560 / 3171) := by
    rw [show ((3171 / 2560) : ℝ) = ((2560 / 3171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (272690837 / 1000000000) ≤ -Real.log (1949 / 2560) ∧
    -Real.log (1949 / 2560) ≤ (136345419 / 500000000) := by
  have h := checkLog_sound (w := (611 / 4509)) (n := 12)
    (lo := (272690837 / 1000000000)) (hi := (136345419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1949) = 1/(1949 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-136345419 / 500000000) (-272690837 / 1000000000) (Real.log (1949 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (48830281 / 125000000) ≤ -Real.log (5120 / 7567) ∧
    -Real.log (5120 / 7567) ≤ (390642249 / 1000000000) := by
  have h := checkLog_sound (w := (2447 / 12687)) (n := 12)
    (lo := (48830281 / 125000000)) (hi := (390642249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7567 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7567 / 5120) = 1/(5120 / 7567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (48830281 / 125000000) (390642249 / 1000000000) (Real.log (7567 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7567 / 5120) = -Real.log (5120 / 7567) := by
    rw [show ((7567 / 5120) : ℝ) = ((5120 / 7567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (649953001 / 1000000000) ≤ -Real.log (2673 / 5120) ∧
    -Real.log (2673 / 5120) ≤ (324976501 / 500000000) := by
  have h := checkLog_sound (w := (2447 / 7793)) (n := 12)
    (lo := (649953001 / 1000000000)) (hi := (324976501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2673) = 1/(2673 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-324976501 / 500000000) (-649953001 / 1000000000) (Real.log (2673 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (390245711 / 1000000000) ≤ -Real.log (1280 / 1891) ∧
    -Real.log (1280 / 1891) ≤ (24390357 / 62500000) := by
  have h := checkLog_sound (w := (611 / 3171)) (n := 12)
    (lo := (390245711 / 1000000000)) (hi := (24390357 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1891 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1891 / 1280) = 1/(1280 / 1891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (390245711 / 1000000000) (24390357 / 62500000) (Real.log (1891 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1891 / 1280) = -Real.log (1280 / 1891) := by
    rw [show ((1891 / 1280) : ℝ) = ((1280 / 1891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10137989 / 15625000) ≤ -Real.log (669 / 1280) ∧
    -Real.log (669 / 1280) ≤ (648831297 / 1000000000) := by
  have h := checkLog_sound (w := (611 / 1949)) (n := 12)
    (lo := (10137989 / 15625000)) (hi := (648831297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 669) = 1/(669 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-648831297 / 1000000000) (-10137989 / 15625000) (Real.log (669 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36684687 / 125000000) ≤ -Real.log (1000000 / 1341083) ∧
    -Real.log (1000000 / 1341083) ≤ (293477497 / 1000000000) := by
  have h := checkLog_sound (w := (341083 / 2341083)) (n := 12)
    (lo := (36684687 / 125000000)) (hi := (293477497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341083 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341083 / 1000000) = 1/(1000000 / 1341083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36684687 / 125000000) (293477497 / 1000000000) (Real.log (1341083 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1341083 / 1000000) = -Real.log (1000000 / 1341083) := by
    rw [show ((1341083 / 1000000) : ℝ) = ((1000000 / 1341083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4171577 / 10000000) ≤ -Real.log (658917 / 1000000) ∧
    -Real.log (658917 / 1000000) ≤ (417157701 / 1000000000) := by
  have h := checkLog_sound (w := (341083 / 1658917)) (n := 12)
    (lo := (4171577 / 10000000)) (hi := (417157701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658917) = 1/(658917 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-417157701 / 1000000000) (-4171577 / 10000000) (Real.log (658917 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (36724667 / 125000000) ≤ -Real.log (125000 / 167689) ∧
    -Real.log (125000 / 167689) ≤ (293797337 / 1000000000) := by
  have h := checkLog_sound (w := (42689 / 292689)) (n := 12)
    (lo := (36724667 / 125000000)) (hi := (293797337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167689 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167689 / 125000) = 1/(125000 / 167689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (36724667 / 125000000) (293797337 / 1000000000) (Real.log (167689 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (167689 / 125000) = -Real.log (125000 / 167689) := by
    rw [show ((167689 / 125000) : ℝ) = ((125000 / 167689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (417808981 / 1000000000) ≤ -Real.log (82311 / 125000) ∧
    -Real.log (82311 / 125000) ≤ (208904491 / 500000000) := by
  have h := checkLog_sound (w := (42689 / 207311)) (n := 12)
    (lo := (417808981 / 1000000000)) (hi := (208904491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 82311) = 1/(82311 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-208904491 / 500000000) (-417808981 / 1000000000) (Real.log (82311 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (55626837 / 250000000) ≤ -Real.log (200000 / 249841) ∧
    -Real.log (200000 / 249841) ≤ (222507349 / 1000000000) := by
  have h := checkLog_sound (w := (49841 / 449841)) (n := 12)
    (lo := (55626837 / 250000000)) (hi := (222507349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249841 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249841 / 200000) = 1/(200000 / 249841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (55626837 / 250000000) (222507349 / 1000000000) (Real.log (249841 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (249841 / 200000) = -Real.log (200000 / 249841) := by
    rw [show ((249841 / 200000) : ℝ) = ((200000 / 249841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (286622633 / 1000000000) ≤ -Real.log (150159 / 200000) ∧
    -Real.log (150159 / 200000) ≤ (143311317 / 500000000) := by
  have h := checkLog_sound (w := (49841 / 350159)) (n := 12)
    (lo := (286622633 / 1000000000)) (hi := (143311317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 150159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 150159) = 1/(150159 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-143311317 / 500000000) (-286622633 / 1000000000) (Real.log (150159 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (222775483 / 1000000000) ≤ -Real.log (50000 / 62477) ∧
    -Real.log (50000 / 62477) ≤ (55693871 / 250000000) := by
  have h := checkLog_sound (w := (12477 / 112477)) (n := 12)
    (lo := (222775483 / 1000000000)) (hi := (55693871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62477 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62477 / 50000) = 1/(50000 / 62477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (222775483 / 1000000000) (55693871 / 250000000) (Real.log (62477 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (62477 / 50000) = -Real.log (50000 / 62477) := by
    rw [show ((62477 / 50000) : ℝ) = ((50000 / 62477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (287068927 / 1000000000) ≤ -Real.log (37523 / 50000) ∧
    -Real.log (37523 / 50000) ≤ (1121363 / 3906250) := by
  have h := checkLog_sound (w := (12477 / 87523)) (n := 12)
    (lo := (287068927 / 1000000000)) (hi := (1121363 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37523) = 1/(37523 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1121363 / 3906250) (-287068927 / 1000000000) (Real.log (37523 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (177658799 / 250000000) ≤ -Real.log (250000000000 / 508820913711) ∧
    -Real.log (250000000000 / 508820913711) ≤ (355317599 / 500000000) := by
  have h := checkLog_sound (w := (8820913711 / 1008820913711)) (n := 12)
    (lo := (1093001 / 62500000)) (hi := (17488017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508820913711 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(508820913711 / 500000000000) = 1/(250000000000 / 508820913711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (177658799 / 250000000) (355317599 / 500000000) (Real.log (508820913711 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (508820913711 / 250000000000) = -Real.log (250000000000 / 508820913711) := by
    rw [show ((508820913711 / 250000000000) : ℝ) = ((250000000000 / 508820913711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (177901579 / 250000000) ≤ -Real.log (500000000000 / 1018630559707) ∧
    -Real.log (500000000000 / 1018630559707) ≤ (355803159 / 500000000) := by
  have h := checkLog_sound (w := (18630559707 / 2018630559707)) (n := 12)
    (lo := (36053 / 1953125)) (hi := (18459137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1018630559707 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1018630559707 / 1000000000000) = 1/(500000000000 / 1018630559707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (177901579 / 250000000) (355803159 / 500000000) (Real.log (1018630559707 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1018630559707 / 500000000000) = -Real.log (500000000000 / 1018630559707) := by
    rw [show ((1018630559707 / 500000000000) : ℝ) = ((500000000000 / 1018630559707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (254564991 / 500000000) ≤ -Real.log (250000000000 / 415960748273) ∧
    -Real.log (250000000000 / 415960748273) ≤ (509129983 / 1000000000) := by
  have h := checkLog_sound (w := (165960748273 / 665960748273)) (n := 12)
    (lo := (254564991 / 500000000)) (hi := (509129983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415960748273 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415960748273 / 250000000000) = 1/(250000000000 / 415960748273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (254564991 / 500000000) (509129983 / 1000000000) (Real.log (415960748273 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (415960748273 / 250000000000) = -Real.log (250000000000 / 415960748273) := by
    rw [show ((415960748273 / 250000000000) : ℝ) = ((250000000000 / 415960748273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (50984441 / 100000000) ≤ -Real.log (500000000000 / 832516056819) ∧
    -Real.log (500000000000 / 832516056819) ≤ (509844411 / 1000000000) := by
  have h := checkLog_sound (w := (332516056819 / 1332516056819)) (n := 12)
    (lo := (50984441 / 100000000)) (hi := (509844411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832516056819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832516056819 / 500000000000) = 1/(500000000000 / 832516056819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (50984441 / 100000000) (509844411 / 1000000000) (Real.log (832516056819 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (832516056819 / 500000000000) = -Real.log (500000000000 / 832516056819) := by
    rw [show ((832516056819 / 500000000000) : ℝ) = ((500000000000 / 832516056819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0341

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0342Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0342
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

theorem reflection_log_1_neg : (214039737 / 1000000000) ≤ -Real.log (2560 / 3171) ∧
    -Real.log (2560 / 3171) ≤ (107019869 / 500000000) := by
  have h := checkLog_sound (w := (611 / 5731)) (n := 12)
    (lo := (214039737 / 1000000000)) (hi := (107019869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3171 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3171 / 2560) = 1/(2560 / 3171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (214039737 / 1000000000) (107019869 / 500000000) (Real.log (3171 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3171 / 2560) = -Real.log (2560 / 3171) := by
    rw [show ((3171 / 2560) : ℝ) = ((2560 / 3171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (272690837 / 1000000000) ≤ -Real.log (1949 / 2560) ∧
    -Real.log (1949 / 2560) ≤ (136345419 / 500000000) := by
  have h := checkLog_sound (w := (611 / 4509)) (n := 12)
    (lo := (272690837 / 1000000000)) (hi := (136345419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1949) = 1/(1949 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-136345419 / 500000000) (-272690837 / 1000000000) (Real.log (1949 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21380319 / 100000000) ≤ -Real.log (10240 / 12681) ∧
    -Real.log (10240 / 12681) ≤ (213803191 / 1000000000) := by
  have h := checkLog_sound (w := (2441 / 22921)) (n := 12)
    (lo := (21380319 / 100000000)) (hi := (213803191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12681 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12681 / 10240) = 1/(10240 / 12681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21380319 / 100000000) (213803191 / 1000000000) (Real.log (12681 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12681 / 10240) = -Real.log (10240 / 12681) := by
    rw [show ((12681 / 10240) : ℝ) = ((10240 / 12681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (272306099 / 1000000000) ≤ -Real.log (7799 / 10240) ∧
    -Real.log (7799 / 10240) ≤ (2723061 / 10000000) := by
  have h := checkLog_sound (w := (2441 / 18039)) (n := 12)
    (lo := (272306099 / 1000000000)) (hi := (2723061 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7799) = 1/(7799 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2723061 / 10000000) (-272306099 / 1000000000) (Real.log (7799 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (390245711 / 1000000000) ≤ -Real.log (1280 / 1891) ∧
    -Real.log (1280 / 1891) ≤ (24390357 / 62500000) := by
  have h := checkLog_sound (w := (611 / 3171)) (n := 12)
    (lo := (390245711 / 1000000000)) (hi := (24390357 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1891 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1891 / 1280) = 1/(1280 / 1891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (390245711 / 1000000000) (24390357 / 62500000) (Real.log (1891 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1891 / 1280) = -Real.log (1280 / 1891) := by
    rw [show ((1891 / 1280) : ℝ) = ((1280 / 1891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10137989 / 15625000) ≤ -Real.log (669 / 1280) ∧
    -Real.log (669 / 1280) ≤ (648831297 / 1000000000) := by
  have h := checkLog_sound (w := (611 / 1949)) (n := 12)
    (lo := (10137989 / 15625000)) (hi := (648831297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 669) = 1/(669 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-648831297 / 1000000000) (-10137989 / 15625000) (Real.log (669 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (389849017 / 1000000000) ≤ -Real.log (5120 / 7561) ∧
    -Real.log (5120 / 7561) ≤ (194924509 / 500000000) := by
  have h := checkLog_sound (w := (2441 / 12681)) (n := 12)
    (lo := (389849017 / 1000000000)) (hi := (194924509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7561 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7561 / 5120) = 1/(5120 / 7561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (389849017 / 1000000000) (194924509 / 500000000) (Real.log (7561 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7561 / 5120) = -Real.log (5120 / 7561) := by
    rw [show ((7561 / 5120) : ℝ) = ((5120 / 7561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5060241 / 7812500) ≤ -Real.log (2679 / 5120) ∧
    -Real.log (2679 / 5120) ≤ (647710849 / 1000000000) := by
  have h := checkLog_sound (w := (2441 / 7799)) (n := 12)
    (lo := (5060241 / 7812500)) (hi := (647710849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2679) = 1/(2679 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-647710849 / 1000000000) (-5060241 / 7812500) (Real.log (2679 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2931583 / 10000000) ≤ -Real.log (200000 / 268131) ∧
    -Real.log (200000 / 268131) ≤ (293158301 / 1000000000) := by
  have h := checkLog_sound (w := (68131 / 468131)) (n := 12)
    (lo := (2931583 / 10000000)) (hi := (293158301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268131 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268131 / 200000) = 1/(200000 / 268131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2931583 / 10000000) (293158301 / 1000000000) (Real.log (268131 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (268131 / 200000) = -Real.log (200000 / 268131) := by
    rw [show ((268131 / 200000) : ℝ) = ((200000 / 268131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10412709 / 25000000) ≤ -Real.log (131869 / 200000) ∧
    -Real.log (131869 / 200000) ≤ (416508361 / 1000000000) := by
  have h := checkLog_sound (w := (68131 / 331869)) (n := 12)
    (lo := (10412709 / 25000000)) (hi := (416508361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 131869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 131869) = 1/(131869 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-416508361 / 1000000000) (-10412709 / 25000000) (Real.log (131869 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146739121 / 500000000) ≤ -Real.log (250000 / 335271) ∧
    -Real.log (250000 / 335271) ≤ (293478243 / 1000000000) := by
  have h := checkLog_sound (w := (85271 / 585271)) (n := 12)
    (lo := (146739121 / 500000000)) (hi := (293478243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335271 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335271 / 250000) = 1/(250000 / 335271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146739121 / 500000000) (293478243 / 1000000000) (Real.log (335271 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (335271 / 250000) = -Real.log (250000 / 335271) := by
    rw [show ((335271 / 250000) : ℝ) = ((250000 / 335271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (208579609 / 500000000) ≤ -Real.log (164729 / 250000) ∧
    -Real.log (164729 / 250000) ≤ (417159219 / 1000000000) := by
  have h := checkLog_sound (w := (85271 / 414729)) (n := 12)
    (lo := (208579609 / 500000000)) (hi := (417159219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 164729) = 1/(164729 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-417159219 / 1000000000) (-208579609 / 500000000) (Real.log (164729 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (222239943 / 1000000000) ≤ -Real.log (1000000 / 1248871) ∧
    -Real.log (1000000 / 1248871) ≤ (27779993 / 125000000) := by
  have h := checkLog_sound (w := (248871 / 2248871)) (n := 12)
    (lo := (222239943 / 1000000000)) (hi := (27779993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248871 / 1000000) = 1/(1000000 / 1248871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (222239943 / 1000000000) (27779993 / 125000000) (Real.log (1248871 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1248871 / 1000000) = -Real.log (1000000 / 1248871) := by
    rw [show ((1248871 / 1000000) : ℝ) = ((1000000 / 1248871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (28617787 / 100000000) ≤ -Real.log (751129 / 1000000) ∧
    -Real.log (751129 / 1000000) ≤ (286177871 / 1000000000) := by
  have h := checkLog_sound (w := (248871 / 1751129)) (n := 12)
    (lo := (28617787 / 100000000)) (hi := (286177871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 751129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 751129) = 1/(751129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-286177871 / 1000000000) (-28617787 / 100000000) (Real.log (751129 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (222508149 / 1000000000) ≤ -Real.log (500000 / 624603) ∧
    -Real.log (500000 / 624603) ≤ (4450163 / 20000000) := by
  have h := checkLog_sound (w := (124603 / 1124603)) (n := 12)
    (lo := (222508149 / 1000000000)) (hi := (4450163 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624603 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624603 / 500000) = 1/(500000 / 624603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (222508149 / 1000000000) (4450163 / 20000000) (Real.log (624603 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (624603 / 500000) = -Real.log (500000 / 624603) := by
    rw [show ((624603 / 500000) : ℝ) = ((500000 / 624603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57324793 / 200000000) ≤ -Real.log (375397 / 500000) ∧
    -Real.log (375397 / 500000) ≤ (143311983 / 500000000) := by
  have h := checkLog_sound (w := (124603 / 875397)) (n := 12)
    (lo := (57324793 / 200000000)) (hi := (143311983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375397) = 1/(375397 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-143311983 / 500000000) (-57324793 / 200000000) (Real.log (375397 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (35483333 / 50000000) ≤ -Real.log (50000000000 / 101665668201) ∧
    -Real.log (50000000000 / 101665668201) ≤ (354833331 / 500000000) := by
  have h := checkLog_sound (w := (1665668201 / 201665668201)) (n := 12)
    (lo := (412987 / 25000000)) (hi := (16519481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101665668201 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(101665668201 / 100000000000) = 1/(50000000000 / 101665668201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (35483333 / 50000000) (354833331 / 500000000) (Real.log (101665668201 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (101665668201 / 50000000000) = -Real.log (50000000000 / 101665668201) := by
    rw [show ((101665668201 / 50000000000) : ℝ) = ((50000000000 / 101665668201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (35531873 / 50000000) ≤ -Real.log (62500000000 / 127205516333) ∧
    -Real.log (62500000000 / 127205516333) ≤ (355318731 / 500000000) := by
  have h := checkLog_sound (w := (2205516333 / 252205516333)) (n := 12)
    (lo := (437257 / 25000000)) (hi := (17490281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127205516333 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(127205516333 / 125000000000) = 1/(62500000000 / 127205516333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (35531873 / 50000000) (355318731 / 500000000) (Real.log (127205516333 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (127205516333 / 62500000000) = -Real.log (62500000000 / 127205516333) := by
    rw [show ((127205516333 / 62500000000) : ℝ) = ((62500000000 / 127205516333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (254208907 / 500000000) ≤ -Real.log (125000000000 / 207832309763) ∧
    -Real.log (125000000000 / 207832309763) ≤ (101683563 / 200000000) := by
  have h := checkLog_sound (w := (82832309763 / 332832309763)) (n := 12)
    (lo := (254208907 / 500000000)) (hi := (101683563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207832309763 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207832309763 / 125000000000) = 1/(125000000000 / 207832309763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (254208907 / 500000000) (101683563 / 200000000) (Real.log (207832309763 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (207832309763 / 125000000000) = -Real.log (125000000000 / 207832309763) := by
    rw [show ((207832309763 / 125000000000) : ℝ) = ((125000000000 / 207832309763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (101826423 / 200000000) ≤ -Real.log (100000000000 / 166384654113) ∧
    -Real.log (100000000000 / 166384654113) ≤ (127283029 / 250000000) := by
  have h := checkLog_sound (w := (66384654113 / 266384654113)) (n := 12)
    (lo := (101826423 / 200000000)) (hi := (127283029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166384654113 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166384654113 / 100000000000) = 1/(100000000000 / 166384654113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (101826423 / 200000000) (127283029 / 250000000) (Real.log (166384654113 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (166384654113 / 100000000000) = -Real.log (100000000000 / 166384654113) := by
    rw [show ((166384654113 / 100000000000) : ℝ) = ((100000000000 / 166384654113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0342

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0343Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0343
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

theorem reflection_log_1_neg : (21380319 / 100000000) ≤ -Real.log (10240 / 12681) ∧
    -Real.log (10240 / 12681) ≤ (213803191 / 1000000000) := by
  have h := checkLog_sound (w := (2441 / 22921)) (n := 12)
    (lo := (21380319 / 100000000)) (hi := (213803191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12681 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12681 / 10240) = 1/(10240 / 12681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21380319 / 100000000) (213803191 / 1000000000) (Real.log (12681 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12681 / 10240) = -Real.log (10240 / 12681) := by
    rw [show ((12681 / 10240) : ℝ) = ((10240 / 12681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (272306099 / 1000000000) ≤ -Real.log (7799 / 10240) ∧
    -Real.log (7799 / 10240) ≤ (2723061 / 10000000) := by
  have h := checkLog_sound (w := (2441 / 18039)) (n := 12)
    (lo := (272306099 / 1000000000)) (hi := (2723061 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7799) = 1/(7799 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2723061 / 10000000) (-272306099 / 1000000000) (Real.log (7799 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (53391647 / 250000000) ≤ -Real.log (5120 / 6339) ∧
    -Real.log (5120 / 6339) ≤ (213566589 / 1000000000) := by
  have h := checkLog_sound (w := (1219 / 11459)) (n := 12)
    (lo := (53391647 / 250000000)) (hi := (213566589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6339 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6339 / 5120) = 1/(5120 / 6339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (53391647 / 250000000) (213566589 / 1000000000) (Real.log (6339 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6339 / 5120) = -Real.log (5120 / 6339) := by
    rw [show ((6339 / 5120) : ℝ) = ((5120 / 6339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (67980377 / 250000000) ≤ -Real.log (3901 / 5120) ∧
    -Real.log (3901 / 5120) ≤ (271921509 / 1000000000) := by
  have h := checkLog_sound (w := (1219 / 9021)) (n := 12)
    (lo := (67980377 / 250000000)) (hi := (271921509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3901) = 1/(3901 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-271921509 / 1000000000) (-67980377 / 250000000) (Real.log (3901 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (389849017 / 1000000000) ≤ -Real.log (5120 / 7561) ∧
    -Real.log (5120 / 7561) ≤ (194924509 / 500000000) := by
  have h := checkLog_sound (w := (2441 / 12681)) (n := 12)
    (lo := (389849017 / 1000000000)) (hi := (194924509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7561 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7561 / 5120) = 1/(5120 / 7561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (389849017 / 1000000000) (194924509 / 500000000) (Real.log (7561 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7561 / 5120) = -Real.log (5120 / 7561) := by
    rw [show ((7561 / 5120) : ℝ) = ((5120 / 7561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5060241 / 7812500) ≤ -Real.log (2679 / 5120) ∧
    -Real.log (2679 / 5120) ≤ (647710849 / 1000000000) := by
  have h := checkLog_sound (w := (2441 / 7799)) (n := 12)
    (lo := (5060241 / 7812500)) (hi := (647710849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2679) = 1/(2679 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-647710849 / 1000000000) (-5060241 / 7812500) (Real.log (2679 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77890433 / 200000000) ≤ -Real.log (2560 / 3779) ∧
    -Real.log (2560 / 3779) ≤ (194726083 / 500000000) := by
  have h := checkLog_sound (w := (1219 / 6339)) (n := 12)
    (lo := (77890433 / 200000000)) (hi := (194726083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3779 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3779 / 2560) = 1/(2560 / 3779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77890433 / 200000000) (194726083 / 500000000) (Real.log (3779 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3779 / 2560) = -Real.log (2560 / 3779) := by
    rw [show ((3779 / 2560) : ℝ) = ((2560 / 3779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (323295827 / 500000000) ≤ -Real.log (1341 / 2560) ∧
    -Real.log (1341 / 2560) ≤ (129318331 / 200000000) := by
  have h := checkLog_sound (w := (1219 / 3901)) (n := 12)
    (lo := (323295827 / 500000000)) (hi := (129318331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1341) = 1/(1341 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-129318331 / 200000000) (-323295827 / 500000000) (Real.log (1341 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18302391 / 62500000) ≤ -Real.log (500000 / 670113) ∧
    -Real.log (500000 / 670113) ≤ (292838257 / 1000000000) := by
  have h := checkLog_sound (w := (170113 / 1170113)) (n := 12)
    (lo := (18302391 / 62500000)) (hi := (292838257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670113 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670113 / 500000) = 1/(500000 / 670113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18302391 / 62500000) (292838257 / 1000000000) (Real.log (670113 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (670113 / 500000) = -Real.log (500000 / 670113) := by
    rw [show ((670113 / 500000) : ℝ) = ((500000 / 670113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (207928963 / 500000000) ≤ -Real.log (329887 / 500000) ∧
    -Real.log (329887 / 500000) ≤ (415857927 / 1000000000) := by
  have h := checkLog_sound (w := (170113 / 829887)) (n := 12)
    (lo := (207928963 / 500000000)) (hi := (415857927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 329887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 329887) = 1/(329887 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-415857927 / 1000000000) (-207928963 / 500000000) (Real.log (329887 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146579523 / 500000000) ≤ -Real.log (62500 / 83791) ∧
    -Real.log (62500 / 83791) ≤ (293159047 / 1000000000) := by
  have h := checkLog_sound (w := (21291 / 146291)) (n := 12)
    (lo := (146579523 / 500000000)) (hi := (293159047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83791 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83791 / 62500) = 1/(62500 / 83791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146579523 / 500000000) (293159047 / 1000000000) (Real.log (83791 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (83791 / 62500) = -Real.log (62500 / 83791) := by
    rw [show ((83791 / 62500) : ℝ) = ((62500 / 83791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (416509877 / 1000000000) ≤ -Real.log (41209 / 62500) ∧
    -Real.log (41209 / 62500) ≤ (208254939 / 500000000) := by
  have h := checkLog_sound (w := (21291 / 103709)) (n := 12)
    (lo := (416509877 / 1000000000)) (hi := (208254939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 41209) = 1/(41209 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-208254939 / 500000000) (-416509877 / 1000000000) (Real.log (41209 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (110986633 / 500000000) ≤ -Real.log (500000 / 624269) ∧
    -Real.log (500000 / 624269) ≤ (221973267 / 1000000000) := by
  have h := checkLog_sound (w := (124269 / 1124269)) (n := 12)
    (lo := (110986633 / 500000000)) (hi := (221973267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624269 / 500000) = 1/(500000 / 624269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (110986633 / 500000000) (221973267 / 1000000000) (Real.log (624269 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (624269 / 500000) = -Real.log (500000 / 624269) := by
    rw [show ((624269 / 500000) : ℝ) = ((500000 / 624269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (71433659 / 250000000) ≤ -Real.log (375731 / 500000) ∧
    -Real.log (375731 / 500000) ≤ (285734637 / 1000000000) := by
  have h := checkLog_sound (w := (124269 / 875731)) (n := 12)
    (lo := (71433659 / 250000000)) (hi := (285734637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375731) = 1/(375731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-285734637 / 1000000000) (-71433659 / 250000000) (Real.log (375731 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (222240743 / 1000000000) ≤ -Real.log (125000 / 156109) ∧
    -Real.log (125000 / 156109) ≤ (27780093 / 125000000) := by
  have h := checkLog_sound (w := (31109 / 281109)) (n := 12)
    (lo := (222240743 / 1000000000)) (hi := (27780093 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156109 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156109 / 125000) = 1/(125000 / 156109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (222240743 / 1000000000) (27780093 / 125000000) (Real.log (156109 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (156109 / 125000) = -Real.log (125000 / 156109) := by
    rw [show ((156109 / 125000) : ℝ) = ((125000 / 156109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (143089601 / 500000000) ≤ -Real.log (93891 / 125000) ∧
    -Real.log (93891 / 125000) ≤ (286179203 / 1000000000) := by
  have h := checkLog_sound (w := (31109 / 218891)) (n := 12)
    (lo := (143089601 / 500000000)) (hi := (286179203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 93891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 93891) = 1/(93891 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-286179203 / 1000000000) (-143089601 / 500000000) (Real.log (93891 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (354348091 / 500000000) ≤ -Real.log (12500000000 / 25391762937) ∧
    -Real.log (12500000000 / 25391762937) ≤ (88587023 / 125000000) := by
  have h := checkLog_sound (w := (391762937 / 50391762937)) (n := 12)
    (lo := (7774501 / 500000000)) (hi := (15549003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25391762937 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25391762937 / 25000000000) = 1/(12500000000 / 25391762937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (354348091 / 500000000) (88587023 / 125000000) (Real.log (25391762937 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (25391762937 / 12500000000) = -Real.log (12500000000 / 25391762937) := by
    rw [show ((25391762937 / 12500000000) : ℝ) = ((12500000000 / 25391762937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (709668923 / 1000000000) ≤ -Real.log (250000000000 / 508329491131) ∧
    -Real.log (250000000000 / 508329491131) ≤ (28386757 / 40000000) := by
  have h := checkLog_sound (w := (8329491131 / 1008329491131)) (n := 12)
    (lo := (16521743 / 1000000000)) (hi := (1032609 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508329491131 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(508329491131 / 500000000000) = 1/(250000000000 / 508329491131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (709668923 / 1000000000) (28386757 / 40000000) (Real.log (508329491131 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (508329491131 / 250000000000) = -Real.log (250000000000 / 508329491131) := by
    rw [show ((508329491131 / 250000000000) : ℝ) = ((250000000000 / 508329491131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (507707903 / 1000000000) ≤ -Real.log (250000000000 / 415369639449) ∧
    -Real.log (250000000000 / 415369639449) ≤ (991617 / 1953125) := by
  have h := checkLog_sound (w := (165369639449 / 665369639449)) (n := 12)
    (lo := (507707903 / 1000000000)) (hi := (991617 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415369639449 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415369639449 / 250000000000) = 1/(250000000000 / 415369639449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (507707903 / 1000000000) (991617 / 1953125) (Real.log (415369639449 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (415369639449 / 250000000000) = -Real.log (250000000000 / 415369639449) := by
    rw [show ((415369639449 / 250000000000) : ℝ) = ((250000000000 / 415369639449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (254209973 / 500000000) ≤ -Real.log (500000000000 / 831331011493) ∧
    -Real.log (500000000000 / 831331011493) ≤ (508419947 / 1000000000) := by
  have h := checkLog_sound (w := (331331011493 / 1331331011493)) (n := 12)
    (lo := (254209973 / 500000000)) (hi := (508419947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831331011493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831331011493 / 500000000000) = 1/(500000000000 / 831331011493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (254209973 / 500000000) (508419947 / 1000000000) (Real.log (831331011493 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (831331011493 / 500000000000) = -Real.log (500000000000 / 831331011493) := by
    rw [show ((831331011493 / 500000000000) : ℝ) = ((500000000000 / 831331011493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0343

end


