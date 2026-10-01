-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0060Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0060Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:28:00.689224+00:00
-- url     : https://prove2.me/theorems/54d208a3-d6f7-4d23-b9ec-cb15a3c1a460
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0060Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0061Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0060Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0061Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0062Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0063Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0064Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0065Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0060Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0061Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0062Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0063Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0064Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0065Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0060Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0061Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0062Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0063Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0064Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0065Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0060Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0061Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0062Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0063Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0064Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0065Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0060Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0060
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

theorem reflection_log_1_neg : (366431877 / 1000000000) ≤ -Real.log (2560 / 3693) ∧
    -Real.log (2560 / 3693) ≤ (183215939 / 500000000) := by
  have h := checkLog_sound (w := (1133 / 6253)) (n := 12)
    (lo := (366431877 / 1000000000)) (hi := (183215939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3693 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3693 / 2560) = 1/(2560 / 3693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (366431877 / 1000000000) (183215939 / 500000000) (Real.log (3693 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3693 / 2560) = -Real.log (2560 / 3693) := by
    rw [show ((3693 / 2560) : ℝ) = ((2560 / 3693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (584432919 / 1000000000) ≤ -Real.log (1427 / 2560) ∧
    -Real.log (1427 / 2560) ≤ (14610823 / 25000000) := by
  have h := checkLog_sound (w := (1133 / 3987)) (n := 12)
    (lo := (584432919 / 1000000000)) (hi := (14610823 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1427) = 1/(1427 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14610823 / 25000000) (-584432919 / 1000000000) (Real.log (1427 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (365619199 / 1000000000) ≤ -Real.log (256 / 369) ∧
    -Real.log (256 / 369) ≤ (28564 / 78125) := by
  have h := checkLog_sound (w := (113 / 625)) (n := 12)
    (lo := (365619199 / 1000000000)) (hi := (28564 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 256) = 1/(256 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (365619199 / 1000000000) (28564 / 78125) (Real.log (369 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (369 / 256) = -Real.log (256 / 369) := by
    rw [show ((369 / 256) : ℝ) = ((256 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (291166407 / 500000000) ≤ -Real.log (143 / 256) ∧
    -Real.log (143 / 256) ≤ (116466563 / 200000000) := by
  have h := checkLog_sound (w := (113 / 399)) (n := 12)
    (lo := (291166407 / 500000000)) (hi := (116466563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 143) = 1/(143 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-116466563 / 200000000) (-291166407 / 500000000) (Real.log (143 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (158502677 / 250000000) ≤ -Real.log (1280 / 2413) ∧
    -Real.log (1280 / 2413) ≤ (634010709 / 1000000000) := by
  have h := checkLog_sound (w := (1133 / 3693)) (n := 12)
    (lo := (158502677 / 250000000)) (hi := (634010709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2413 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2413 / 1280) = 1/(1280 / 2413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (158502677 / 250000000) (634010709 / 1000000000) (Real.log (2413 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2413 / 1280) = -Real.log (1280 / 2413) := by
    rw [show ((2413 / 1280) : ℝ) = ((1280 / 2413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (135261423 / 62500000) ≤ -Real.log (147 / 1280) ∧
    -Real.log (147 / 1280) ≤ (541045693 / 250000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 147) = 1/(147 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-541045693 / 250000000) (-135261423 / 62500000) (Real.log (147 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (632766669 / 1000000000) ≤ -Real.log (128 / 241) ∧
    -Real.log (128 / 241) ≤ (63276667 / 100000000) := by
  have h := checkLog_sound (w := (113 / 369)) (n := 12)
    (lo := (632766669 / 1000000000)) (hi := (63276667 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 128) = 1/(128 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (632766669 / 1000000000) (63276667 / 100000000) (Real.log (241 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (241 / 128) = -Real.log (128 / 241) := by
    rw [show ((241 / 128) : ℝ) = ((128 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2143980061 / 1000000000) ≤ -Real.log (15 / 128) ∧
    -Real.log (15 / 128) ≤ (428796013 / 200000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 15) = 1/(15 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-428796013 / 200000000) (-2143980061 / 1000000000) (Real.log (15 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252558983 / 500000000) ≤ -Real.log (1000000 / 1657181) ∧
    -Real.log (1000000 / 1657181) ≤ (505117967 / 1000000000) := by
  have h := checkLog_sound (w := (657181 / 2657181)) (n := 12)
    (lo := (252558983 / 500000000)) (hi := (505117967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1657181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1657181 / 1000000) = 1/(1000000 / 1657181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252558983 / 500000000) (505117967 / 1000000000) (Real.log (1657181 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1657181 / 1000000) = -Real.log (1000000 / 1657181) := by
    rw [show ((1657181 / 1000000) : ℝ) = ((1000000 / 1657181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1070552667 / 1000000000) ≤ -Real.log (342819 / 1000000) ∧
    -Real.log (342819 / 1000000) ≤ (1070552669 / 1000000000) := by
  have h := checkLog_sound (w := (157181 / 842819)) (n := 12)
    (lo := (377405487 / 1000000000)) (hi := (23587843 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342819) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 342819) = 1/(342819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1070552669 / 1000000000) (-1070552667 / 1000000000) (Real.log (342819 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (506365693 / 1000000000) ≤ -Real.log (4000 / 6637) ∧
    -Real.log (4000 / 6637) ≤ (253182847 / 500000000) := by
  have h := checkLog_sound (w := (2637 / 10637)) (n := 12)
    (lo := (506365693 / 1000000000)) (hi := (253182847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6637 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6637 / 4000) = 1/(4000 / 6637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (506365693 / 1000000000) (253182847 / 500000000) (Real.log (6637 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (6637 / 4000) = -Real.log (4000 / 6637) := by
    rw [show ((6637 / 4000) : ℝ) = ((4000 / 6637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1076606207 / 1000000000) ≤ -Real.log (1363 / 4000) ∧
    -Real.log (1363 / 4000) ≤ (1076606209 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 3363)) (n := 12)
    (lo := (383459027 / 1000000000)) (hi := (95864757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2000 / 1363) = 1/(1363 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1076606209 / 1000000000) (-1076606207 / 1000000000) (Real.log (1363 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (211665283 / 500000000) ≤ -Real.log (1000000 / 1527039) ∧
    -Real.log (1000000 / 1527039) ≤ (423330567 / 1000000000) := by
  have h := checkLog_sound (w := (527039 / 2527039)) (n := 12)
    (lo := (211665283 / 500000000)) (hi := (423330567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1527039 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1527039 / 1000000) = 1/(1000000 / 1527039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (211665283 / 500000000) (423330567 / 1000000000) (Real.log (1527039 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1527039 / 1000000) = -Real.log (1000000 / 1527039) := by
    rw [show ((1527039 / 1000000) : ℝ) = ((1000000 / 1527039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (149748469 / 200000000) ≤ -Real.log (472961 / 1000000) ∧
    -Real.log (472961 / 1000000) ≤ (748742347 / 1000000000) := by
  have h := checkLog_sound (w := (27039 / 972961)) (n := 12)
    (lo := (11119033 / 200000000)) (hi := (27797583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 472961) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 472961) = 1/(472961 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-748742347 / 1000000000) (-149748469 / 200000000) (Real.log (472961 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42470287 / 100000000) ≤ -Real.log (62500 / 95571) ∧
    -Real.log (62500 / 95571) ≤ (424702871 / 1000000000) := by
  have h := checkLog_sound (w := (33071 / 158071)) (n := 12)
    (lo := (42470287 / 100000000)) (hi := (424702871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95571 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95571 / 62500) = 1/(62500 / 95571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42470287 / 100000000) (424702871 / 1000000000) (Real.log (95571 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (95571 / 62500) = -Real.log (62500 / 95571) := by
    rw [show ((95571 / 62500) : ℝ) = ((62500 / 95571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (753185973 / 1000000000) ≤ -Real.log (29429 / 62500) ∧
    -Real.log (29429 / 62500) ≤ (30127439 / 40000000) := by
  have h := checkLog_sound (w := (1821 / 60679)) (n := 12)
    (lo := (60038793 / 1000000000)) (hi := (30019397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29429) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 29429) = 1/(29429 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-30127439 / 40000000) (-753185973 / 1000000000) (Real.log (29429 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (196958829 / 125000000) ≤ -Real.log (100000000000 / 483398236387) ∧
    -Real.log (100000000000 / 483398236387) ≤ (315134127 / 200000000) := by
  have h := checkLog_sound (w := (83398236387 / 883398236387)) (n := 12)
    (lo := (11836017 / 62500000)) (hi := (189376273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483398236387 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(483398236387 / 400000000000) = 1/(100000000000 / 483398236387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (196958829 / 125000000) (315134127 / 200000000) (Real.log (483398236387 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (483398236387 / 100000000000) = -Real.log (100000000000 / 483398236387) := by
    rw [show ((483398236387 / 100000000000) : ℝ) = ((100000000000 / 483398236387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (15829719 / 10000000) ≤ -Real.log (62500000000 / 304337857667) ∧
    -Real.log (62500000000 / 304337857667) ≤ (1582971903 / 1000000000) := by
  have h := checkLog_sound (w := (54337857667 / 554337857667)) (n := 12)
    (lo := (9833877 / 50000000)) (hi := (196677541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304337857667 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(304337857667 / 250000000000) = 1/(62500000000 / 304337857667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (15829719 / 10000000) (1582971903 / 1000000000) (Real.log (304337857667 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (304337857667 / 62500000000) = -Real.log (62500000000 / 304337857667) := by
    rw [show ((304337857667 / 62500000000) : ℝ) = ((62500000000 / 304337857667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1172072911 / 1000000000) ≤ -Real.log (500000000000 / 1614339237273) ∧
    -Real.log (500000000000 / 1614339237273) ≤ (1172072913 / 1000000000) := by
  have h := checkLog_sound (w := (614339237273 / 2614339237273)) (n := 12)
    (lo := (478925731 / 1000000000)) (hi := (119731433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1614339237273 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1614339237273 / 1000000000000) = 1/(500000000000 / 1614339237273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1172072911 / 1000000000) (1172072913 / 1000000000) (Real.log (1614339237273 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1614339237273 / 500000000000) = -Real.log (500000000000 / 1614339237273) := by
    rw [show ((1614339237273 / 500000000000) : ℝ) = ((500000000000 / 1614339237273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1177888843 / 1000000000) ≤ -Real.log (50000000000 / 162375547929) ∧
    -Real.log (50000000000 / 162375547929) ≤ (235577769 / 200000000) := by
  have h := checkLog_sound (w := (62375547929 / 262375547929)) (n := 12)
    (lo := (484741663 / 1000000000)) (hi := (15148177 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162375547929 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(162375547929 / 100000000000) = 1/(50000000000 / 162375547929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1177888843 / 1000000000) (235577769 / 200000000) (Real.log (162375547929 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (162375547929 / 50000000000) = -Real.log (50000000000 / 162375547929) := by
    rw [show ((162375547929 / 50000000000) : ℝ) = ((50000000000 / 162375547929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0060

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0061Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0061
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

theorem reflection_log_1_neg : (365619199 / 1000000000) ≤ -Real.log (256 / 369) ∧
    -Real.log (256 / 369) ≤ (28564 / 78125) := by
  have h := checkLog_sound (w := (113 / 625)) (n := 12)
    (lo := (365619199 / 1000000000)) (hi := (28564 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 256) = 1/(256 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (365619199 / 1000000000) (28564 / 78125) (Real.log (369 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (369 / 256) = -Real.log (256 / 369) := by
    rw [show ((369 / 256) : ℝ) = ((256 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (291166407 / 500000000) ≤ -Real.log (143 / 256) ∧
    -Real.log (143 / 256) ≤ (116466563 / 200000000) := by
  have h := checkLog_sound (w := (113 / 399)) (n := 12)
    (lo := (291166407 / 500000000)) (hi := (116466563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 143) = 1/(143 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-116466563 / 200000000) (-291166407 / 500000000) (Real.log (143 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (18240293 / 50000000) ≤ -Real.log (2560 / 3687) ∧
    -Real.log (2560 / 3687) ≤ (364805861 / 1000000000) := by
  have h := checkLog_sound (w := (1127 / 6247)) (n := 12)
    (lo := (18240293 / 50000000)) (hi := (364805861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3687 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3687 / 2560) = 1/(2560 / 3687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (18240293 / 50000000) (364805861 / 1000000000) (Real.log (3687 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3687 / 2560) = -Real.log (2560 / 3687) := by
    rw [show ((3687 / 2560) : ℝ) = ((2560 / 3687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (580237109 / 1000000000) ≤ -Real.log (1433 / 2560) ∧
    -Real.log (1433 / 2560) ≤ (58023711 / 100000000) := by
  have h := checkLog_sound (w := (1127 / 3993)) (n := 12)
    (lo := (580237109 / 1000000000)) (hi := (58023711 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1433) = 1/(1433 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58023711 / 100000000) (-580237109 / 1000000000) (Real.log (1433 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (632766669 / 1000000000) ≤ -Real.log (128 / 241) ∧
    -Real.log (128 / 241) ≤ (63276667 / 100000000) := by
  have h := checkLog_sound (w := (113 / 369)) (n := 12)
    (lo := (632766669 / 1000000000)) (hi := (63276667 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 128) = 1/(128 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (632766669 / 1000000000) (63276667 / 100000000) (Real.log (241 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (241 / 128) = -Real.log (128 / 241) := by
    rw [show ((241 / 128) : ℝ) = ((128 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2143980061 / 1000000000) ≤ -Real.log (15 / 128) ∧
    -Real.log (15 / 128) ≤ (428796013 / 200000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 15) = 1/(15 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-428796013 / 200000000) (-2143980061 / 1000000000) (Real.log (15 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15788027 / 25000000) ≤ -Real.log (1280 / 2407) ∧
    -Real.log (1280 / 2407) ≤ (631521081 / 1000000000) := by
  have h := checkLog_sound (w := (1127 / 3687)) (n := 12)
    (lo := (15788027 / 25000000)) (hi := (631521081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2407 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2407 / 1280) = 1/(1280 / 2407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15788027 / 25000000) (631521081 / 1000000000) (Real.log (2407 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2407 / 1280) = -Real.log (1280 / 2407) := by
    rw [show ((2407 / 1280) : ℝ) = ((1280 / 2407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2124177433 / 1000000000) ≤ -Real.log (153 / 1280) ∧
    -Real.log (153 / 1280) ≤ (2124177437 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 153) = 1/(153 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2124177437 / 1000000000) (-2124177433 / 1000000000) (Real.log (153 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (503872909 / 1000000000) ≤ -Real.log (1000000 / 1655119) ∧
    -Real.log (1000000 / 1655119) ≤ (50387291 / 100000000) := by
  have h := checkLog_sound (w := (655119 / 2655119)) (n := 12)
    (lo := (503872909 / 1000000000)) (hi := (50387291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1655119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1655119 / 1000000) = 1/(1000000 / 1655119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (503872909 / 1000000000) (50387291 / 100000000) (Real.log (1655119 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1655119 / 1000000) = -Real.log (1000000 / 1655119) := by
    rw [show ((1655119 / 1000000) : ℝ) = ((1000000 / 1655119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (133069481 / 125000000) ≤ -Real.log (344881 / 1000000) ∧
    -Real.log (344881 / 1000000) ≤ (21291117 / 20000000) := by
  have h := checkLog_sound (w := (155119 / 844881)) (n := 12)
    (lo := (92852167 / 250000000)) (hi := (371408669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344881) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 344881) = 1/(344881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21291117 / 20000000) (-133069481 / 125000000) (Real.log (344881 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (505118569 / 1000000000) ≤ -Real.log (500000 / 828591) ∧
    -Real.log (500000 / 828591) ≤ (50511857 / 100000000) := by
  have h := checkLog_sound (w := (328591 / 1328591)) (n := 12)
    (lo := (505118569 / 1000000000)) (hi := (50511857 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((828591 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(828591 / 500000) = 1/(500000 / 828591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (505118569 / 1000000000) (50511857 / 100000000) (Real.log (828591 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (828591 / 500000) = -Real.log (500000 / 828591) := by
    rw [show ((828591 / 500000) : ℝ) = ((500000 / 828591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (16727431 / 15625000) ≤ -Real.log (171409 / 500000) ∧
    -Real.log (171409 / 500000) ≤ (535277793 / 500000000) := by
  have h := checkLog_sound (w := (78591 / 421409)) (n := 12)
    (lo := (94352101 / 250000000)) (hi := (75481681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171409) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 171409) = 1/(171409 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-535277793 / 500000000) (-16727431 / 15625000) (Real.log (171409 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (84392849 / 200000000) ≤ -Real.log (500000 / 762477) ∧
    -Real.log (500000 / 762477) ≤ (210982123 / 500000000) := by
  have h := checkLog_sound (w := (262477 / 1262477)) (n := 12)
    (lo := (84392849 / 200000000)) (hi := (210982123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762477 / 500000) = 1/(500000 / 762477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (84392849 / 200000000) (210982123 / 500000000) (Real.log (762477 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (762477 / 500000) = -Real.log (500000 / 762477) := by
    rw [show ((762477 / 500000) : ℝ) = ((500000 / 762477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (186085909 / 250000000) ≤ -Real.log (237523 / 500000) ∧
    -Real.log (237523 / 500000) ≤ (372171819 / 500000000) := by
  have h := checkLog_sound (w := (12477 / 487523)) (n := 12)
    (lo := (6399557 / 125000000)) (hi := (51196457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 237523) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 237523) = 1/(237523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-372171819 / 500000000) (-186085909 / 250000000) (Real.log (237523 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (423331221 / 1000000000) ≤ -Real.log (3125 / 4772) ∧
    -Real.log (3125 / 4772) ≤ (211665611 / 500000000) := by
  have h := checkLog_sound (w := (1647 / 7897)) (n := 12)
    (lo := (423331221 / 1000000000)) (hi := (211665611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4772 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4772 / 3125) = 1/(3125 / 4772) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (423331221 / 1000000000) (211665611 / 500000000) (Real.log (4772 / 3125)) := by
  have h := reflection_log_15_neg
  have he : Real.log (4772 / 3125) = -Real.log (3125 / 4772) := by
    rw [show ((4772 / 3125) : ℝ) = ((3125 / 4772) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37437223 / 50000000) ≤ -Real.log (1478 / 3125) ∧
    -Real.log (1478 / 3125) ≤ (374372231 / 500000000) := by
  have h := checkLog_sound (w := (169 / 6081)) (n := 12)
    (lo := (347483 / 6250000)) (hi := (55597281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2956) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 2956) = 1/(1478 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-374372231 / 500000000) (-37437223 / 50000000) (Real.log (1478 / 3125)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1568428757 / 1000000000) ≤ -Real.log (500000000000 / 2399550859571) ∧
    -Real.log (500000000000 / 2399550859571) ≤ (39210719 / 25000000) := by
  have h := checkLog_sound (w := (399550859571 / 4399550859571)) (n := 12)
    (lo := (182134397 / 1000000000)) (hi := (91067199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2399550859571 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2399550859571 / 2000000000000) = 1/(500000000000 / 2399550859571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1568428757 / 1000000000) (39210719 / 25000000) (Real.log (2399550859571 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2399550859571 / 500000000000) = -Real.log (500000000000 / 2399550859571) := by
    rw [show ((2399550859571 / 500000000000) : ℝ) = ((500000000000 / 2399550859571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1575674153 / 1000000000) ≤ -Real.log (500000000000 / 2416999690799) ∧
    -Real.log (500000000000 / 2416999690799) ≤ (393918539 / 250000000) := by
  have h := checkLog_sound (w := (416999690799 / 4416999690799)) (n := 12)
    (lo := (189379793 / 1000000000)) (hi := (94689897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2416999690799 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2416999690799 / 2000000000000) = 1/(500000000000 / 2416999690799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1575674153 / 1000000000) (393918539 / 250000000) (Real.log (2416999690799 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2416999690799 / 500000000000) = -Real.log (500000000000 / 2416999690799) := by
    rw [show ((2416999690799 / 500000000000) : ℝ) = ((500000000000 / 2416999690799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (583153941 / 500000000) ≤ -Real.log (1562500000 / 5015810311) ∧
    -Real.log (1562500000 / 5015810311) ≤ (291576971 / 250000000) := by
  have h := checkLog_sound (w := (1890810311 / 8140810311)) (n := 12)
    (lo := (236580351 / 500000000)) (hi := (473160703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5015810311 / 3125000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5015810311 / 3125000000) = 1/(1562500000 / 5015810311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (583153941 / 500000000) (291576971 / 250000000) (Real.log (5015810311 / 1562500000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5015810311 / 1562500000) = -Real.log (1562500000 / 5015810311) := by
    rw [show ((5015810311 / 1562500000) : ℝ) = ((1562500000 / 5015810311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1172075681 / 1000000000) ≤ -Real.log (250000000000 / 807171853857) ∧
    -Real.log (250000000000 / 807171853857) ≤ (1172075683 / 1000000000) := by
  have h := checkLog_sound (w := (307171853857 / 1307171853857)) (n := 12)
    (lo := (478928501 / 1000000000)) (hi := (239464251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807171853857 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(807171853857 / 500000000000) = 1/(250000000000 / 807171853857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1172075681 / 1000000000) (1172075683 / 1000000000) (Real.log (807171853857 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (807171853857 / 250000000000) = -Real.log (250000000000 / 807171853857) := by
    rw [show ((807171853857 / 250000000000) : ℝ) = ((250000000000 / 807171853857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0061

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0062Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0062
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

theorem reflection_log_1_neg : (18240293 / 50000000) ≤ -Real.log (2560 / 3687) ∧
    -Real.log (2560 / 3687) ≤ (364805861 / 1000000000) := by
  have h := checkLog_sound (w := (1127 / 6247)) (n := 12)
    (lo := (18240293 / 50000000)) (hi := (364805861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3687 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3687 / 2560) = 1/(2560 / 3687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (18240293 / 50000000) (364805861 / 1000000000) (Real.log (3687 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3687 / 2560) = -Real.log (2560 / 3687) := by
    rw [show ((3687 / 2560) : ℝ) = ((2560 / 3687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (580237109 / 1000000000) ≤ -Real.log (1433 / 2560) ∧
    -Real.log (1433 / 2560) ≤ (58023711 / 100000000) := by
  have h := checkLog_sound (w := (1127 / 3993)) (n := 12)
    (lo := (580237109 / 1000000000)) (hi := (58023711 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1433) = 1/(1433 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58023711 / 100000000) (-580237109 / 1000000000) (Real.log (1433 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (363991859 / 1000000000) ≤ -Real.log (640 / 921) ∧
    -Real.log (640 / 921) ≤ (18199593 / 50000000) := by
  have h := checkLog_sound (w := (281 / 1561)) (n := 12)
    (lo := (363991859 / 1000000000)) (hi := (18199593 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921 / 640) = 1/(640 / 921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (363991859 / 1000000000) (18199593 / 50000000) (Real.log (921 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (921 / 640) = -Real.log (640 / 921) := by
    rw [show ((921 / 640) : ℝ) = ((640 / 921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (578145787 / 1000000000) ≤ -Real.log (359 / 640) ∧
    -Real.log (359 / 640) ≤ (144536447 / 250000000) := by
  have h := checkLog_sound (w := (281 / 999)) (n := 12)
    (lo := (578145787 / 1000000000)) (hi := (144536447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 359) = 1/(359 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-144536447 / 250000000) (-578145787 / 1000000000) (Real.log (359 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15788027 / 25000000) ≤ -Real.log (1280 / 2407) ∧
    -Real.log (1280 / 2407) ≤ (631521081 / 1000000000) := by
  have h := checkLog_sound (w := (1127 / 3687)) (n := 12)
    (lo := (15788027 / 25000000)) (hi := (631521081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2407 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2407 / 1280) = 1/(1280 / 2407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15788027 / 25000000) (631521081 / 1000000000) (Real.log (2407 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2407 / 1280) = -Real.log (1280 / 2407) := by
    rw [show ((2407 / 1280) : ℝ) = ((1280 / 2407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2124177433 / 1000000000) ≤ -Real.log (153 / 1280) ∧
    -Real.log (153 / 1280) ≤ (2124177437 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 153) = 1/(153 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2124177437 / 1000000000) (-2124177433 / 1000000000) (Real.log (153 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (315136969 / 500000000) ≤ -Real.log (320 / 601) ∧
    -Real.log (320 / 601) ≤ (630273939 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 921)) (n := 12)
    (lo := (315136969 / 500000000)) (hi := (630273939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601 / 320) = 1/(320 / 601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (315136969 / 500000000) (630273939 / 1000000000) (Real.log (601 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (601 / 320) = -Real.log (320 / 601) := by
    rw [show ((601 / 320) : ℝ) = ((320 / 601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2104759347 / 1000000000) ≤ -Real.log (39 / 320) ∧
    -Real.log (39 / 320) ≤ (2104759351 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 39) = 1/(39 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2104759351 / 1000000000) (-2104759347 / 1000000000) (Real.log (39 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (50262993 / 100000000) ≤ -Real.log (1000000 / 1653063) ∧
    -Real.log (1000000 / 1653063) ≤ (502629931 / 1000000000) := by
  have h := checkLog_sound (w := (653063 / 2653063)) (n := 12)
    (lo := (50262993 / 100000000)) (hi := (502629931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653063 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653063 / 1000000) = 1/(1000000 / 1653063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (50262993 / 100000000) (502629931 / 1000000000) (Real.log (1653063 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1653063 / 1000000) = -Real.log (1000000 / 1653063) := by
    rw [show ((1653063 / 1000000) : ℝ) = ((1000000 / 1653063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1058612071 / 1000000000) ≤ -Real.log (346937 / 1000000) ∧
    -Real.log (346937 / 1000000) ≤ (1058612073 / 1000000000) := by
  have h := checkLog_sound (w := (153063 / 846937)) (n := 12)
    (lo := (365464891 / 1000000000)) (hi := (91366223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346937) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 346937) = 1/(346937 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1058612073 / 1000000000) (-1058612071 / 1000000000) (Real.log (346937 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (503873513 / 1000000000) ≤ -Real.log (12500 / 20689) ∧
    -Real.log (12500 / 20689) ≤ (251936757 / 500000000) := by
  have h := checkLog_sound (w := (8189 / 33189)) (n := 12)
    (lo := (503873513 / 1000000000)) (hi := (251936757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20689 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20689 / 12500) = 1/(12500 / 20689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (503873513 / 1000000000) (251936757 / 500000000) (Real.log (20689 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (20689 / 12500) = -Real.log (12500 / 20689) := by
    rw [show ((20689 / 12500) : ℝ) = ((12500 / 20689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1064558747 / 1000000000) ≤ -Real.log (4311 / 12500) ∧
    -Real.log (4311 / 12500) ≤ (1064558749 / 1000000000) := by
  have h := checkLog_sound (w := (1939 / 10561)) (n := 12)
    (lo := (371411567 / 1000000000)) (hi := (23213223 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4311) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 4311) = 1/(4311 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1064558749 / 1000000000) (-1064558747 / 1000000000) (Real.log (4311 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (210301639 / 500000000) ≤ -Real.log (3125 / 4759) ∧
    -Real.log (3125 / 4759) ≤ (420603279 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 3942)) (n := 12)
    (lo := (210301639 / 500000000)) (hi := (420603279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4759 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4759 / 3125) = 1/(3125 / 4759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (210301639 / 500000000) (420603279 / 1000000000) (Real.log (4759 / 3125)) := by
  have h := reflection_log_13_neg
  have he : Real.log (4759 / 3125) = -Real.log (3125 / 4759) := by
    rw [show ((4759 / 3125) : ℝ) = ((3125 / 4759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (369993623 / 500000000) ≤ -Real.log (1491 / 3125) ∧
    -Real.log (1491 / 3125) ≤ (46249203 / 62500000) := by
  have h := checkLog_sound (w := (143 / 6107)) (n := 12)
    (lo := (23420033 / 500000000)) (hi := (46840067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2982) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 2982) = 1/(1491 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46249203 / 62500000) (-369993623 / 500000000) (Real.log (1491 / 3125)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (421964901 / 1000000000) ≤ -Real.log (200000 / 304991) ∧
    -Real.log (200000 / 304991) ≤ (210982451 / 500000000) := by
  have h := checkLog_sound (w := (104991 / 504991)) (n := 12)
    (lo := (421964901 / 1000000000)) (hi := (210982451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304991 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304991 / 200000) = 1/(200000 / 304991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (421964901 / 1000000000) (210982451 / 500000000) (Real.log (304991 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (304991 / 200000) = -Real.log (200000 / 304991) := by
    rw [show ((304991 / 200000) : ℝ) = ((200000 / 304991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (372172871 / 500000000) ≤ -Real.log (95009 / 200000) ∧
    -Real.log (95009 / 200000) ≤ (46521609 / 62500000) := by
  have h := checkLog_sound (w := (4991 / 195009)) (n := 12)
    (lo := (25599281 / 500000000)) (hi := (51198563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 95009) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 95009) = 1/(95009 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-46521609 / 62500000) (-372172871 / 500000000) (Real.log (95009 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1561242001 / 1000000000) ≤ -Real.log (500000000000 / 2382367692117) ∧
    -Real.log (500000000000 / 2382367692117) ≤ (390310501 / 250000000) := by
  have h := checkLog_sound (w := (382367692117 / 4382367692117)) (n := 12)
    (lo := (174947641 / 1000000000)) (hi := (87473821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2382367692117 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2382367692117 / 2000000000000) = 1/(500000000000 / 2382367692117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1561242001 / 1000000000) (390310501 / 250000000) (Real.log (2382367692117 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2382367692117 / 500000000000) = -Real.log (500000000000 / 2382367692117) := by
    rw [show ((2382367692117 / 500000000000) : ℝ) = ((500000000000 / 2382367692117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1568432261 / 1000000000) ≤ -Real.log (31250000000 / 149972454187) ∧
    -Real.log (31250000000 / 149972454187) ≤ (196054033 / 125000000) := by
  have h := checkLog_sound (w := (24972454187 / 274972454187)) (n := 12)
    (lo := (182137901 / 1000000000)) (hi := (91068951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149972454187 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(149972454187 / 125000000000) = 1/(31250000000 / 149972454187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1568432261 / 1000000000) (196054033 / 125000000) (Real.log (149972454187 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (149972454187 / 31250000000) = -Real.log (31250000000 / 149972454187) := by
    rw [show ((149972454187 / 31250000000) : ℝ) = ((31250000000 / 149972454187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (46423621 / 40000000) ≤ -Real.log (500000000000 / 1595908786049) ∧
    -Real.log (500000000000 / 1595908786049) ≤ (1160590527 / 1000000000) := by
  have h := checkLog_sound (w := (595908786049 / 2595908786049)) (n := 12)
    (lo := (93488669 / 200000000)) (hi := (233721673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1595908786049 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1595908786049 / 1000000000000) = 1/(500000000000 / 1595908786049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (46423621 / 40000000) (1160590527 / 1000000000) (Real.log (1595908786049 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1595908786049 / 500000000000) = -Real.log (500000000000 / 1595908786049) := by
    rw [show ((1595908786049 / 500000000000) : ℝ) = ((500000000000 / 1595908786049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1166310643 / 1000000000) ≤ -Real.log (100000000000 / 321012746161) ∧
    -Real.log (100000000000 / 321012746161) ≤ (233262129 / 200000000) := by
  have h := checkLog_sound (w := (121012746161 / 521012746161)) (n := 12)
    (lo := (473163463 / 1000000000)) (hi := (59145433 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321012746161 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(321012746161 / 200000000000) = 1/(100000000000 / 321012746161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1166310643 / 1000000000) (233262129 / 200000000) (Real.log (321012746161 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (321012746161 / 100000000000) = -Real.log (100000000000 / 321012746161) := by
    rw [show ((321012746161 / 100000000000) : ℝ) = ((100000000000 / 321012746161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0062

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0063Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0063
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

theorem reflection_log_1_neg : (363991859 / 1000000000) ≤ -Real.log (640 / 921) ∧
    -Real.log (640 / 921) ≤ (18199593 / 50000000) := by
  have h := checkLog_sound (w := (281 / 1561)) (n := 12)
    (lo := (363991859 / 1000000000)) (hi := (18199593 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921 / 640) = 1/(640 / 921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (363991859 / 1000000000) (18199593 / 50000000) (Real.log (921 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (921 / 640) = -Real.log (640 / 921) := by
    rw [show ((921 / 640) : ℝ) = ((640 / 921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (578145787 / 1000000000) ≤ -Real.log (359 / 640) ∧
    -Real.log (359 / 640) ≤ (144536447 / 250000000) := by
  have h := checkLog_sound (w := (281 / 999)) (n := 12)
    (lo := (578145787 / 1000000000)) (hi := (144536447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 359) = 1/(359 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-144536447 / 250000000) (-578145787 / 1000000000) (Real.log (359 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (72635439 / 200000000) ≤ -Real.log (2560 / 3681) ∧
    -Real.log (2560 / 3681) ≤ (90794299 / 250000000) := by
  have h := checkLog_sound (w := (1121 / 6241)) (n := 12)
    (lo := (72635439 / 200000000)) (hi := (90794299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3681 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3681 / 2560) = 1/(2560 / 3681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (72635439 / 200000000) (90794299 / 250000000) (Real.log (3681 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3681 / 2560) = -Real.log (2560 / 3681) := by
    rw [show ((3681 / 2560) : ℝ) = ((2560 / 3681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57605883 / 100000000) ≤ -Real.log (1439 / 2560) ∧
    -Real.log (1439 / 2560) ≤ (576058831 / 1000000000) := by
  have h := checkLog_sound (w := (1121 / 3999)) (n := 12)
    (lo := (57605883 / 100000000)) (hi := (576058831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1439) = 1/(1439 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-576058831 / 1000000000) (-57605883 / 100000000) (Real.log (1439 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (315136969 / 500000000) ≤ -Real.log (320 / 601) ∧
    -Real.log (320 / 601) ≤ (630273939 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 921)) (n := 12)
    (lo := (315136969 / 500000000)) (hi := (630273939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601 / 320) = 1/(320 / 601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (315136969 / 500000000) (630273939 / 1000000000) (Real.log (601 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (601 / 320) = -Real.log (320 / 601) := by
    rw [show ((601 / 320) : ℝ) = ((320 / 601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2104759347 / 1000000000) ≤ -Real.log (39 / 320) ∧
    -Real.log (39 / 320) ≤ (2104759351 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 39) = 1/(39 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2104759351 / 1000000000) (-2104759347 / 1000000000) (Real.log (39 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (629025239 / 1000000000) ≤ -Real.log (1280 / 2401) ∧
    -Real.log (1280 / 2401) ≤ (15725631 / 25000000) := by
  have h := checkLog_sound (w := (1121 / 3681)) (n := 12)
    (lo := (629025239 / 1000000000)) (hi := (15725631 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2401 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2401 / 1280) = 1/(1280 / 2401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (629025239 / 1000000000) (15725631 / 25000000) (Real.log (2401 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2401 / 1280) = -Real.log (1280 / 2401) := by
    rw [show ((2401 / 1280) : ℝ) = ((1280 / 2401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2085711153 / 1000000000) ≤ -Real.log (159 / 1280) ∧
    -Real.log (159 / 1280) ≤ (2085711157 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 159) = 1/(159 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2085711157 / 1000000000) (-2085711153 / 1000000000) (Real.log (159 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (250694519 / 500000000) ≤ -Real.log (1000000 / 1651013) ∧
    -Real.log (1000000 / 1651013) ≤ (501389039 / 1000000000) := by
  have h := checkLog_sound (w := (651013 / 2651013)) (n := 12)
    (lo := (250694519 / 500000000)) (hi := (501389039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651013 / 1000000) = 1/(1000000 / 1651013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (250694519 / 500000000) (501389039 / 1000000000) (Real.log (1651013 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1651013 / 1000000) = -Real.log (1000000 / 1651013) := by
    rw [show ((1651013 / 1000000) : ℝ) = ((1000000 / 1651013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (526360303 / 500000000) ≤ -Real.log (348987 / 1000000) ∧
    -Real.log (348987 / 1000000) ≤ (32897519 / 31250000) := by
  have h := checkLog_sound (w := (151013 / 848987)) (n := 12)
    (lo := (179786713 / 500000000)) (hi := (359573427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348987) = 1/(348987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-32897519 / 31250000) (-526360303 / 500000000) (Real.log (348987 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (100526107 / 200000000) ≤ -Real.log (125000 / 206633) ∧
    -Real.log (125000 / 206633) ≤ (62828817 / 125000000) := by
  have h := checkLog_sound (w := (81633 / 331633)) (n := 12)
    (lo := (100526107 / 200000000)) (hi := (62828817 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206633 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206633 / 125000) = 1/(125000 / 206633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (100526107 / 200000000) (62828817 / 125000000) (Real.log (206633 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (206633 / 125000) = -Real.log (125000 / 206633) := by
    rw [show ((206633 / 125000) : ℝ) = ((125000 / 206633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1058614953 / 1000000000) ≤ -Real.log (43367 / 125000) ∧
    -Real.log (43367 / 125000) ≤ (211722991 / 200000000) := by
  have h := checkLog_sound (w := (19133 / 105867)) (n := 12)
    (lo := (365467773 / 1000000000)) (hi := (182733887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43367) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 43367) = 1/(43367 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-211722991 / 200000000) (-1058614953 / 1000000000) (Real.log (43367 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52405879 / 125000000) ≤ -Real.log (62500 / 95051) ∧
    -Real.log (62500 / 95051) ≤ (419247033 / 1000000000) := by
  have h := checkLog_sound (w := (32551 / 157551)) (n := 12)
    (lo := (52405879 / 125000000)) (hi := (419247033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95051 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95051 / 62500) = 1/(62500 / 95051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52405879 / 125000000) (419247033 / 1000000000) (Real.log (95051 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (95051 / 62500) = -Real.log (62500 / 95051) := by
    rw [show ((95051 / 62500) : ℝ) = ((62500 / 95051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (735670621 / 1000000000) ≤ -Real.log (29949 / 62500) ∧
    -Real.log (29949 / 62500) ≤ (735670623 / 1000000000) := by
  have h := checkLog_sound (w := (1301 / 61199)) (n := 12)
    (lo := (42523441 / 1000000000)) (hi := (21261721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29949) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 29949) = 1/(29949 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-735670623 / 1000000000) (-735670621 / 1000000000) (Real.log (29949 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (84120787 / 200000000) ≤ -Real.log (1000000 / 1522881) ∧
    -Real.log (1000000 / 1522881) ≤ (13143873 / 31250000) := by
  have h := checkLog_sound (w := (522881 / 2522881)) (n := 12)
    (lo := (84120787 / 200000000)) (hi := (13143873 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1522881 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1522881 / 1000000) = 1/(1000000 / 1522881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (84120787 / 200000000) (13143873 / 31250000) (Real.log (1522881 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1522881 / 1000000) = -Real.log (1000000 / 1522881) := by
    rw [show ((1522881 / 1000000) : ℝ) = ((1000000 / 1522881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (369994671 / 500000000) ≤ -Real.log (477119 / 1000000) ∧
    -Real.log (477119 / 1000000) ≤ (23124667 / 31250000) := by
  have h := checkLog_sound (w := (22881 / 977119)) (n := 12)
    (lo := (23421081 / 500000000)) (hi := (46842163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 477119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 477119) = 1/(477119 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-23124667 / 31250000) (-369994671 / 500000000) (Real.log (477119 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (388527411 / 250000000) ≤ -Real.log (500000000000 / 2365436248341) ∧
    -Real.log (500000000000 / 2365436248341) ≤ (1554109647 / 1000000000) := by
  have h := checkLog_sound (w := (365436248341 / 4365436248341)) (n := 12)
    (lo := (41953821 / 250000000)) (hi := (33563057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2365436248341 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2365436248341 / 2000000000000) = 1/(500000000000 / 2365436248341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (388527411 / 250000000) (1554109647 / 1000000000) (Real.log (2365436248341 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2365436248341 / 500000000000) = -Real.log (500000000000 / 2365436248341) := by
    rw [show ((2365436248341 / 500000000000) : ℝ) = ((500000000000 / 2365436248341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (97577843 / 62500000) ≤ -Real.log (100000000000 / 476475200037) ∧
    -Real.log (100000000000 / 476475200037) ≤ (1561245491 / 1000000000) := by
  have h := checkLog_sound (w := (76475200037 / 876475200037)) (n := 12)
    (lo := (21868891 / 125000000)) (hi := (174951129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((476475200037 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(476475200037 / 400000000000) = 1/(100000000000 / 476475200037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (97577843 / 62500000) (1561245491 / 1000000000) (Real.log (476475200037 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (476475200037 / 100000000000) = -Real.log (100000000000 / 476475200037) := by
    rw [show ((476475200037 / 100000000000) : ℝ) = ((100000000000 / 476475200037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (577458827 / 500000000) ≤ -Real.log (250000000000 / 793440515543) ∧
    -Real.log (250000000000 / 793440515543) ≤ (144364707 / 125000000) := by
  have h := checkLog_sound (w := (293440515543 / 1293440515543)) (n := 12)
    (lo := (230885237 / 500000000)) (hi := (18470819 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793440515543 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(793440515543 / 500000000000) = 1/(250000000000 / 793440515543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (577458827 / 500000000) (144364707 / 125000000) (Real.log (793440515543 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (793440515543 / 250000000000) = -Real.log (250000000000 / 793440515543) := by
    rw [show ((793440515543 / 250000000000) : ℝ) = ((250000000000 / 793440515543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (580296639 / 500000000) ≤ -Real.log (500000000000 / 1595913178893) ∧
    -Real.log (500000000000 / 1595913178893) ≤ (1813427 / 1562500) := by
  have h := checkLog_sound (w := (595913178893 / 2595913178893)) (n := 12)
    (lo := (233723049 / 500000000)) (hi := (467446099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1595913178893 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1595913178893 / 1000000000000) = 1/(500000000000 / 1595913178893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (580296639 / 500000000) (1813427 / 1562500) (Real.log (1595913178893 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1595913178893 / 500000000000) = -Real.log (500000000000 / 1595913178893) := by
    rw [show ((1595913178893 / 500000000000) : ℝ) = ((500000000000 / 1595913178893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0063

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0064Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0064
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

theorem reflection_log_1_neg : (72635439 / 200000000) ≤ -Real.log (2560 / 3681) ∧
    -Real.log (2560 / 3681) ≤ (90794299 / 250000000) := by
  have h := checkLog_sound (w := (1121 / 6241)) (n := 12)
    (lo := (72635439 / 200000000)) (hi := (90794299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3681 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3681 / 2560) = 1/(2560 / 3681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (72635439 / 200000000) (90794299 / 250000000) (Real.log (3681 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3681 / 2560) = -Real.log (2560 / 3681) := by
    rw [show ((3681 / 2560) : ℝ) = ((2560 / 3681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57605883 / 100000000) ≤ -Real.log (1439 / 2560) ∧
    -Real.log (1439 / 2560) ≤ (576058831 / 1000000000) := by
  have h := checkLog_sound (w := (1121 / 3999)) (n := 12)
    (lo := (57605883 / 100000000)) (hi := (576058831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1439) = 1/(1439 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-576058831 / 1000000000) (-57605883 / 100000000) (Real.log (1439 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (362361867 / 1000000000) ≤ -Real.log (1280 / 1839) ∧
    -Real.log (1280 / 1839) ≤ (90590467 / 250000000) := by
  have h := checkLog_sound (w := (559 / 3119)) (n := 12)
    (lo := (362361867 / 1000000000)) (hi := (90590467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839 / 1280) = 1/(1280 / 1839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (362361867 / 1000000000) (90590467 / 250000000) (Real.log (1839 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1839 / 1280) = -Real.log (1280 / 1839) := by
    rw [show ((1839 / 1280) : ℝ) = ((1280 / 1839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (573976219 / 1000000000) ≤ -Real.log (721 / 1280) ∧
    -Real.log (721 / 1280) ≤ (28698811 / 50000000) := by
  have h := checkLog_sound (w := (559 / 2001)) (n := 12)
    (lo := (573976219 / 1000000000)) (hi := (28698811 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 721) = 1/(721 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-28698811 / 50000000) (-573976219 / 1000000000) (Real.log (721 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (629025239 / 1000000000) ≤ -Real.log (1280 / 2401) ∧
    -Real.log (1280 / 2401) ≤ (15725631 / 25000000) := by
  have h := checkLog_sound (w := (1121 / 3681)) (n := 12)
    (lo := (629025239 / 1000000000)) (hi := (15725631 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2401 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2401 / 1280) = 1/(1280 / 2401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (629025239 / 1000000000) (15725631 / 25000000) (Real.log (2401 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2401 / 1280) = -Real.log (1280 / 2401) := by
    rw [show ((2401 / 1280) : ℝ) = ((1280 / 2401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2085711153 / 1000000000) ≤ -Real.log (159 / 1280) ∧
    -Real.log (159 / 1280) ≤ (2085711157 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 159) = 1/(159 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2085711157 / 1000000000) (-2085711153 / 1000000000) (Real.log (159 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (313887489 / 500000000) ≤ -Real.log (640 / 1199) ∧
    -Real.log (640 / 1199) ≤ (627774979 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 1839)) (n := 12)
    (lo := (313887489 / 500000000)) (hi := (627774979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199 / 640) = 1/(640 / 1199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (313887489 / 500000000) (627774979 / 1000000000) (Real.log (1199 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1199 / 640) = -Real.log (640 / 1199) := by
    rw [show ((1199 / 640) : ℝ) = ((640 / 1199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (103350951 / 50000000) ≤ -Real.log (81 / 640) ∧
    -Real.log (81 / 640) ≤ (2067019023 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 81) = 1/(81 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2067019023 / 1000000000) (-103350951 / 50000000) (Real.log (81 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125037561 / 250000000) ≤ -Real.log (1000000 / 1648969) ∧
    -Real.log (1000000 / 1648969) ≤ (100030049 / 200000000) := by
  have h := checkLog_sound (w := (648969 / 2648969)) (n := 12)
    (lo := (125037561 / 250000000)) (hi := (100030049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1648969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1648969 / 1000000) = 1/(1000000 / 1648969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125037561 / 250000000) (100030049 / 200000000) (Real.log (1648969 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1648969 / 1000000) = -Real.log (1000000 / 1648969) := by
    rw [show ((1648969 / 1000000) : ℝ) = ((1000000 / 1648969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1046880739 / 1000000000) ≤ -Real.log (351031 / 1000000) ∧
    -Real.log (351031 / 1000000) ≤ (1046880741 / 1000000000) := by
  have h := checkLog_sound (w := (148969 / 851031)) (n := 12)
    (lo := (353733559 / 1000000000)) (hi := (8843339 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351031) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 351031) = 1/(351031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1046880741 / 1000000000) (-1046880739 / 1000000000) (Real.log (351031 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (125347411 / 250000000) ≤ -Real.log (500000 / 825507) ∧
    -Real.log (500000 / 825507) ≤ (100277929 / 200000000) := by
  have h := checkLog_sound (w := (325507 / 1325507)) (n := 12)
    (lo := (125347411 / 250000000)) (hi := (100277929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825507 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825507 / 500000) = 1/(500000 / 825507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (125347411 / 250000000) (100277929 / 200000000) (Real.log (825507 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (825507 / 500000) = -Real.log (500000 / 825507) := by
    rw [show ((825507 / 500000) : ℝ) = ((500000 / 825507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1052723471 / 1000000000) ≤ -Real.log (174493 / 500000) ∧
    -Real.log (174493 / 500000) ≤ (1052723473 / 1000000000) := by
  have h := checkLog_sound (w := (75507 / 424493)) (n := 12)
    (lo := (359576291 / 1000000000)) (hi := (89894073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174493) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 174493) = 1/(174493 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1052723473 / 1000000000) (-1052723471 / 1000000000) (Real.log (174493 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (417895529 / 1000000000) ≤ -Real.log (500000 / 759381) ∧
    -Real.log (500000 / 759381) ≤ (41789553 / 100000000) := by
  have h := checkLog_sound (w := (259381 / 1259381)) (n := 12)
    (lo := (417895529 / 1000000000)) (hi := (41789553 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759381 / 500000) = 1/(500000 / 759381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (417895529 / 1000000000) (41789553 / 100000000) (Real.log (759381 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (759381 / 500000) = -Real.log (500000 / 759381) := by
    rw [show ((759381 / 500000) : ℝ) = ((500000 / 759381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (45712083 / 62500000) ≤ -Real.log (240619 / 500000) ∧
    -Real.log (240619 / 500000) ≤ (73139333 / 100000000) := by
  have h := checkLog_sound (w := (9381 / 490619)) (n := 12)
    (lo := (9561537 / 250000000)) (hi := (38246149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 240619) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 240619) = 1/(240619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-73139333 / 100000000) (-45712083 / 62500000) (Real.log (240619 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (41924769 / 100000000) ≤ -Real.log (1000000 / 1520817) ∧
    -Real.log (1000000 / 1520817) ≤ (419247691 / 1000000000) := by
  have h := checkLog_sound (w := (520817 / 2520817)) (n := 12)
    (lo := (41924769 / 100000000)) (hi := (419247691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1520817 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1520817 / 1000000) = 1/(1000000 / 1520817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (41924769 / 100000000) (419247691 / 1000000000) (Real.log (1520817 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1520817 / 1000000) = -Real.log (1000000 / 1520817) := by
    rw [show ((1520817 / 1000000) : ℝ) = ((1000000 / 1520817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (183918177 / 250000000) ≤ -Real.log (479183 / 1000000) ∧
    -Real.log (479183 / 1000000) ≤ (73567271 / 100000000) := by
  have h := checkLog_sound (w := (20817 / 979183)) (n := 12)
    (lo := (5315691 / 125000000)) (hi := (42525529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 479183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 479183) = 1/(479183 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-73567271 / 100000000) (-183918177 / 250000000) (Real.log (479183 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1547030983 / 1000000000) ≤ -Real.log (500000000000 / 2348751249889) ∧
    -Real.log (500000000000 / 2348751249889) ≤ (773515493 / 500000000) := by
  have h := checkLog_sound (w := (348751249889 / 4348751249889)) (n := 12)
    (lo := (160736623 / 1000000000)) (hi := (10046039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2348751249889 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2348751249889 / 2000000000000) = 1/(500000000000 / 2348751249889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1547030983 / 1000000000) (773515493 / 500000000) (Real.log (2348751249889 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2348751249889 / 500000000000) = -Real.log (500000000000 / 2348751249889) := by
    rw [show ((2348751249889 / 500000000000) : ℝ) = ((500000000000 / 2348751249889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (310822623 / 200000000) ≤ -Real.log (500000000000 / 2365444459091) ∧
    -Real.log (500000000000 / 2365444459091) ≤ (777056559 / 500000000) := by
  have h := checkLog_sound (w := (365444459091 / 4365444459091)) (n := 12)
    (lo := (33563751 / 200000000)) (hi := (41954689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2365444459091 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2365444459091 / 2000000000000) = 1/(500000000000 / 2365444459091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (310822623 / 200000000) (777056559 / 500000000) (Real.log (2365444459091 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2365444459091 / 500000000000) = -Real.log (500000000000 / 2365444459091) := by
    rw [show ((2365444459091 / 500000000000) : ℝ) = ((500000000000 / 2365444459091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1149288857 / 1000000000) ≤ -Real.log (31250000000 / 98623368271) ∧
    -Real.log (31250000000 / 98623368271) ≤ (1149288859 / 1000000000) := by
  have h := checkLog_sound (w := (36123368271 / 161123368271)) (n := 12)
    (lo := (456141677 / 1000000000)) (hi := (228070839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98623368271 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(98623368271 / 62500000000) = 1/(31250000000 / 98623368271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1149288857 / 1000000000) (1149288859 / 1000000000) (Real.log (98623368271 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (98623368271 / 31250000000) = -Real.log (31250000000 / 98623368271) := by
    rw [show ((98623368271 / 31250000000) : ℝ) = ((31250000000 / 98623368271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (577460199 / 500000000) ≤ -Real.log (62500000000 / 198360673271) ∧
    -Real.log (62500000000 / 198360673271) ≤ (2887301 / 2500000) := by
  have h := checkLog_sound (w := (73360673271 / 323360673271)) (n := 12)
    (lo := (230886609 / 500000000)) (hi := (461773219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198360673271 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(198360673271 / 125000000000) = 1/(62500000000 / 198360673271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (577460199 / 500000000) (2887301 / 2500000) (Real.log (198360673271 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (198360673271 / 62500000000) = -Real.log (62500000000 / 198360673271) := by
    rw [show ((198360673271 / 62500000000) : ℝ) = ((62500000000 / 198360673271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0064

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0065Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0065
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

theorem reflection_log_1_neg : (362361867 / 1000000000) ≤ -Real.log (1280 / 1839) ∧
    -Real.log (1280 / 1839) ≤ (90590467 / 250000000) := by
  have h := checkLog_sound (w := (559 / 3119)) (n := 12)
    (lo := (362361867 / 1000000000)) (hi := (90590467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839 / 1280) = 1/(1280 / 1839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (362361867 / 1000000000) (90590467 / 250000000) (Real.log (1839 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1839 / 1280) = -Real.log (1280 / 1839) := by
    rw [show ((1839 / 1280) : ℝ) = ((1280 / 1839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (573976219 / 1000000000) ≤ -Real.log (721 / 1280) ∧
    -Real.log (721 / 1280) ≤ (28698811 / 50000000) := by
  have h := checkLog_sound (w := (559 / 2001)) (n := 12)
    (lo := (573976219 / 1000000000)) (hi := (28698811 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 721) = 1/(721 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-28698811 / 50000000) (-573976219 / 1000000000) (Real.log (721 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (180772937 / 500000000) ≤ -Real.log (512 / 735) ∧
    -Real.log (512 / 735) ≤ (2892367 / 8000000) := by
  have h := checkLog_sound (w := (223 / 1247)) (n := 12)
    (lo := (180772937 / 500000000)) (hi := (2892367 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735 / 512) = 1/(512 / 735) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (180772937 / 500000000) (2892367 / 8000000) (Real.log (735 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (735 / 512) = -Real.log (512 / 735) := by
    rw [show ((735 / 512) : ℝ) = ((512 / 735) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (35743621 / 62500000) ≤ -Real.log (289 / 512) ∧
    -Real.log (289 / 512) ≤ (571897937 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 801)) (n := 12)
    (lo := (35743621 / 62500000)) (hi := (571897937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 289) = 1/(289 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-571897937 / 1000000000) (-35743621 / 62500000) (Real.log (289 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (313887489 / 500000000) ≤ -Real.log (640 / 1199) ∧
    -Real.log (640 / 1199) ≤ (627774979 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 1839)) (n := 12)
    (lo := (313887489 / 500000000)) (hi := (627774979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199 / 640) = 1/(640 / 1199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (313887489 / 500000000) (627774979 / 1000000000) (Real.log (1199 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1199 / 640) = -Real.log (640 / 1199) := by
    rw [show ((1199 / 640) : ℝ) = ((640 / 1199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (103350951 / 50000000) ≤ -Real.log (81 / 640) ∧
    -Real.log (81 / 640) ≤ (2067019023 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 81) = 1/(81 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2067019023 / 1000000000) (-103350951 / 50000000) (Real.log (81 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39157697 / 62500000) ≤ -Real.log (256 / 479) ∧
    -Real.log (256 / 479) ≤ (626523153 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 735)) (n := 12)
    (lo := (39157697 / 62500000)) (hi := (626523153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479 / 256) = 1/(256 / 479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39157697 / 62500000) (626523153 / 1000000000) (Real.log (479 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (479 / 256) = -Real.log (256 / 479) := by
    rw [show ((479 / 256) : ℝ) = ((256 / 479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2048669881 / 1000000000) ≤ -Real.log (33 / 256) ∧
    -Real.log (33 / 256) ≤ (512167471 / 250000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 33) = 1/(33 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-512167471 / 250000000) (-2048669881 / 1000000000) (Real.log (33 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (124728237 / 250000000) ≤ -Real.log (100000 / 164693) ∧
    -Real.log (100000 / 164693) ≤ (498912949 / 1000000000) := by
  have h := checkLog_sound (w := (64693 / 264693)) (n := 12)
    (lo := (124728237 / 250000000)) (hi := (498912949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164693 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164693 / 100000) = 1/(100000 / 164693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (124728237 / 250000000) (498912949 / 1000000000) (Real.log (164693 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (164693 / 100000) = -Real.log (100000 / 164693) := by
    rw [show ((164693 / 100000) : ℝ) = ((100000 / 164693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52054447 / 50000000) ≤ -Real.log (35307 / 100000) ∧
    -Real.log (35307 / 100000) ≤ (520544471 / 500000000) := by
  have h := checkLog_sound (w := (14693 / 85307)) (n := 12)
    (lo := (543659 / 1562500)) (hi := (347941761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35307) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35307) = 1/(35307 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-520544471 / 500000000) (-52054447 / 50000000) (Real.log (35307 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10003017 / 20000000) ≤ -Real.log (100000 / 164897) ∧
    -Real.log (100000 / 164897) ≤ (500150851 / 1000000000) := by
  have h := checkLog_sound (w := (64897 / 264897)) (n := 12)
    (lo := (10003017 / 20000000)) (hi := (500150851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164897 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164897 / 100000) = 1/(100000 / 164897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10003017 / 20000000) (500150851 / 1000000000) (Real.log (164897 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (164897 / 100000) = -Real.log (100000 / 164897) := by
    rw [show ((164897 / 100000) : ℝ) = ((100000 / 164897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (261720897 / 250000000) ≤ -Real.log (35103 / 100000) ∧
    -Real.log (35103 / 100000) ≤ (104688359 / 100000000) := by
  have h := checkLog_sound (w := (14897 / 85103)) (n := 12)
    (lo := (44217051 / 125000000)) (hi := (353736409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35103) = 1/(35103 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-104688359 / 100000000) (-261720897 / 250000000) (Real.log (35103 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (416548789 / 1000000000) ≤ -Real.log (500000 / 758359) ∧
    -Real.log (500000 / 758359) ≤ (41654879 / 100000000) := by
  have h := checkLog_sound (w := (258359 / 1258359)) (n := 12)
    (lo := (416548789 / 1000000000)) (hi := (41654879 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758359 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758359 / 500000) = 1/(500000 / 758359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (416548789 / 1000000000) (41654879 / 100000000) (Real.log (758359 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (758359 / 500000) = -Real.log (500000 / 758359) := by
    rw [show ((758359 / 500000) : ℝ) = ((500000 / 758359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2840449 / 3906250) ≤ -Real.log (241641 / 500000) ∧
    -Real.log (241641 / 500000) ≤ (363577473 / 500000000) := by
  have h := checkLog_sound (w := (8359 / 491641)) (n := 12)
    (lo := (8501941 / 250000000)) (hi := (6801553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 241641) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 241641) = 1/(241641 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-363577473 / 500000000) (-2840449 / 3906250) (Real.log (241641 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (417896187 / 1000000000) ≤ -Real.log (1000000 / 1518763) ∧
    -Real.log (1000000 / 1518763) ≤ (104474047 / 250000000) := by
  have h := checkLog_sound (w := (518763 / 2518763)) (n := 12)
    (lo := (417896187 / 1000000000)) (hi := (104474047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1518763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1518763 / 1000000) = 1/(1000000 / 1518763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (417896187 / 1000000000) (104474047 / 250000000) (Real.log (1518763 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1518763 / 1000000) = -Real.log (1000000 / 1518763) := by
    rw [show ((1518763 / 1000000) : ℝ) = ((1000000 / 1518763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (365697703 / 500000000) ≤ -Real.log (481237 / 1000000) ∧
    -Real.log (481237 / 1000000) ≤ (45712213 / 62500000) := by
  have h := checkLog_sound (w := (18763 / 981237)) (n := 12)
    (lo := (19124113 / 500000000)) (hi := (38248227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 481237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 481237) = 1/(481237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-45712213 / 62500000) (-365697703 / 500000000) (Real.log (481237 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1540001889 / 1000000000) ≤ -Real.log (500000000000 / 2332299543999) ∧
    -Real.log (500000000000 / 2332299543999) ≤ (385000473 / 250000000) := by
  have h := checkLog_sound (w := (332299543999 / 4332299543999)) (n := 12)
    (lo := (153707529 / 1000000000)) (hi := (15370753 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2332299543999 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2332299543999 / 2000000000000) = 1/(500000000000 / 2332299543999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1540001889 / 1000000000) (385000473 / 250000000) (Real.log (2332299543999 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2332299543999 / 500000000000) = -Real.log (500000000000 / 2332299543999) := by
    rw [show ((2332299543999 / 500000000000) : ℝ) = ((500000000000 / 2332299543999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (773517219 / 500000000) ≤ -Real.log (500000000000 / 2348759365297) ∧
    -Real.log (500000000000 / 2348759365297) ≤ (1547034441 / 1000000000) := by
  have h := checkLog_sound (w := (348759365297 / 4348759365297)) (n := 12)
    (lo := (80370039 / 500000000)) (hi := (160740079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2348759365297 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2348759365297 / 2000000000000) = 1/(500000000000 / 2348759365297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (773517219 / 500000000) (1547034441 / 1000000000) (Real.log (2348759365297 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2348759365297 / 500000000000) = -Real.log (500000000000 / 2348759365297) := by
    rw [show ((2348759365297 / 500000000000) : ℝ) = ((500000000000 / 2348759365297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (571851867 / 500000000) ≤ -Real.log (125000000000 / 392296319747) ∧
    -Real.log (125000000000 / 392296319747) ≤ (142962967 / 125000000) := by
  have h := checkLog_sound (w := (142296319747 / 642296319747)) (n := 12)
    (lo := (225278277 / 500000000)) (hi := (90111311 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392296319747 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(392296319747 / 250000000000) = 1/(125000000000 / 392296319747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (571851867 / 500000000) (142962967 / 125000000) (Real.log (392296319747 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (392296319747 / 125000000000) = -Real.log (125000000000 / 392296319747) := by
    rw [show ((392296319747 / 125000000000) : ℝ) = ((125000000000 / 392296319747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1149291593 / 1000000000) ≤ -Real.log (500000000000 / 1577978210321) ∧
    -Real.log (500000000000 / 1577978210321) ≤ (229858319 / 200000000) := by
  have h := checkLog_sound (w := (577978210321 / 2577978210321)) (n := 12)
    (lo := (456144413 / 1000000000)) (hi := (228072207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1577978210321 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1577978210321 / 1000000000000) = 1/(500000000000 / 1577978210321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1149291593 / 1000000000) (229858319 / 200000000) (Real.log (1577978210321 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1577978210321 / 500000000000) = -Real.log (500000000000 / 1577978210321) := by
    rw [show ((1577978210321 / 500000000000) : ℝ) = ((500000000000 / 1577978210321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0065

end


