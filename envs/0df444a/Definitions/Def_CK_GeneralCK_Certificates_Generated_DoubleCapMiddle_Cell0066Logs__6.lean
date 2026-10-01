-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0066Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0066Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:02:03.902109+00:00
-- url     : https://prove2.me/theorems/df5245d6-d780-4310-8fab-ec895c15af39
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0066Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0066Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0068Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0069Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0070Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0071Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0066Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0068Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0069Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0070Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0071Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0066Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0068Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0069Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0070Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0071Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0066Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0067Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0068Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0069Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0070Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0071Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0066Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0066
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

theorem reflection_log_1_neg : (180772937 / 500000000) ≤ -Real.log (512 / 735) ∧
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


theorem reflection_log_1 : Bounds (180772937 / 500000000) (2892367 / 8000000) (Real.log (735 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (735 / 512) = -Real.log (512 / 735) := by
    rw [show ((735 / 512) : ℝ) = ((512 / 735) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (35743621 / 62500000) ≤ -Real.log (289 / 512) ∧
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


theorem reflection_log_2 : Bounds (-571897937 / 1000000000) (-35743621 / 62500000) (Real.log (289 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (180364607 / 500000000) ≤ -Real.log (320 / 459) ∧
    -Real.log (320 / 459) ≤ (72145843 / 200000000) := by
  have h := checkLog_sound (w := (139 / 779)) (n := 12)
    (lo := (180364607 / 500000000)) (hi := (72145843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((459 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(459 / 320) = 1/(320 / 459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (180364607 / 500000000) (72145843 / 200000000) (Real.log (459 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (459 / 320) = -Real.log (320 / 459) := by
    rw [show ((459 / 320) : ℝ) = ((320 / 459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (142455991 / 250000000) ≤ -Real.log (181 / 320) ∧
    -Real.log (181 / 320) ≤ (113964793 / 200000000) := by
  have h := checkLog_sound (w := (139 / 501)) (n := 12)
    (lo := (142455991 / 250000000)) (hi := (113964793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 181) = 1/(181 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-113964793 / 200000000) (-142455991 / 250000000) (Real.log (181 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (39157697 / 62500000) ≤ -Real.log (256 / 479) ∧
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


theorem reflection_log_5 : Bounds (39157697 / 62500000) (626523153 / 1000000000) (Real.log (479 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (479 / 256) = -Real.log (256 / 479) := by
    rw [show ((479 / 256) : ℝ) = ((256 / 479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2048669881 / 1000000000) ≤ -Real.log (33 / 256) ∧
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


theorem reflection_log_6 : Bounds (-512167471 / 250000000) (-2048669881 / 1000000000) (Real.log (33 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (312634879 / 500000000) ≤ -Real.log (160 / 299) ∧
    -Real.log (160 / 299) ≤ (625269759 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 459)) (n := 12)
    (lo := (312634879 / 500000000)) (hi := (625269759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299 / 160) = 1/(160 / 299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (312634879 / 500000000) (625269759 / 1000000000) (Real.log (299 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (299 / 160) = -Real.log (160 / 299) := by
    rw [show ((299 / 160) : ℝ) = ((160 / 299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126915711 / 62500000) ≤ -Real.log (21 / 160) ∧
    -Real.log (21 / 160) ≤ (2030651379 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 21) = 1/(21 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2030651379 / 1000000000) (-126915711 / 62500000) (Real.log (21 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62209721 / 125000000) ≤ -Real.log (1000000 / 1644897) ∧
    -Real.log (1000000 / 1644897) ≤ (497677769 / 1000000000) := by
  have h := checkLog_sound (w := (644897 / 2644897)) (n := 12)
    (lo := (62209721 / 125000000)) (hi := (497677769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1644897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1644897 / 1000000) = 1/(1000000 / 1644897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62209721 / 125000000) (497677769 / 1000000000) (Real.log (1644897 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1644897 / 1000000) = -Real.log (1000000 / 1644897) := by
    rw [show ((1644897 / 1000000) : ℝ) = ((1000000 / 1644897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (103534739 / 100000000) ≤ -Real.log (355103 / 1000000) ∧
    -Real.log (355103 / 1000000) ≤ (16177303 / 15625000) := by
  have h := checkLog_sound (w := (144897 / 855103)) (n := 12)
    (lo := (34220021 / 100000000)) (hi := (342200211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 355103) = 1/(355103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-16177303 / 15625000) (-103534739 / 100000000) (Real.log (355103 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (99782711 / 200000000) ≤ -Real.log (1000000 / 1646931) ∧
    -Real.log (1000000 / 1646931) ≤ (124728389 / 250000000) := by
  have h := checkLog_sound (w := (646931 / 2646931)) (n := 12)
    (lo := (99782711 / 200000000)) (hi := (124728389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1646931 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1646931 / 1000000) = 1/(1000000 / 1646931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (99782711 / 200000000) (124728389 / 250000000) (Real.log (1646931 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1646931 / 1000000) = -Real.log (1000000 / 1646931) := by
    rw [show ((1646931 / 1000000) : ℝ) = ((1000000 / 1646931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1041091773 / 1000000000) ≤ -Real.log (353069 / 1000000) ∧
    -Real.log (353069 / 1000000) ≤ (41643671 / 40000000) := by
  have h := checkLog_sound (w := (146931 / 853069)) (n := 12)
    (lo := (347944593 / 1000000000)) (hi := (173972297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 353069) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 353069) = 1/(353069 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-41643671 / 40000000) (-1041091773 / 1000000000) (Real.log (353069 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51900937 / 125000000) ≤ -Real.log (200000 / 302937) ∧
    -Real.log (200000 / 302937) ≤ (415207497 / 1000000000) := by
  have h := checkLog_sound (w := (102937 / 502937)) (n := 12)
    (lo := (51900937 / 125000000)) (hi := (415207497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302937 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302937 / 200000) = 1/(200000 / 302937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51900937 / 125000000) (415207497 / 1000000000) (Real.log (302937 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (302937 / 200000) = -Real.log (200000 / 302937) := by
    rw [show ((302937 / 200000) : ℝ) = ((200000 / 302937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (722957113 / 1000000000) ≤ -Real.log (97063 / 200000) ∧
    -Real.log (97063 / 200000) ≤ (144591423 / 200000000) := by
  have h := checkLog_sound (w := (2937 / 197063)) (n := 12)
    (lo := (29809933 / 1000000000)) (hi := (14904967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 97063) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 97063) = 1/(97063 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-144591423 / 200000000) (-722957113 / 1000000000) (Real.log (97063 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (416549449 / 1000000000) ≤ -Real.log (1000000 / 1516719) ∧
    -Real.log (1000000 / 1516719) ≤ (8330989 / 20000000) := by
  have h := checkLog_sound (w := (516719 / 2516719)) (n := 12)
    (lo := (416549449 / 1000000000)) (hi := (8330989 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1516719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1516719 / 1000000) = 1/(1000000 / 1516719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (416549449 / 1000000000) (8330989 / 20000000) (Real.log (1516719 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1516719 / 1000000) = -Real.log (1000000 / 1516719) := by
    rw [show ((1516719 / 1000000) : ℝ) = ((1000000 / 1516719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (727157013 / 1000000000) ≤ -Real.log (483281 / 1000000) ∧
    -Real.log (483281 / 1000000) ≤ (145431403 / 200000000) := by
  have h := checkLog_sound (w := (16719 / 983281)) (n := 12)
    (lo := (34009833 / 1000000000)) (hi := (17004917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 483281) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 483281) = 1/(483281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-145431403 / 200000000) (-727157013 / 1000000000) (Real.log (483281 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1533025157 / 1000000000) ≤ -Real.log (250000000000 / 1158042173679) ∧
    -Real.log (250000000000 / 1158042173679) ≤ (38325629 / 25000000) := by
  have h := checkLog_sound (w := (158042173679 / 2158042173679)) (n := 12)
    (lo := (146730797 / 1000000000)) (hi := (73365399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158042173679 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1158042173679 / 1000000000000) = 1/(250000000000 / 1158042173679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1533025157 / 1000000000) (38325629 / 25000000) (Real.log (1158042173679 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1158042173679 / 250000000000) = -Real.log (250000000000 / 1158042173679) := by
    rw [show ((1158042173679 / 250000000000) : ℝ) = ((250000000000 / 1158042173679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (96250333 / 62500000) ≤ -Real.log (62500000000 / 291538445743) ∧
    -Real.log (62500000000 / 291538445743) ≤ (1540005331 / 1000000000) := by
  have h := checkLog_sound (w := (41538445743 / 541538445743)) (n := 12)
    (lo := (19213871 / 125000000)) (hi := (153710969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291538445743 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(291538445743 / 250000000000) = 1/(62500000000 / 291538445743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (96250333 / 62500000) (1540005331 / 1000000000) (Real.log (291538445743 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (291538445743 / 62500000000) = -Real.log (62500000000 / 291538445743) := by
    rw [show ((291538445743 / 62500000000) : ℝ) = ((62500000000 / 291538445743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (113816461 / 100000000) ≤ -Real.log (250000000000 / 780258697959) ∧
    -Real.log (250000000000 / 780258697959) ≤ (284541153 / 250000000) := by
  have h := checkLog_sound (w := (280258697959 / 1280258697959)) (n := 12)
    (lo := (44501743 / 100000000)) (hi := (445017431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780258697959 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(780258697959 / 500000000000) = 1/(250000000000 / 780258697959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (113816461 / 100000000) (284541153 / 250000000) (Real.log (780258697959 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (780258697959 / 250000000000) = -Real.log (250000000000 / 780258697959) := by
    rw [show ((780258697959 / 250000000000) : ℝ) = ((250000000000 / 780258697959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (571853231 / 500000000) ≤ -Real.log (20000000000 / 62767582421) ∧
    -Real.log (20000000000 / 62767582421) ≤ (35740827 / 31250000) := by
  have h := checkLog_sound (w := (22767582421 / 102767582421)) (n := 12)
    (lo := (225279641 / 500000000)) (hi := (450559283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62767582421 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62767582421 / 40000000000) = 1/(20000000000 / 62767582421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (571853231 / 500000000) (35740827 / 31250000) (Real.log (62767582421 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (62767582421 / 20000000000) = -Real.log (20000000000 / 62767582421) := by
    rw [show ((62767582421 / 20000000000) : ℝ) = ((20000000000 / 62767582421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0066

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0067Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0067
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

theorem reflection_log_1_neg : (180364607 / 500000000) ≤ -Real.log (320 / 459) ∧
    -Real.log (320 / 459) ≤ (72145843 / 200000000) := by
  have h := checkLog_sound (w := (139 / 779)) (n := 12)
    (lo := (180364607 / 500000000)) (hi := (72145843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((459 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(459 / 320) = 1/(320 / 459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (180364607 / 500000000) (72145843 / 200000000) (Real.log (459 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (459 / 320) = -Real.log (320 / 459) := by
    rw [show ((459 / 320) : ℝ) = ((320 / 459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (142455991 / 250000000) ≤ -Real.log (181 / 320) ∧
    -Real.log (181 / 320) ≤ (113964793 / 200000000) := by
  have h := checkLog_sound (w := (139 / 501)) (n := 12)
    (lo := (142455991 / 250000000)) (hi := (113964793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 181) = 1/(181 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113964793 / 200000000) (-142455991 / 250000000) (Real.log (181 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (179955943 / 500000000) ≤ -Real.log (2560 / 3669) ∧
    -Real.log (2560 / 3669) ≤ (359911887 / 1000000000) := by
  have h := checkLog_sound (w := (1109 / 6229)) (n := 12)
    (lo := (179955943 / 500000000)) (hi := (359911887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3669 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3669 / 2560) = 1/(2560 / 3669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (179955943 / 500000000) (359911887 / 1000000000) (Real.log (3669 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3669 / 2560) = -Real.log (2560 / 3669) := by
    rw [show ((3669 / 2560) : ℝ) = ((2560 / 3669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (141938571 / 250000000) ≤ -Real.log (1451 / 2560) ∧
    -Real.log (1451 / 2560) ≤ (113550857 / 200000000) := by
  have h := checkLog_sound (w := (1109 / 4011)) (n := 12)
    (lo := (141938571 / 250000000)) (hi := (113550857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1451) = 1/(1451 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-113550857 / 200000000) (-141938571 / 250000000) (Real.log (1451 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (312634879 / 500000000) ≤ -Real.log (160 / 299) ∧
    -Real.log (160 / 299) ≤ (625269759 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 459)) (n := 12)
    (lo := (312634879 / 500000000)) (hi := (625269759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299 / 160) = 1/(160 / 299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (312634879 / 500000000) (625269759 / 1000000000) (Real.log (299 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (299 / 160) = -Real.log (160 / 299) := by
    rw [show ((299 / 160) : ℝ) = ((160 / 299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (126915711 / 62500000) ≤ -Real.log (21 / 160) ∧
    -Real.log (21 / 160) ≤ (2030651379 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 21) = 1/(21 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2030651379 / 1000000000) (-126915711 / 62500000) (Real.log (21 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (62401479 / 100000000) ≤ -Real.log (1280 / 2389) ∧
    -Real.log (1280 / 2389) ≤ (624014791 / 1000000000) := by
  have h := checkLog_sound (w := (1109 / 3669)) (n := 12)
    (lo := (62401479 / 100000000)) (hi := (624014791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2389 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2389 / 1280) = 1/(1280 / 2389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (62401479 / 100000000) (624014791 / 1000000000) (Real.log (2389 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2389 / 1280) = -Real.log (1280 / 2389) := by
    rw [show ((2389 / 1280) : ℝ) = ((1280 / 2389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2012951799 / 1000000000) ≤ -Real.log (171 / 1280) ∧
    -Real.log (171 / 1280) ≤ (1006475901 / 500000000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 171) = 1/(171 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1006475901 / 500000000) (-2012951799 / 1000000000) (Real.log (171 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62055589 / 125000000) ≤ -Real.log (100000 / 164287) ∧
    -Real.log (100000 / 164287) ≤ (496444713 / 1000000000) := by
  have h := checkLog_sound (w := (64287 / 264287)) (n := 12)
    (lo := (62055589 / 125000000)) (hi := (496444713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164287 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164287 / 100000) = 1/(100000 / 164287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62055589 / 125000000) (496444713 / 1000000000) (Real.log (164287 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (164287 / 100000) = -Real.log (100000 / 164287) := by
    rw [show ((164287 / 100000) : ℝ) = ((100000 / 164287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1029655417 / 1000000000) ≤ -Real.log (35713 / 100000) ∧
    -Real.log (35713 / 100000) ≤ (1029655419 / 1000000000) := by
  have h := checkLog_sound (w := (14287 / 85713)) (n := 12)
    (lo := (336508237 / 1000000000)) (hi := (168254119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35713) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35713) = 1/(35713 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1029655419 / 1000000000) (-1029655417 / 1000000000) (Real.log (35713 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (62209797 / 125000000) ≤ -Real.log (500000 / 822449) ∧
    -Real.log (500000 / 822449) ≤ (497678377 / 1000000000) := by
  have h := checkLog_sound (w := (322449 / 1322449)) (n := 12)
    (lo := (62209797 / 125000000)) (hi := (497678377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822449 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822449 / 500000) = 1/(500000 / 822449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (62209797 / 125000000) (497678377 / 1000000000) (Real.log (822449 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (822449 / 500000) = -Real.log (500000 / 822449) := by
    rw [show ((822449 / 500000) : ℝ) = ((500000 / 822449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (517675103 / 500000000) ≤ -Real.log (177551 / 500000) ∧
    -Real.log (177551 / 500000) ≤ (16177347 / 15625000) := by
  have h := checkLog_sound (w := (72449 / 427551)) (n := 12)
    (lo := (171101513 / 500000000)) (hi := (342203027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177551) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177551) = 1/(177551 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16177347 / 15625000) (-517675103 / 500000000) (Real.log (177551 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (413870351 / 1000000000) ≤ -Real.log (1000000 / 1512661) ∧
    -Real.log (1000000 / 1512661) ≤ (25866897 / 62500000) := by
  have h := checkLog_sound (w := (512661 / 2512661)) (n := 12)
    (lo := (413870351 / 1000000000)) (hi := (25866897 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1512661 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1512661 / 1000000) = 1/(1000000 / 1512661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (413870351 / 1000000000) (25866897 / 62500000) (Real.log (1512661 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1512661 / 1000000) = -Real.log (1000000 / 1512661) := by
    rw [show ((1512661 / 1000000) : ℝ) = ((1000000 / 1512661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (359397649 / 500000000) ≤ -Real.log (487339 / 1000000) ∧
    -Real.log (487339 / 1000000) ≤ (7187953 / 10000000) := by
  have h := checkLog_sound (w := (12661 / 987339)) (n := 12)
    (lo := (12824059 / 500000000)) (hi := (25648119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 487339) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 487339) = 1/(487339 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-7187953 / 10000000) (-359397649 / 500000000) (Real.log (487339 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (103802039 / 250000000) ≤ -Real.log (500000 / 757343) ∧
    -Real.log (500000 / 757343) ≤ (415208157 / 1000000000) := by
  have h := checkLog_sound (w := (257343 / 1257343)) (n := 12)
    (lo := (103802039 / 250000000)) (hi := (415208157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757343 / 500000) = 1/(500000 / 757343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103802039 / 250000000) (415208157 / 1000000000) (Real.log (757343 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (757343 / 500000) = -Real.log (500000 / 757343) := by
    rw [show ((757343 / 500000) : ℝ) = ((500000 / 757343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (361479587 / 500000000) ≤ -Real.log (242657 / 500000) ∧
    -Real.log (242657 / 500000) ≤ (90369897 / 125000000) := by
  have h := checkLog_sound (w := (7343 / 492657)) (n := 12)
    (lo := (14905997 / 500000000)) (hi := (5962399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 242657) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 242657) = 1/(242657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-90369897 / 125000000) (-361479587 / 500000000) (Real.log (242657 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1526100129 / 1000000000) ≤ -Real.log (125000000000 / 575025200907) ∧
    -Real.log (125000000000 / 575025200907) ≤ (381525033 / 250000000) := by
  have h := checkLog_sound (w := (75025200907 / 1075025200907)) (n := 12)
    (lo := (139805769 / 1000000000)) (hi := (13980577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575025200907 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(575025200907 / 500000000000) = 1/(125000000000 / 575025200907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1526100129 / 1000000000) (381525033 / 250000000) (Real.log (575025200907 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (575025200907 / 125000000000) = -Real.log (125000000000 / 575025200907) := by
    rw [show ((575025200907 / 125000000000) : ℝ) = ((125000000000 / 575025200907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1533028581 / 1000000000) ≤ -Real.log (31250000000 / 144755767357) ∧
    -Real.log (31250000000 / 144755767357) ≤ (191628573 / 125000000) := by
  have h := checkLog_sound (w := (19755767357 / 269755767357)) (n := 12)
    (lo := (146734221 / 1000000000)) (hi := (73367111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144755767357 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(144755767357 / 125000000000) = 1/(31250000000 / 144755767357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1533028581 / 1000000000) (191628573 / 125000000) (Real.log (144755767357 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (144755767357 / 31250000000) = -Real.log (31250000000 / 144755767357) := by
    rw [show ((144755767357 / 31250000000) : ℝ) = ((31250000000 / 144755767357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22653313 / 20000000) ≤ -Real.log (250000000000 / 775979862067) ∧
    -Real.log (250000000000 / 775979862067) ≤ (283166413 / 250000000) := by
  have h := checkLog_sound (w := (275979862067 / 1275979862067)) (n := 12)
    (lo := (43951847 / 100000000)) (hi := (439518471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775979862067 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(775979862067 / 500000000000) = 1/(250000000000 / 775979862067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (22653313 / 20000000) (283166413 / 250000000) (Real.log (775979862067 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (775979862067 / 250000000000) = -Real.log (250000000000 / 775979862067) := by
    rw [show ((775979862067 / 250000000000) : ℝ) = ((250000000000 / 775979862067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1138167331 / 1000000000) ≤ -Real.log (500000000000 / 1560521641659) ∧
    -Real.log (500000000000 / 1560521641659) ≤ (1138167333 / 1000000000) := by
  have h := checkLog_sound (w := (560521641659 / 2560521641659)) (n := 12)
    (lo := (445020151 / 1000000000)) (hi := (55627519 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1560521641659 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1560521641659 / 1000000000000) = 1/(500000000000 / 1560521641659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1138167331 / 1000000000) (1138167333 / 1000000000) (Real.log (1560521641659 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1560521641659 / 500000000000) = -Real.log (500000000000 / 1560521641659) := by
    rw [show ((1560521641659 / 500000000000) : ℝ) = ((500000000000 / 1560521641659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0067

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0068Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0068
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

theorem reflection_log_1_neg : (179955943 / 500000000) ≤ -Real.log (2560 / 3669) ∧
    -Real.log (2560 / 3669) ≤ (359911887 / 1000000000) := by
  have h := checkLog_sound (w := (1109 / 6229)) (n := 12)
    (lo := (179955943 / 500000000)) (hi := (359911887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3669 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3669 / 2560) = 1/(2560 / 3669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (179955943 / 500000000) (359911887 / 1000000000) (Real.log (3669 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3669 / 2560) = -Real.log (2560 / 3669) := by
    rw [show ((3669 / 2560) : ℝ) = ((2560 / 3669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (141938571 / 250000000) ≤ -Real.log (1451 / 2560) ∧
    -Real.log (1451 / 2560) ≤ (113550857 / 200000000) := by
  have h := checkLog_sound (w := (1109 / 4011)) (n := 12)
    (lo := (141938571 / 250000000)) (hi := (113550857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1451) = 1/(1451 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113550857 / 200000000) (-141938571 / 250000000) (Real.log (1451 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (35909389 / 100000000) ≤ -Real.log (1280 / 1833) ∧
    -Real.log (1280 / 1833) ≤ (359093891 / 1000000000) := by
  have h := checkLog_sound (w := (553 / 3113)) (n := 12)
    (lo := (35909389 / 100000000)) (hi := (359093891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1833 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1833 / 1280) = 1/(1280 / 1833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (35909389 / 100000000) (359093891 / 1000000000) (Real.log (1833 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1833 / 1280) = -Real.log (1280 / 1833) := by
    rw [show ((1833 / 1280) : ℝ) = ((1280 / 1833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (565688879 / 1000000000) ≤ -Real.log (727 / 1280) ∧
    -Real.log (727 / 1280) ≤ (7071111 / 12500000) := by
  have h := checkLog_sound (w := (553 / 2007)) (n := 12)
    (lo := (565688879 / 1000000000)) (hi := (7071111 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 727) = 1/(727 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7071111 / 12500000) (-565688879 / 1000000000) (Real.log (727 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (62401479 / 100000000) ≤ -Real.log (1280 / 2389) ∧
    -Real.log (1280 / 2389) ≤ (624014791 / 1000000000) := by
  have h := checkLog_sound (w := (1109 / 3669)) (n := 12)
    (lo := (62401479 / 100000000)) (hi := (624014791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2389 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2389 / 1280) = 1/(1280 / 2389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (62401479 / 100000000) (624014791 / 1000000000) (Real.log (2389 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2389 / 1280) = -Real.log (1280 / 2389) := by
    rw [show ((2389 / 1280) : ℝ) = ((1280 / 2389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2012951799 / 1000000000) ≤ -Real.log (171 / 1280) ∧
    -Real.log (171 / 1280) ≤ (1006475901 / 500000000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 171) = 1/(171 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1006475901 / 500000000) (-2012951799 / 1000000000) (Real.log (171 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124551649 / 200000000) ≤ -Real.log (640 / 1193) ∧
    -Real.log (640 / 1193) ≤ (311379123 / 500000000) := by
  have h := checkLog_sound (w := (553 / 1833)) (n := 12)
    (lo := (124551649 / 200000000)) (hi := (311379123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193 / 640) = 1/(640 / 1193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124551649 / 200000000) (311379123 / 500000000) (Real.log (1193 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1193 / 640) = -Real.log (640 / 1193) := by
    rw [show ((1193 / 640) : ℝ) = ((640 / 1193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (249445007 / 125000000) ≤ -Real.log (87 / 640) ∧
    -Real.log (87 / 640) ≤ (1995560059 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 87) = 1/(87 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1995560059 / 1000000000) (-249445007 / 125000000) (Real.log (87 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (495212571 / 1000000000) ≤ -Real.log (1000000 / 1640847) ∧
    -Real.log (1000000 / 1640847) ≤ (123803143 / 250000000) := by
  have h := checkLog_sound (w := (640847 / 2640847)) (n := 12)
    (lo := (495212571 / 1000000000)) (hi := (123803143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1640847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1640847 / 1000000) = 1/(1000000 / 1640847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (495212571 / 1000000000) (123803143 / 250000000) (Real.log (1640847 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1640847 / 1000000) = -Real.log (1000000 / 1640847) := by
    rw [show ((1640847 / 1000000) : ℝ) = ((1000000 / 1640847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (256001699 / 250000000) ≤ -Real.log (359153 / 1000000) ∧
    -Real.log (359153 / 1000000) ≤ (512003399 / 500000000) := by
  have h := checkLog_sound (w := (140847 / 859153)) (n := 12)
    (lo := (10339363 / 31250000)) (hi := (330859617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 359153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 359153) = 1/(359153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-512003399 / 500000000) (-256001699 / 250000000) (Real.log (359153 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (496445321 / 1000000000) ≤ -Real.log (1000000 / 1642871) ∧
    -Real.log (1000000 / 1642871) ≤ (248222661 / 500000000) := by
  have h := checkLog_sound (w := (642871 / 2642871)) (n := 12)
    (lo := (496445321 / 1000000000)) (hi := (248222661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1642871 / 1000000) = 1/(1000000 / 1642871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (496445321 / 1000000000) (248222661 / 500000000) (Real.log (1642871 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1642871 / 1000000) = -Real.log (1000000 / 1642871) := by
    rw [show ((1642871 / 1000000) : ℝ) = ((1000000 / 1642871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1029658217 / 1000000000) ≤ -Real.log (357129 / 1000000) ∧
    -Real.log (357129 / 1000000) ≤ (1029658219 / 1000000000) := by
  have h := checkLog_sound (w := (142871 / 857129)) (n := 12)
    (lo := (336511037 / 1000000000)) (hi := (168255519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357129) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 357129) = 1/(357129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1029658219 / 1000000000) (-1029658217 / 1000000000) (Real.log (357129 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (412537373 / 1000000000) ≤ -Real.log (500000 / 755323) ∧
    -Real.log (500000 / 755323) ≤ (206268687 / 500000000) := by
  have h := checkLog_sound (w := (255323 / 1255323)) (n := 12)
    (lo := (412537373 / 1000000000)) (hi := (206268687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755323 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755323 / 500000) = 1/(500000 / 755323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (412537373 / 1000000000) (206268687 / 500000000) (Real.log (755323 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (755323 / 500000) = -Real.log (500000 / 755323) := by
    rw [show ((755323 / 500000) : ℝ) = ((500000 / 755323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (178667281 / 250000000) ≤ -Real.log (244677 / 500000) ∧
    -Real.log (244677 / 500000) ≤ (357334563 / 500000000) := by
  have h := checkLog_sound (w := (5323 / 494677)) (n := 12)
    (lo := (2690243 / 125000000)) (hi := (4304389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 244677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 244677) = 1/(244677 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-357334563 / 500000000) (-178667281 / 250000000) (Real.log (244677 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (103467753 / 250000000) ≤ -Real.log (500000 / 756331) ∧
    -Real.log (500000 / 756331) ≤ (413871013 / 1000000000) := by
  have h := checkLog_sound (w := (256331 / 1256331)) (n := 12)
    (lo := (103467753 / 250000000)) (hi := (413871013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((756331 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(756331 / 500000) = 1/(500000 / 756331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103467753 / 250000000) (413871013 / 1000000000) (Real.log (756331 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (756331 / 500000) = -Real.log (500000 / 756331) := by
    rw [show ((756331 / 500000) : ℝ) = ((500000 / 756331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (14375947 / 20000000) ≤ -Real.log (243669 / 500000) ∧
    -Real.log (243669 / 500000) ≤ (89849669 / 125000000) := by
  have h := checkLog_sound (w := (6331 / 493669)) (n := 12)
    (lo := (2565017 / 100000000)) (hi := (25650171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 243669) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 243669) = 1/(243669 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-89849669 / 125000000) (-14375947 / 20000000) (Real.log (243669 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (189902421 / 125000000) ≤ -Real.log (31250000000 / 142770542777) ∧
    -Real.log (31250000000 / 142770542777) ≤ (1519219371 / 1000000000) := by
  have h := checkLog_sound (w := (17770542777 / 267770542777)) (n := 12)
    (lo := (8307813 / 62500000)) (hi := (132925009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142770542777 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(142770542777 / 125000000000) = 1/(31250000000 / 142770542777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (189902421 / 125000000) (1519219371 / 1000000000) (Real.log (142770542777 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (142770542777 / 31250000000) = -Real.log (31250000000 / 142770542777) := by
    rw [show ((142770542777 / 31250000000) : ℝ) = ((31250000000 / 142770542777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1526103537 / 1000000000) ≤ -Real.log (62500000000 / 287513580527) ∧
    -Real.log (62500000000 / 287513580527) ≤ (76305177 / 50000000) := by
  have h := checkLog_sound (w := (37513580527 / 537513580527)) (n := 12)
    (lo := (139809177 / 1000000000)) (hi := (69904589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287513580527 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(287513580527 / 250000000000) = 1/(62500000000 / 287513580527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1526103537 / 1000000000) (76305177 / 50000000) (Real.log (287513580527 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (287513580527 / 62500000000) = -Real.log (62500000000 / 287513580527) := by
    rw [show ((287513580527 / 62500000000) : ℝ) = ((62500000000 / 287513580527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (563603249 / 500000000) ≤ -Real.log (250000000000 / 771755211973) ∧
    -Real.log (250000000000 / 771755211973) ≤ (2254413 / 2000000) := by
  have h := checkLog_sound (w := (271755211973 / 1271755211973)) (n := 12)
    (lo := (217029659 / 500000000)) (hi := (434059319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771755211973 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(771755211973 / 500000000000) = 1/(250000000000 / 771755211973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (563603249 / 500000000) (2254413 / 2000000) (Real.log (771755211973 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (771755211973 / 250000000000) = -Real.log (250000000000 / 771755211973) := by
    rw [show ((771755211973 / 250000000000) : ℝ) = ((250000000000 / 771755211973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1132668363 / 1000000000) ≤ -Real.log (250000000000 / 775981967341) ∧
    -Real.log (250000000000 / 775981967341) ≤ (226533673 / 200000000) := by
  have h := checkLog_sound (w := (275981967341 / 1275981967341)) (n := 12)
    (lo := (439521183 / 1000000000)) (hi := (13735037 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775981967341 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(775981967341 / 500000000000) = 1/(250000000000 / 775981967341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1132668363 / 1000000000) (226533673 / 200000000) (Real.log (775981967341 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (775981967341 / 250000000000) = -Real.log (250000000000 / 775981967341) := by
    rw [show ((775981967341 / 250000000000) : ℝ) = ((250000000000 / 775981967341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0068

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0069Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0069
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

theorem reflection_log_1_neg : (35909389 / 100000000) ≤ -Real.log (1280 / 1833) ∧
    -Real.log (1280 / 1833) ≤ (359093891 / 1000000000) := by
  have h := checkLog_sound (w := (553 / 3113)) (n := 12)
    (lo := (35909389 / 100000000)) (hi := (359093891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1833 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1833 / 1280) = 1/(1280 / 1833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (35909389 / 100000000) (359093891 / 1000000000) (Real.log (1833 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1833 / 1280) = -Real.log (1280 / 1833) := by
    rw [show ((1833 / 1280) : ℝ) = ((1280 / 1833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (565688879 / 1000000000) ≤ -Real.log (727 / 1280) ∧
    -Real.log (727 / 1280) ≤ (7071111 / 12500000) := by
  have h := checkLog_sound (w := (553 / 2007)) (n := 12)
    (lo := (565688879 / 1000000000)) (hi := (7071111 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 727) = 1/(727 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7071111 / 12500000) (-565688879 / 1000000000) (Real.log (727 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (14331009 / 40000000) ≤ -Real.log (2560 / 3663) ∧
    -Real.log (2560 / 3663) ≤ (179137613 / 500000000) := by
  have h := checkLog_sound (w := (1103 / 6223)) (n := 12)
    (lo := (14331009 / 40000000)) (hi := (179137613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3663 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3663 / 2560) = 1/(2560 / 3663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (14331009 / 40000000) (179137613 / 500000000) (Real.log (3663 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3663 / 2560) = -Real.log (2560 / 3663) := by
    rw [show ((3663 / 2560) : ℝ) = ((2560 / 3663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (563627731 / 1000000000) ≤ -Real.log (1457 / 2560) ∧
    -Real.log (1457 / 2560) ≤ (140906933 / 250000000) := by
  have h := checkLog_sound (w := (1103 / 4017)) (n := 12)
    (lo := (563627731 / 1000000000)) (hi := (140906933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1457) = 1/(1457 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140906933 / 250000000) (-563627731 / 1000000000) (Real.log (1457 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (124551649 / 200000000) ≤ -Real.log (640 / 1193) ∧
    -Real.log (640 / 1193) ≤ (311379123 / 500000000) := by
  have h := checkLog_sound (w := (553 / 1833)) (n := 12)
    (lo := (124551649 / 200000000)) (hi := (311379123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193 / 640) = 1/(640 / 1193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (124551649 / 200000000) (311379123 / 500000000) (Real.log (1193 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1193 / 640) = -Real.log (640 / 1193) := by
    rw [show ((1193 / 640) : ℝ) = ((640 / 1193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (249445007 / 125000000) ≤ -Real.log (87 / 640) ∧
    -Real.log (87 / 640) ≤ (1995560059 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 87) = 1/(87 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1995560059 / 1000000000) (-249445007 / 125000000) (Real.log (87 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15537503 / 25000000) ≤ -Real.log (1280 / 2383) ∧
    -Real.log (1280 / 2383) ≤ (621500121 / 1000000000) := by
  have h := checkLog_sound (w := (1103 / 3663)) (n := 12)
    (lo := (15537503 / 25000000)) (hi := (621500121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2383 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2383 / 1280) = 1/(1280 / 2383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15537503 / 25000000) (621500121 / 1000000000) (Real.log (2383 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2383 / 1280) = -Real.log (1280 / 2383) := by
    rw [show ((2383 / 1280) : ℝ) = ((1280 / 2383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1978465623 / 1000000000) ≤ -Real.log (177 / 1280) ∧
    -Real.log (177 / 1280) ≤ (989232813 / 500000000) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 177) = 1/(177 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-989232813 / 500000000) (-1978465623 / 1000000000) (Real.log (177 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (123495643 / 250000000) ≤ -Real.log (100000 / 163883) ∧
    -Real.log (100000 / 163883) ≤ (493982573 / 1000000000) := by
  have h := checkLog_sound (w := (63883 / 263883)) (n := 12)
    (lo := (123495643 / 250000000)) (hi := (493982573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163883 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163883 / 100000) = 1/(100000 / 163883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (123495643 / 250000000) (493982573 / 1000000000) (Real.log (163883 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (163883 / 100000) = -Real.log (100000 / 163883) := by
    rw [show ((163883 / 100000) : ℝ) = ((100000 / 163883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (254601629 / 250000000) ≤ -Real.log (36117 / 100000) ∧
    -Real.log (36117 / 100000) ≤ (509203259 / 500000000) := by
  have h := checkLog_sound (w := (13883 / 86117)) (n := 12)
    (lo := (40657417 / 125000000)) (hi := (325259337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 36117) = 1/(36117 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-509203259 / 500000000) (-254601629 / 250000000) (Real.log (36117 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (495213181 / 1000000000) ≤ -Real.log (62500 / 102553) ∧
    -Real.log (62500 / 102553) ≤ (247606591 / 500000000) := by
  have h := checkLog_sound (w := (40053 / 165053)) (n := 12)
    (lo := (495213181 / 1000000000)) (hi := (247606591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102553 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102553 / 62500) = 1/(62500 / 102553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (495213181 / 1000000000) (247606591 / 500000000) (Real.log (102553 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (102553 / 62500) = -Real.log (62500 / 102553) := by
    rw [show ((102553 / 62500) : ℝ) = ((62500 / 102553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1024009581 / 1000000000) ≤ -Real.log (22447 / 62500) ∧
    -Real.log (22447 / 62500) ≤ (1024009583 / 1000000000) := by
  have h := checkLog_sound (w := (8803 / 53697)) (n := 12)
    (lo := (330862401 / 1000000000)) (hi := (165431201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22447) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 22447) = 1/(22447 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1024009583 / 1000000000) (-1024009581 / 1000000000) (Real.log (22447 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (82241849 / 200000000) ≤ -Real.log (1000000 / 1508641) ∧
    -Real.log (1000000 / 1508641) ≤ (205604623 / 500000000) := by
  have h := checkLog_sound (w := (508641 / 2508641)) (n := 12)
    (lo := (82241849 / 200000000)) (hi := (205604623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1508641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1508641 / 1000000) = 1/(1000000 / 1508641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (82241849 / 200000000) (205604623 / 500000000) (Real.log (1508641 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1508641 / 1000000) = -Real.log (1000000 / 1508641) := by
    rw [show ((1508641 / 1000000) : ℝ) = ((1000000 / 1508641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (22205633 / 31250000) ≤ -Real.log (491359 / 1000000) ∧
    -Real.log (491359 / 1000000) ≤ (355290129 / 500000000) := by
  have h := checkLog_sound (w := (8641 / 991359)) (n := 12)
    (lo := (4358269 / 250000000)) (hi := (17433077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 491359) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 491359) = 1/(491359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-355290129 / 500000000) (-22205633 / 31250000) (Real.log (491359 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (82507607 / 200000000) ≤ -Real.log (1000000 / 1510647) ∧
    -Real.log (1000000 / 1510647) ≤ (103134509 / 250000000) := by
  have h := checkLog_sound (w := (510647 / 2510647)) (n := 12)
    (lo := (82507607 / 200000000)) (hi := (103134509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1510647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1510647 / 1000000) = 1/(1000000 / 1510647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (82507607 / 200000000) (103134509 / 250000000) (Real.log (1510647 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1510647 / 1000000) = -Real.log (1000000 / 1510647) := by
    rw [show ((1510647 / 1000000) : ℝ) = ((1000000 / 1510647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (714671167 / 1000000000) ≤ -Real.log (489353 / 1000000) ∧
    -Real.log (489353 / 1000000) ≤ (714671169 / 1000000000) := by
  have h := checkLog_sound (w := (10647 / 989353)) (n := 12)
    (lo := (21523987 / 1000000000)) (hi := (5380997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 489353) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 489353) = 1/(489353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-714671169 / 1000000000) (-714671167 / 1000000000) (Real.log (489353 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (47262159 / 31250000) ≤ -Real.log (50000000000 / 226877924523) ∧
    -Real.log (50000000000 / 226877924523) ≤ (1512389091 / 1000000000) := by
  have h := checkLog_sound (w := (26877924523 / 426877924523)) (n := 12)
    (lo := (15761841 / 125000000)) (hi := (126094729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226877924523 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(226877924523 / 200000000000) = 1/(50000000000 / 226877924523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (47262159 / 31250000) (1512389091 / 1000000000) (Real.log (226877924523 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (226877924523 / 50000000000) = -Real.log (50000000000 / 226877924523) := by
    rw [show ((226877924523 / 50000000000) : ℝ) = ((50000000000 / 226877924523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (759611381 / 500000000) ≤ -Real.log (500000000000 / 2284336436941) ∧
    -Real.log (500000000000 / 2284336436941) ≤ (303844553 / 200000000) := by
  have h := checkLog_sound (w := (284336436941 / 4284336436941)) (n := 12)
    (lo := (66464201 / 500000000)) (hi := (132928403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2284336436941 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2284336436941 / 2000000000000) = 1/(500000000000 / 2284336436941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (759611381 / 500000000) (303844553 / 200000000) (Real.log (2284336436941 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2284336436941 / 500000000000) = -Real.log (500000000000 / 2284336436941) := by
    rw [show ((2284336436941 / 500000000000) : ℝ) = ((500000000000 / 2284336436941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (560894751 / 500000000) ≤ -Real.log (250000000000 / 767585919867) ∧
    -Real.log (250000000000 / 767585919867) ≤ (17527961 / 15625000) := by
  have h := checkLog_sound (w := (267585919867 / 1267585919867)) (n := 12)
    (lo := (214321161 / 500000000)) (hi := (428642323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767585919867 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(767585919867 / 500000000000) = 1/(250000000000 / 767585919867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (560894751 / 500000000) (17527961 / 15625000) (Real.log (767585919867 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (767585919867 / 250000000000) = -Real.log (250000000000 / 767585919867) := by
    rw [show ((767585919867 / 250000000000) : ℝ) = ((250000000000 / 767585919867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1127209203 / 1000000000) ≤ -Real.log (500000000000 / 1543514599891) ∧
    -Real.log (500000000000 / 1543514599891) ≤ (225441841 / 200000000) := by
  have h := checkLog_sound (w := (543514599891 / 2543514599891)) (n := 12)
    (lo := (434062023 / 1000000000)) (hi := (54257753 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1543514599891 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1543514599891 / 1000000000000) = 1/(500000000000 / 1543514599891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1127209203 / 1000000000) (225441841 / 200000000) (Real.log (1543514599891 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1543514599891 / 500000000000) = -Real.log (500000000000 / 1543514599891) := by
    rw [show ((1543514599891 / 500000000000) : ℝ) = ((500000000000 / 1543514599891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0069

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0070Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0070
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

theorem reflection_log_1_neg : (14331009 / 40000000) ≤ -Real.log (2560 / 3663) ∧
    -Real.log (2560 / 3663) ≤ (179137613 / 500000000) := by
  have h := checkLog_sound (w := (1103 / 6223)) (n := 12)
    (lo := (14331009 / 40000000)) (hi := (179137613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3663 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3663 / 2560) = 1/(2560 / 3663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (14331009 / 40000000) (179137613 / 500000000) (Real.log (3663 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3663 / 2560) = -Real.log (2560 / 3663) := by
    rw [show ((3663 / 2560) : ℝ) = ((2560 / 3663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (563627731 / 1000000000) ≤ -Real.log (1457 / 2560) ∧
    -Real.log (1457 / 2560) ≤ (140906933 / 250000000) := by
  have h := checkLog_sound (w := (1103 / 4017)) (n := 12)
    (lo := (563627731 / 1000000000)) (hi := (140906933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1457) = 1/(1457 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-140906933 / 250000000) (-563627731 / 1000000000) (Real.log (1457 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (22340993 / 62500000) ≤ -Real.log (128 / 183) ∧
    -Real.log (128 / 183) ≤ (357455889 / 1000000000) := by
  have h := checkLog_sound (w := (55 / 311)) (n := 12)
    (lo := (22340993 / 62500000)) (hi := (357455889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183 / 128) = 1/(128 / 183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (22340993 / 62500000) (357455889 / 1000000000) (Real.log (183 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (183 / 128) = -Real.log (128 / 183) := by
    rw [show ((183 / 128) : ℝ) = ((128 / 183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280785411 / 500000000) ≤ -Real.log (73 / 128) ∧
    -Real.log (73 / 128) ≤ (561570823 / 1000000000) := by
  have h := checkLog_sound (w := (55 / 201)) (n := 12)
    (lo := (280785411 / 500000000)) (hi := (561570823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 73) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 73) = 1/(73 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-561570823 / 1000000000) (-280785411 / 500000000) (Real.log (73 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15537503 / 25000000) ≤ -Real.log (1280 / 2383) ∧
    -Real.log (1280 / 2383) ≤ (621500121 / 1000000000) := by
  have h := checkLog_sound (w := (1103 / 3663)) (n := 12)
    (lo := (15537503 / 25000000)) (hi := (621500121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2383 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2383 / 1280) = 1/(1280 / 2383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15537503 / 25000000) (621500121 / 1000000000) (Real.log (2383 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2383 / 1280) = -Real.log (1280 / 2383) := by
    rw [show ((2383 / 1280) : ℝ) = ((1280 / 2383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1978465623 / 1000000000) ≤ -Real.log (177 / 1280) ∧
    -Real.log (177 / 1280) ≤ (989232813 / 500000000) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 177) = 1/(177 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-989232813 / 500000000) (-1978465623 / 1000000000) (Real.log (177 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (620240409 / 1000000000) ≤ -Real.log (64 / 119) ∧
    -Real.log (64 / 119) ≤ (62024041 / 100000000) := by
  have h := checkLog_sound (w := (55 / 183)) (n := 12)
    (lo := (620240409 / 1000000000)) (hi := (62024041 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119 / 64) = 1/(64 / 119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (620240409 / 1000000000) (62024041 / 100000000) (Real.log (119 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (119 / 64) = -Real.log (64 / 119) := by
    rw [show ((119 / 64) : ℝ) = ((64 / 119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (245207313 / 125000000) ≤ -Real.log (9 / 64) ∧
    -Real.log (9 / 64) ≤ (1961658507 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 9) = 1/(9 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1961658507 / 1000000000) (-245207313 / 125000000) (Real.log (9 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (492754113 / 1000000000) ≤ -Real.log (500000 / 818409) ∧
    -Real.log (500000 / 818409) ≤ (246377057 / 500000000) := by
  have h := checkLog_sound (w := (318409 / 1318409)) (n := 12)
    (lo := (492754113 / 1000000000)) (hi := (246377057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818409 / 500000) = 1/(500000 / 818409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (492754113 / 1000000000) (246377057 / 500000000) (Real.log (818409 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (818409 / 500000) = -Real.log (500000 / 818409) := by
    rw [show ((818409 / 500000) : ℝ) = ((500000 / 818409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (126606399 / 125000000) ≤ -Real.log (181591 / 500000) ∧
    -Real.log (181591 / 500000) ≤ (506425597 / 500000000) := by
  have h := checkLog_sound (w := (68409 / 431591)) (n := 12)
    (lo := (79926003 / 250000000)) (hi := (319704013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 181591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 181591) = 1/(181591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-506425597 / 500000000) (-126606399 / 125000000) (Real.log (181591 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (246991591 / 500000000) ≤ -Real.log (1000000 / 1638831) ∧
    -Real.log (1000000 / 1638831) ≤ (493983183 / 1000000000) := by
  have h := checkLog_sound (w := (638831 / 2638831)) (n := 12)
    (lo := (246991591 / 500000000)) (hi := (493983183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1638831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1638831 / 1000000) = 1/(1000000 / 1638831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (246991591 / 500000000) (493983183 / 1000000000) (Real.log (1638831 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1638831 / 1000000) = -Real.log (1000000 / 1638831) := by
    rw [show ((1638831 / 1000000) : ℝ) = ((1000000 / 1638831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (203681857 / 200000000) ≤ -Real.log (361169 / 1000000) ∧
    -Real.log (361169 / 1000000) ≤ (1018409287 / 1000000000) := by
  have h := checkLog_sound (w := (138831 / 861169)) (n := 12)
    (lo := (65052421 / 200000000)) (hi := (162631053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 361169) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 361169) = 1/(361169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1018409287 / 1000000000) (-203681857 / 200000000) (Real.log (361169 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102471331 / 250000000) ≤ -Real.log (200000 / 301329) ∧
    -Real.log (200000 / 301329) ≤ (16395413 / 40000000) := by
  have h := checkLog_sound (w := (101329 / 501329)) (n := 12)
    (lo := (102471331 / 250000000)) (hi := (16395413 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301329 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301329 / 200000) = 1/(200000 / 301329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102471331 / 250000000) (16395413 / 40000000) (Real.log (301329 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (301329 / 200000) = -Real.log (200000 / 301329) := by
    rw [show ((301329 / 200000) : ℝ) = ((200000 / 301329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (353263141 / 500000000) ≤ -Real.log (98671 / 200000) ∧
    -Real.log (98671 / 200000) ≤ (176631571 / 250000000) := by
  have h := checkLog_sound (w := (1329 / 198671)) (n := 12)
    (lo := (6689551 / 500000000)) (hi := (13379103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 98671) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 98671) = 1/(98671 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-176631571 / 250000000) (-353263141 / 500000000) (Real.log (98671 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (102802477 / 250000000) ≤ -Real.log (500000 / 754321) ∧
    -Real.log (500000 / 754321) ≤ (411209909 / 1000000000) := by
  have h := checkLog_sound (w := (254321 / 1254321)) (n := 12)
    (lo := (102802477 / 250000000)) (hi := (411209909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754321 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754321 / 500000) = 1/(500000 / 754321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102802477 / 250000000) (411209909 / 1000000000) (Real.log (754321 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (754321 / 500000) = -Real.log (500000 / 754321) := by
    rw [show ((754321 / 500000) : ℝ) = ((500000 / 754321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (177645573 / 250000000) ≤ -Real.log (245679 / 500000) ∧
    -Real.log (245679 / 500000) ≤ (355291147 / 500000000) := by
  have h := checkLog_sound (w := (4321 / 495679)) (n := 12)
    (lo := (2179389 / 125000000)) (hi := (17435113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 245679) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 245679) = 1/(245679 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-355291147 / 500000000) (-177645573 / 250000000) (Real.log (245679 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (301121061 / 200000000) ≤ -Real.log (500000000000 / 2253440423809) ∧
    -Real.log (500000000000 / 2253440423809) ≤ (376401327 / 250000000) := by
  have h := checkLog_sound (w := (253440423809 / 4253440423809)) (n := 12)
    (lo := (23862189 / 200000000)) (hi := (59655473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2253440423809 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2253440423809 / 2000000000000) = 1/(500000000000 / 2253440423809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (301121061 / 200000000) (376401327 / 250000000) (Real.log (2253440423809 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2253440423809 / 500000000000) = -Real.log (500000000000 / 2253440423809) := by
    rw [show ((2253440423809 / 500000000000) : ℝ) = ((500000000000 / 2253440423809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1512392467 / 1000000000) ≤ -Real.log (500000000000 / 2268786911391) ∧
    -Real.log (500000000000 / 2268786911391) ≤ (151239247 / 100000000) := by
  have h := checkLog_sound (w := (268786911391 / 4268786911391)) (n := 12)
    (lo := (126098107 / 1000000000)) (hi := (31524527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2268786911391 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2268786911391 / 2000000000000) = 1/(500000000000 / 2268786911391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1512392467 / 1000000000) (151239247 / 100000000) (Real.log (2268786911391 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2268786911391 / 500000000000) = -Real.log (500000000000 / 2268786911391) := by
    rw [show ((2268786911391 / 500000000000) : ℝ) = ((500000000000 / 2268786911391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (558205803 / 500000000) ≤ -Real.log (500000000000 / 1526938006101) ∧
    -Real.log (500000000000 / 1526938006101) ≤ (139551451 / 125000000) := by
  have h := checkLog_sound (w := (526938006101 / 2526938006101)) (n := 12)
    (lo := (211632213 / 500000000)) (hi := (423264427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1526938006101 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1526938006101 / 1000000000000) = 1/(500000000000 / 1526938006101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (558205803 / 500000000) (139551451 / 125000000) (Real.log (1526938006101 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1526938006101 / 500000000000) = -Real.log (500000000000 / 1526938006101) := by
    rw [show ((1526938006101 / 500000000000) : ℝ) = ((500000000000 / 1526938006101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (5608961 / 5000000) ≤ -Real.log (125000000000 / 383793995417) ∧
    -Real.log (125000000000 / 383793995417) ≤ (560896101 / 500000000) := by
  have h := checkLog_sound (w := (133793995417 / 633793995417)) (n := 12)
    (lo := (21432251 / 50000000)) (hi := (428645021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383793995417 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(383793995417 / 250000000000) = 1/(125000000000 / 383793995417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (5608961 / 5000000) (560896101 / 500000000) (Real.log (383793995417 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (383793995417 / 125000000000) = -Real.log (125000000000 / 383793995417) := by
    rw [show ((383793995417 / 125000000000) : ℝ) = ((125000000000 / 383793995417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0070

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0071Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0071
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

theorem reflection_log_1_neg : (22340993 / 62500000) ≤ -Real.log (128 / 183) ∧
    -Real.log (128 / 183) ≤ (357455889 / 1000000000) := by
  have h := checkLog_sound (w := (55 / 311)) (n := 12)
    (lo := (22340993 / 62500000)) (hi := (357455889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183 / 128) = 1/(128 / 183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (22340993 / 62500000) (357455889 / 1000000000) (Real.log (183 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (183 / 128) = -Real.log (128 / 183) := by
    rw [show ((183 / 128) : ℝ) = ((128 / 183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280785411 / 500000000) ≤ -Real.log (73 / 128) ∧
    -Real.log (73 / 128) ≤ (561570823 / 1000000000) := by
  have h := checkLog_sound (w := (55 / 201)) (n := 12)
    (lo := (280785411 / 500000000)) (hi := (561570823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 73) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 73) = 1/(73 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-561570823 / 1000000000) (-280785411 / 500000000) (Real.log (73 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8915897 / 25000000) ≤ -Real.log (2560 / 3657) ∧
    -Real.log (2560 / 3657) ≤ (356635881 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 6217)) (n := 12)
    (lo := (8915897 / 25000000)) (hi := (356635881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3657 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3657 / 2560) = 1/(2560 / 3657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8915897 / 25000000) (356635881 / 1000000000) (Real.log (3657 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3657 / 2560) = -Real.log (2560 / 3657) := by
    rw [show ((3657 / 2560) : ℝ) = ((2560 / 3657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (69939767 / 125000000) ≤ -Real.log (1463 / 2560) ∧
    -Real.log (1463 / 2560) ≤ (559518137 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 4023)) (n := 12)
    (lo := (69939767 / 125000000)) (hi := (559518137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1463) = 1/(1463 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-559518137 / 1000000000) (-69939767 / 125000000) (Real.log (1463 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (620240409 / 1000000000) ≤ -Real.log (64 / 119) ∧
    -Real.log (64 / 119) ≤ (62024041 / 100000000) := by
  have h := checkLog_sound (w := (55 / 183)) (n := 12)
    (lo := (620240409 / 1000000000)) (hi := (62024041 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119 / 64) = 1/(64 / 119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (620240409 / 1000000000) (62024041 / 100000000) (Real.log (119 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (119 / 64) = -Real.log (64 / 119) := by
    rw [show ((119 / 64) : ℝ) = ((64 / 119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (245207313 / 125000000) ≤ -Real.log (9 / 64) ∧
    -Real.log (9 / 64) ≤ (1961658507 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 9) = 1/(9 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1961658507 / 1000000000) (-245207313 / 125000000) (Real.log (9 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (61897911 / 100000000) ≤ -Real.log (1280 / 2377) ∧
    -Real.log (1280 / 2377) ≤ (618979111 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 3657)) (n := 12)
    (lo := (61897911 / 100000000)) (hi := (618979111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2377 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2377 / 1280) = 1/(1280 / 2377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (61897911 / 100000000) (618979111 / 1000000000) (Real.log (2377 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2377 / 1280) = -Real.log (1280 / 2377) := by
    rw [show ((2377 / 1280) : ℝ) = ((1280 / 2377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (972564601 / 500000000) ≤ -Real.log (183 / 1280) ∧
    -Real.log (183 / 1280) ≤ (389025841 / 200000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 183) = 1/(183 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-389025841 / 200000000) (-972564601 / 500000000) (Real.log (183 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (491527201 / 1000000000) ≤ -Real.log (1000000 / 1634811) ∧
    -Real.log (1000000 / 1634811) ≤ (245763601 / 500000000) := by
  have h := checkLog_sound (w := (634811 / 2634811)) (n := 12)
    (lo := (491527201 / 1000000000)) (hi := (245763601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1634811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1634811 / 1000000) = 1/(1000000 / 1634811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (491527201 / 1000000000) (245763601 / 500000000) (Real.log (1634811 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1634811 / 1000000) = -Real.log (1000000 / 1634811) := by
    rw [show ((1634811 / 1000000) : ℝ) = ((1000000 / 1634811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4029361 / 4000000) ≤ -Real.log (365189 / 1000000) ∧
    -Real.log (365189 / 1000000) ≤ (251835063 / 250000000) := by
  have h := checkLog_sound (w := (134811 / 865189)) (n := 12)
    (lo := (31419307 / 100000000)) (hi := (314193071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 365189) = 1/(365189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-251835063 / 250000000) (-4029361 / 4000000) (Real.log (365189 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (123188681 / 250000000) ≤ -Real.log (1000000 / 1636819) ∧
    -Real.log (1000000 / 1636819) ≤ (19710189 / 40000000) := by
  have h := checkLog_sound (w := (636819 / 2636819)) (n := 12)
    (lo := (123188681 / 250000000)) (hi := (19710189 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1636819 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1636819 / 1000000) = 1/(1000000 / 1636819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (123188681 / 250000000) (19710189 / 40000000) (Real.log (1636819 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1636819 / 1000000) = -Real.log (1000000 / 1636819) := by
    rw [show ((1636819 / 1000000) : ℝ) = ((1000000 / 1636819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (202570789 / 200000000) ≤ -Real.log (363181 / 1000000) ∧
    -Real.log (363181 / 1000000) ≤ (1012853947 / 1000000000) := by
  have h := checkLog_sound (w := (136819 / 863181)) (n := 12)
    (lo := (63941353 / 200000000)) (hi := (159853383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363181) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 363181) = 1/(363181 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1012853947 / 1000000000) (-202570789 / 200000000) (Real.log (363181 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (408565629 / 1000000000) ≤ -Real.log (500000 / 752329) ∧
    -Real.log (500000 / 752329) ≤ (40856563 / 100000000) := by
  have h := checkLog_sound (w := (252329 / 1252329)) (n := 12)
    (lo := (408565629 / 1000000000)) (hi := (40856563 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752329 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752329 / 500000) = 1/(500000 / 752329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (408565629 / 1000000000) (40856563 / 100000000) (Real.log (752329 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (752329 / 500000) = -Real.log (500000 / 752329) := by
    rw [show ((752329 / 500000) : ℝ) = ((500000 / 752329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (140501369 / 200000000) ≤ -Real.log (247671 / 500000) ∧
    -Real.log (247671 / 500000) ≤ (702506847 / 1000000000) := by
  have h := checkLog_sound (w := (2329 / 497671)) (n := 12)
    (lo := (1871933 / 200000000)) (hi := (4679833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 247671) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 247671) = 1/(247671 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-702506847 / 1000000000) (-140501369 / 200000000) (Real.log (247671 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (102471497 / 250000000) ≤ -Real.log (500000 / 753323) ∧
    -Real.log (500000 / 753323) ≤ (409885989 / 1000000000) := by
  have h := checkLog_sound (w := (253323 / 1253323)) (n := 12)
    (lo := (102471497 / 250000000)) (hi := (409885989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753323 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753323 / 500000) = 1/(500000 / 753323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102471497 / 250000000) (409885989 / 1000000000) (Real.log (753323 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (753323 / 500000) = -Real.log (500000 / 753323) := by
    rw [show ((753323 / 500000) : ℝ) = ((500000 / 753323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (706528309 / 1000000000) ≤ -Real.log (246677 / 500000) ∧
    -Real.log (246677 / 500000) ≤ (706528311 / 1000000000) := by
  have h := checkLog_sound (w := (3323 / 496677)) (n := 12)
    (lo := (13381129 / 1000000000)) (hi := (1338113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 246677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 246677) = 1/(246677 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-706528311 / 1000000000) (-706528309 / 1000000000) (Real.log (246677 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1498867451 / 1000000000) ≤ -Real.log (500000000000 / 2238308108951) ∧
    -Real.log (500000000000 / 2238308108951) ≤ (749433727 / 500000000) := by
  have h := checkLog_sound (w := (238308108951 / 4238308108951)) (n := 12)
    (lo := (112573091 / 1000000000)) (hi := (28143273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2238308108951 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2238308108951 / 2000000000000) = 1/(500000000000 / 2238308108951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1498867451 / 1000000000) (749433727 / 500000000) (Real.log (2238308108951 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2238308108951 / 500000000000) = -Real.log (500000000000 / 2238308108951) := by
    rw [show ((2238308108951 / 500000000000) : ℝ) = ((500000000000 / 2238308108951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1505608669 / 1000000000) ≤ -Real.log (100000000000 / 450689601053) ∧
    -Real.log (100000000000 / 450689601053) ≤ (47050271 / 31250000) := by
  have h := checkLog_sound (w := (50689601053 / 850689601053)) (n := 12)
    (lo := (119314309 / 1000000000)) (hi := (11931431 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450689601053 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(450689601053 / 400000000000) = 1/(100000000000 / 450689601053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1505608669 / 1000000000) (47050271 / 31250000) (Real.log (450689601053 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (450689601053 / 100000000000) = -Real.log (100000000000 / 450689601053) := by
    rw [show ((450689601053 / 100000000000) : ℝ) = ((100000000000 / 450689601053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (44442899 / 40000000) ≤ -Real.log (500000000000 / 1518807207949) ∧
    -Real.log (500000000000 / 1518807207949) ≤ (1111072477 / 1000000000) := by
  have h := checkLog_sound (w := (518807207949 / 2518807207949)) (n := 12)
    (lo := (83585059 / 200000000)) (hi := (26120331 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1518807207949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1518807207949 / 1000000000000) = 1/(500000000000 / 1518807207949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (44442899 / 40000000) (1111072477 / 1000000000) (Real.log (1518807207949 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1518807207949 / 500000000000) = -Real.log (500000000000 / 1518807207949) := by
    rw [show ((1518807207949 / 500000000000) : ℝ) = ((500000000000 / 1518807207949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1116414297 / 1000000000) ≤ -Real.log (125000000000 / 381735528647) ∧
    -Real.log (125000000000 / 381735528647) ≤ (1116414299 / 1000000000) := by
  have h := checkLog_sound (w := (131735528647 / 631735528647)) (n := 12)
    (lo := (423267117 / 1000000000)) (hi := (211633559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381735528647 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(381735528647 / 250000000000) = 1/(125000000000 / 381735528647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1116414297 / 1000000000) (1116414299 / 1000000000) (Real.log (381735528647 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (381735528647 / 125000000000) = -Real.log (125000000000 / 381735528647) := by
    rw [show ((381735528647 / 125000000000) : ℝ) = ((125000000000 / 381735528647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0071

end


