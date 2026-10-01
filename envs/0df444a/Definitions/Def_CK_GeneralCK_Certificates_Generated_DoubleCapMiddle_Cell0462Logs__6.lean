-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0462Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0462Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:27:06.153597+00:00
-- url     : https://prove2.me/theorems/6643e4f9-dd62-4693-ae44-f3bc24e9626c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0462Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0463Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0462Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0463Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0464Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0465Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0466Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0467Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0462Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0463Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0464Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0465Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0466Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0467Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0462Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0463Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0464Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0465Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0466Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0467Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0462Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0463Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0464Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0465Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0466Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0467Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0462Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0462
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

theorem reflection_log_1_neg : (185246961 / 1000000000) ≤ -Real.log (2560 / 3081) ∧
    -Real.log (2560 / 3081) ≤ (92623481 / 500000000) := by
  have h := checkLog_sound (w := (521 / 5641)) (n := 12)
    (lo := (185246961 / 1000000000)) (hi := (92623481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3081 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3081 / 2560) = 1/(2560 / 3081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (185246961 / 1000000000) (92623481 / 500000000) (Real.log (3081 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3081 / 2560) = -Real.log (2560 / 3081) := by
    rw [show ((3081 / 2560) : ℝ) = ((2560 / 3081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (113773883 / 500000000) ≤ -Real.log (2039 / 2560) ∧
    -Real.log (2039 / 2560) ≤ (227547767 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 4599)) (n := 12)
    (lo := (113773883 / 500000000)) (hi := (227547767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2039) = 1/(2039 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-227547767 / 1000000000) (-113773883 / 500000000) (Real.log (2039 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11562719 / 62500000) ≤ -Real.log (10240 / 12321) ∧
    -Real.log (10240 / 12321) ≤ (37000701 / 200000000) := by
  have h := checkLog_sound (w := (2081 / 22561)) (n := 12)
    (lo := (11562719 / 62500000)) (hi := (37000701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12321 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12321 / 10240) = 1/(10240 / 12321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11562719 / 62500000) (37000701 / 200000000) (Real.log (12321 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12321 / 10240) = -Real.log (10240 / 12321) := by
    rw [show ((12321 / 10240) : ℝ) = ((10240 / 12321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (227180007 / 1000000000) ≤ -Real.log (8159 / 10240) ∧
    -Real.log (8159 / 10240) ≤ (28397501 / 125000000) := by
  have h := checkLog_sound (w := (2081 / 18399)) (n := 12)
    (lo := (227180007 / 1000000000)) (hi := (28397501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8159) = 1/(8159 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-28397501 / 125000000) (-227180007 / 1000000000) (Real.log (8159 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (85370497 / 250000000) ≤ -Real.log (1280 / 1801) ∧
    -Real.log (1280 / 1801) ≤ (341481989 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 3081)) (n := 12)
    (lo := (85370497 / 250000000)) (hi := (341481989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1801 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1801 / 1280) = 1/(1280 / 1801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (85370497 / 250000000) (341481989 / 1000000000) (Real.log (1801 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1801 / 1280) = -Real.log (1280 / 1801) := by
    rw [show ((1801 / 1280) : ℝ) = ((1280 / 1801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (522613579 / 1000000000) ≤ -Real.log (759 / 1280) ∧
    -Real.log (759 / 1280) ≤ (26130679 / 50000000) := by
  have h := checkLog_sound (w := (521 / 2039)) (n := 12)
    (lo := (522613579 / 1000000000)) (hi := (26130679 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 759) = 1/(759 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26130679 / 50000000) (-522613579 / 1000000000) (Real.log (759 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (170532733 / 500000000) ≤ -Real.log (5120 / 7201) ∧
    -Real.log (5120 / 7201) ≤ (341065467 / 1000000000) := by
  have h := checkLog_sound (w := (2081 / 12321)) (n := 12)
    (lo := (170532733 / 500000000)) (hi := (341065467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7201 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7201 / 5120) = 1/(5120 / 7201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (170532733 / 500000000) (341065467 / 1000000000) (Real.log (7201 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7201 / 5120) = -Real.log (5120 / 7201) := by
    rw [show ((7201 / 5120) : ℝ) = ((5120 / 7201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (20865037 / 40000000) ≤ -Real.log (3039 / 5120) ∧
    -Real.log (3039 / 5120) ≤ (260812963 / 500000000) := by
  have h := checkLog_sound (w := (2081 / 8159)) (n := 12)
    (lo := (20865037 / 40000000)) (hi := (260812963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3039) = 1/(3039 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-260812963 / 500000000) (-20865037 / 40000000) (Real.log (3039 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (63568871 / 250000000) ≤ -Real.log (1000000 / 1289527) ∧
    -Real.log (1000000 / 1289527) ≤ (50855097 / 200000000) := by
  have h := checkLog_sound (w := (289527 / 2289527)) (n := 12)
    (lo := (63568871 / 250000000)) (hi := (50855097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289527 / 1000000) = 1/(1000000 / 1289527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (63568871 / 250000000) (50855097 / 200000000) (Real.log (1289527 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1289527 / 1000000) = -Real.log (1000000 / 1289527) := by
    rw [show ((1289527 / 1000000) : ℝ) = ((1000000 / 1289527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (341824333 / 1000000000) ≤ -Real.log (710473 / 1000000) ∧
    -Real.log (710473 / 1000000) ≤ (170912167 / 500000000) := by
  have h := checkLog_sound (w := (289527 / 1710473)) (n := 12)
    (lo := (341824333 / 1000000000)) (hi := (170912167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 710473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 710473) = 1/(710473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-170912167 / 500000000) (-341824333 / 1000000000) (Real.log (710473 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15912813 / 62500000) ≤ -Real.log (31250 / 40311) ∧
    -Real.log (31250 / 40311) ≤ (254605009 / 1000000000) := by
  have h := checkLog_sound (w := (9061 / 71561)) (n := 12)
    (lo := (15912813 / 62500000)) (hi := (254605009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40311 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40311 / 31250) = 1/(31250 / 40311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15912813 / 62500000) (254605009 / 1000000000) (Real.log (40311 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (40311 / 31250) = -Real.log (31250 / 40311) := by
    rw [show ((40311 / 31250) : ℝ) = ((31250 / 40311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (68484541 / 200000000) ≤ -Real.log (22189 / 31250) ∧
    -Real.log (22189 / 31250) ≤ (171211353 / 500000000) := by
  have h := checkLog_sound (w := (9061 / 53439)) (n := 12)
    (lo := (68484541 / 200000000)) (hi := (171211353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 22189) = 1/(22189 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-171211353 / 500000000) (-68484541 / 200000000) (Real.log (22189 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38056457 / 200000000) ≤ -Real.log (1000000 / 1209591) ∧
    -Real.log (1000000 / 1209591) ≤ (95141143 / 500000000) := by
  have h := checkLog_sound (w := (209591 / 2209591)) (n := 12)
    (lo := (38056457 / 200000000)) (hi := (95141143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209591 / 1000000) = 1/(1000000 / 1209591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38056457 / 200000000) (95141143 / 500000000) (Real.log (1209591 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1209591 / 1000000) = -Real.log (1000000 / 1209591) := by
    rw [show ((1209591 / 1000000) : ℝ) = ((1000000 / 1209591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (47040949 / 200000000) ≤ -Real.log (790409 / 1000000) ∧
    -Real.log (790409 / 1000000) ≤ (117602373 / 500000000) := by
  have h := checkLog_sound (w := (209591 / 1790409)) (n := 12)
    (lo := (47040949 / 200000000)) (hi := (117602373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790409) = 1/(790409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-117602373 / 500000000) (-47040949 / 200000000) (Real.log (790409 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (95274641 / 500000000) ≤ -Real.log (500000 / 604957) ∧
    -Real.log (500000 / 604957) ≤ (190549283 / 1000000000) := by
  have h := checkLog_sound (w := (104957 / 1104957)) (n := 12)
    (lo := (95274641 / 500000000)) (hi := (190549283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604957 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604957 / 500000) = 1/(500000 / 604957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95274641 / 500000000) (190549283 / 1000000000) (Real.log (604957 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (604957 / 500000) = -Real.log (500000 / 604957) := by
    rw [show ((604957 / 500000) : ℝ) = ((500000 / 604957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (117806739 / 500000000) ≤ -Real.log (395043 / 500000) ∧
    -Real.log (395043 / 500000) ≤ (235613479 / 1000000000) := by
  have h := checkLog_sound (w := (104957 / 895043)) (n := 12)
    (lo := (117806739 / 500000000)) (hi := (235613479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 395043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 395043) = 1/(395043 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-235613479 / 1000000000) (-117806739 / 500000000) (Real.log (395043 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (298049909 / 500000000) ≤ -Real.log (250000000000 / 453756511507) ∧
    -Real.log (250000000000 / 453756511507) ≤ (596099819 / 1000000000) := by
  have h := checkLog_sound (w := (203756511507 / 703756511507)) (n := 12)
    (lo := (298049909 / 500000000)) (hi := (596099819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((453756511507 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(453756511507 / 250000000000) = 1/(250000000000 / 453756511507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (298049909 / 500000000) (596099819 / 1000000000) (Real.log (453756511507 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (453756511507 / 250000000000) = -Real.log (250000000000 / 453756511507) := by
    rw [show ((453756511507 / 250000000000) : ℝ) = ((250000000000 / 453756511507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (597027713 / 1000000000) ≤ -Real.log (25000000000 / 45417774573) ∧
    -Real.log (25000000000 / 45417774573) ≤ (298513857 / 500000000) := by
  have h := checkLog_sound (w := (20417774573 / 70417774573)) (n := 12)
    (lo := (597027713 / 1000000000)) (hi := (298513857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45417774573 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45417774573 / 25000000000) = 1/(25000000000 / 45417774573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (597027713 / 1000000000) (298513857 / 500000000) (Real.log (45417774573 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45417774573 / 25000000000) = -Real.log (25000000000 / 45417774573) := by
    rw [show ((45417774573 / 25000000000) : ℝ) = ((25000000000 / 45417774573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (425487031 / 1000000000) ≤ -Real.log (20000000000 / 30606711209) ∧
    -Real.log (20000000000 / 30606711209) ≤ (53185879 / 125000000) := by
  have h := checkLog_sound (w := (10606711209 / 50606711209)) (n := 12)
    (lo := (425487031 / 1000000000)) (hi := (53185879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30606711209 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30606711209 / 20000000000) = 1/(20000000000 / 30606711209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (425487031 / 1000000000) (53185879 / 125000000) (Real.log (30606711209 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (30606711209 / 20000000000) = -Real.log (20000000000 / 30606711209) := by
    rw [show ((30606711209 / 20000000000) : ℝ) = ((20000000000 / 30606711209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (426162761 / 1000000000) ≤ -Real.log (25000000000 / 38284250069) ∧
    -Real.log (25000000000 / 38284250069) ≤ (213081381 / 500000000) := by
  have h := checkLog_sound (w := (13284250069 / 63284250069)) (n := 12)
    (lo := (426162761 / 1000000000)) (hi := (213081381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38284250069 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38284250069 / 25000000000) = 1/(25000000000 / 38284250069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (426162761 / 1000000000) (213081381 / 500000000) (Real.log (38284250069 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (38284250069 / 25000000000) = -Real.log (25000000000 / 38284250069) := by
    rw [show ((38284250069 / 25000000000) : ℝ) = ((25000000000 / 38284250069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0462

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0463Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0463
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

theorem reflection_log_1_neg : (11562719 / 62500000) ≤ -Real.log (10240 / 12321) ∧
    -Real.log (10240 / 12321) ≤ (37000701 / 200000000) := by
  have h := checkLog_sound (w := (2081 / 22561)) (n := 12)
    (lo := (11562719 / 62500000)) (hi := (37000701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12321 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12321 / 10240) = 1/(10240 / 12321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11562719 / 62500000) (37000701 / 200000000) (Real.log (12321 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12321 / 10240) = -Real.log (10240 / 12321) := by
    rw [show ((12321 / 10240) : ℝ) = ((10240 / 12321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (227180007 / 1000000000) ≤ -Real.log (8159 / 10240) ∧
    -Real.log (8159 / 10240) ≤ (28397501 / 125000000) := by
  have h := checkLog_sound (w := (2081 / 18399)) (n := 12)
    (lo := (227180007 / 1000000000)) (hi := (28397501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8159) = 1/(8159 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-28397501 / 125000000) (-227180007 / 1000000000) (Real.log (8159 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (184759987 / 1000000000) ≤ -Real.log (5120 / 6159) ∧
    -Real.log (5120 / 6159) ≤ (46189997 / 250000000) := by
  have h := checkLog_sound (w := (1039 / 11279)) (n := 12)
    (lo := (184759987 / 1000000000)) (hi := (46189997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6159 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6159 / 5120) = 1/(5120 / 6159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (184759987 / 1000000000) (46189997 / 250000000) (Real.log (6159 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6159 / 5120) = -Real.log (5120 / 6159) := by
    rw [show ((6159 / 5120) : ℝ) = ((5120 / 6159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (113406191 / 500000000) ≤ -Real.log (4081 / 5120) ∧
    -Real.log (4081 / 5120) ≤ (226812383 / 1000000000) := by
  have h := checkLog_sound (w := (1039 / 9201)) (n := 12)
    (lo := (113406191 / 500000000)) (hi := (226812383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4081) = 1/(4081 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-226812383 / 1000000000) (-113406191 / 500000000) (Real.log (4081 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (170532733 / 500000000) ≤ -Real.log (5120 / 7201) ∧
    -Real.log (5120 / 7201) ≤ (341065467 / 1000000000) := by
  have h := checkLog_sound (w := (2081 / 12321)) (n := 12)
    (lo := (170532733 / 500000000)) (hi := (341065467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7201 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7201 / 5120) = 1/(5120 / 7201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (170532733 / 500000000) (341065467 / 1000000000) (Real.log (7201 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7201 / 5120) = -Real.log (5120 / 7201) := by
    rw [show ((7201 / 5120) : ℝ) = ((5120 / 7201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (20865037 / 40000000) ≤ -Real.log (3039 / 5120) ∧
    -Real.log (3039 / 5120) ≤ (260812963 / 500000000) := by
  have h := checkLog_sound (w := (2081 / 8159)) (n := 12)
    (lo := (20865037 / 40000000)) (hi := (260812963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3039) = 1/(3039 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-260812963 / 500000000) (-20865037 / 40000000) (Real.log (3039 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (34064877 / 100000000) ≤ -Real.log (2560 / 3599) ∧
    -Real.log (2560 / 3599) ≤ (340648771 / 1000000000) := by
  have h := checkLog_sound (w := (1039 / 6159)) (n := 12)
    (lo := (34064877 / 100000000)) (hi := (340648771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3599 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3599 / 2560) = 1/(2560 / 3599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (34064877 / 100000000) (340648771 / 1000000000) (Real.log (3599 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3599 / 2560) = -Real.log (2560 / 3599) := by
    rw [show ((3599 / 2560) : ℝ) = ((2560 / 3599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (104127849 / 200000000) ≤ -Real.log (1521 / 2560) ∧
    -Real.log (1521 / 2560) ≤ (260319623 / 500000000) := by
  have h := checkLog_sound (w := (1039 / 4081)) (n := 12)
    (lo := (104127849 / 200000000)) (hi := (260319623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1521) = 1/(1521 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-260319623 / 500000000) (-104127849 / 200000000) (Real.log (1521 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (253946627 / 1000000000) ≤ -Real.log (1000000 / 1289103) ∧
    -Real.log (1000000 / 1289103) ≤ (63486657 / 250000000) := by
  have h := checkLog_sound (w := (289103 / 2289103)) (n := 12)
    (lo := (253946627 / 1000000000)) (hi := (63486657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289103 / 1000000) = 1/(1000000 / 1289103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (253946627 / 1000000000) (63486657 / 250000000) (Real.log (1289103 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1289103 / 1000000) = -Real.log (1000000 / 1289103) := by
    rw [show ((1289103 / 1000000) : ℝ) = ((1000000 / 1289103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (170613863 / 500000000) ≤ -Real.log (710897 / 1000000) ∧
    -Real.log (710897 / 1000000) ≤ (341227727 / 1000000000) := by
  have h := checkLog_sound (w := (289103 / 1710897)) (n := 12)
    (lo := (170613863 / 500000000)) (hi := (341227727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 710897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 710897) = 1/(710897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-341227727 / 1000000000) (-170613863 / 500000000) (Real.log (710897 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (254276259 / 1000000000) ≤ -Real.log (125000 / 161191) ∧
    -Real.log (125000 / 161191) ≤ (12713813 / 50000000) := by
  have h := checkLog_sound (w := (36191 / 286191)) (n := 12)
    (lo := (254276259 / 1000000000)) (hi := (12713813 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161191 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161191 / 125000) = 1/(125000 / 161191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (254276259 / 1000000000) (12713813 / 50000000) (Real.log (161191 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161191 / 125000) = -Real.log (125000 / 161191) := by
    rw [show ((161191 / 125000) : ℝ) = ((125000 / 161191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (341825741 / 1000000000) ≤ -Real.log (88809 / 125000) ∧
    -Real.log (88809 / 125000) ≤ (170912871 / 500000000) := by
  have h := checkLog_sound (w := (36191 / 213809)) (n := 12)
    (lo := (341825741 / 1000000000)) (hi := (170912871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88809) = 1/(88809 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-170912871 / 500000000) (-341825741 / 1000000000) (Real.log (88809 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190016871 / 1000000000) ≤ -Real.log (100000 / 120927) ∧
    -Real.log (100000 / 120927) ≤ (23752109 / 125000000) := by
  have h := checkLog_sound (w := (20927 / 220927)) (n := 12)
    (lo := (190016871 / 1000000000)) (hi := (23752109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120927 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120927 / 100000) = 1/(100000 / 120927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190016871 / 1000000000) (23752109 / 125000000) (Real.log (120927 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (120927 / 100000) = -Real.log (100000 / 120927) := by
    rw [show ((120927 / 100000) : ℝ) = ((100000 / 120927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (234798709 / 1000000000) ≤ -Real.log (79073 / 100000) ∧
    -Real.log (79073 / 100000) ≤ (23479871 / 100000000) := by
  have h := checkLog_sound (w := (20927 / 179073)) (n := 12)
    (lo := (234798709 / 1000000000)) (hi := (23479871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 79073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 79073) = 1/(79073 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-23479871 / 100000000) (-234798709 / 1000000000) (Real.log (79073 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (23785389 / 125000000) ≤ -Real.log (125000 / 151199) ∧
    -Real.log (125000 / 151199) ≤ (190283113 / 1000000000) := by
  have h := checkLog_sound (w := (26199 / 276199)) (n := 12)
    (lo := (23785389 / 125000000)) (hi := (190283113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151199 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151199 / 125000) = 1/(125000 / 151199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (23785389 / 125000000) (190283113 / 1000000000) (Real.log (151199 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (151199 / 125000) = -Real.log (125000 / 151199) := by
    rw [show ((151199 / 125000) : ℝ) = ((125000 / 151199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (235206011 / 1000000000) ≤ -Real.log (98801 / 125000) ∧
    -Real.log (98801 / 125000) ≤ (58801503 / 250000000) := by
  have h := checkLog_sound (w := (26199 / 223801)) (n := 12)
    (lo := (235206011 / 1000000000)) (hi := (58801503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98801) = 1/(98801 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-58801503 / 250000000) (-235206011 / 1000000000) (Real.log (98801 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (595174353 / 1000000000) ≤ -Real.log (500000000000 / 906673540611) ∧
    -Real.log (500000000000 / 906673540611) ≤ (297587177 / 500000000) := by
  have h := checkLog_sound (w := (406673540611 / 1406673540611)) (n := 12)
    (lo := (595174353 / 1000000000)) (hi := (297587177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((906673540611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(906673540611 / 500000000000) = 1/(500000000000 / 906673540611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (595174353 / 1000000000) (297587177 / 500000000) (Real.log (906673540611 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (906673540611 / 500000000000) = -Real.log (500000000000 / 906673540611) := by
    rw [show ((906673540611 / 500000000000) : ℝ) = ((500000000000 / 906673540611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (596102001 / 1000000000) ≤ -Real.log (50000000000 / 90751500411) ∧
    -Real.log (50000000000 / 90751500411) ≤ (298051001 / 500000000) := by
  have h := checkLog_sound (w := (40751500411 / 140751500411)) (n := 12)
    (lo := (596102001 / 1000000000)) (hi := (298051001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90751500411 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90751500411 / 50000000000) = 1/(50000000000 / 90751500411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (596102001 / 1000000000) (298051001 / 500000000) (Real.log (90751500411 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (90751500411 / 50000000000) = -Real.log (50000000000 / 90751500411) := by
    rw [show ((90751500411 / 50000000000) : ℝ) = ((50000000000 / 90751500411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (424815581 / 1000000000) ≤ -Real.log (250000000000 / 382327090157) ∧
    -Real.log (250000000000 / 382327090157) ≤ (212407791 / 500000000) := by
  have h := checkLog_sound (w := (132327090157 / 632327090157)) (n := 12)
    (lo := (424815581 / 1000000000)) (hi := (212407791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382327090157 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382327090157 / 250000000000) = 1/(250000000000 / 382327090157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (424815581 / 1000000000) (212407791 / 500000000) (Real.log (382327090157 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (382327090157 / 250000000000) = -Real.log (250000000000 / 382327090157) := by
    rw [show ((382327090157 / 250000000000) : ℝ) = ((250000000000 / 382327090157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (425489123 / 1000000000) ≤ -Real.log (500000000000 / 765169380877) ∧
    -Real.log (500000000000 / 765169380877) ≤ (106372281 / 250000000) := by
  have h := checkLog_sound (w := (265169380877 / 1265169380877)) (n := 12)
    (lo := (425489123 / 1000000000)) (hi := (106372281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765169380877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765169380877 / 500000000000) = 1/(500000000000 / 765169380877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (425489123 / 1000000000) (106372281 / 250000000) (Real.log (765169380877 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (765169380877 / 500000000000) = -Real.log (500000000000 / 765169380877) := by
    rw [show ((765169380877 / 500000000000) : ℝ) = ((500000000000 / 765169380877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0463

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0464Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0464
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

theorem reflection_log_1_neg : (184759987 / 1000000000) ≤ -Real.log (5120 / 6159) ∧
    -Real.log (5120 / 6159) ≤ (46189997 / 250000000) := by
  have h := checkLog_sound (w := (1039 / 11279)) (n := 12)
    (lo := (184759987 / 1000000000)) (hi := (46189997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6159 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6159 / 5120) = 1/(5120 / 6159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (184759987 / 1000000000) (46189997 / 250000000) (Real.log (6159 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6159 / 5120) = -Real.log (5120 / 6159) := by
    rw [show ((6159 / 5120) : ℝ) = ((5120 / 6159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (113406191 / 500000000) ≤ -Real.log (4081 / 5120) ∧
    -Real.log (4081 / 5120) ≤ (226812383 / 1000000000) := by
  have h := checkLog_sound (w := (1039 / 9201)) (n := 12)
    (lo := (113406191 / 500000000)) (hi := (226812383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4081) = 1/(4081 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-226812383 / 1000000000) (-113406191 / 500000000) (Real.log (4081 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (184516411 / 1000000000) ≤ -Real.log (2048 / 2463) ∧
    -Real.log (2048 / 2463) ≤ (46129103 / 250000000) := by
  have h := checkLog_sound (w := (415 / 4511)) (n := 12)
    (lo := (184516411 / 1000000000)) (hi := (46129103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2463 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2463 / 2048) = 1/(2048 / 2463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (184516411 / 1000000000) (46129103 / 250000000) (Real.log (2463 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2463 / 2048) = -Real.log (2048 / 2463) := by
    rw [show ((2463 / 2048) : ℝ) = ((2048 / 2463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (226444893 / 1000000000) ≤ -Real.log (1633 / 2048) ∧
    -Real.log (1633 / 2048) ≤ (113222447 / 500000000) := by
  have h := checkLog_sound (w := (415 / 3681)) (n := 12)
    (lo := (226444893 / 1000000000)) (hi := (113222447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1633) = 1/(1633 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-113222447 / 500000000) (-226444893 / 1000000000) (Real.log (1633 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (34064877 / 100000000) ≤ -Real.log (2560 / 3599) ∧
    -Real.log (2560 / 3599) ≤ (340648771 / 1000000000) := by
  have h := checkLog_sound (w := (1039 / 6159)) (n := 12)
    (lo := (34064877 / 100000000)) (hi := (340648771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3599 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3599 / 2560) = 1/(2560 / 3599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (34064877 / 100000000) (340648771 / 1000000000) (Real.log (3599 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3599 / 2560) = -Real.log (2560 / 3599) := by
    rw [show ((3599 / 2560) : ℝ) = ((2560 / 3599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104127849 / 200000000) ≤ -Real.log (1521 / 2560) ∧
    -Real.log (1521 / 2560) ≤ (260319623 / 500000000) := by
  have h := checkLog_sound (w := (1039 / 4081)) (n := 12)
    (lo := (104127849 / 200000000)) (hi := (260319623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1521) = 1/(1521 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-260319623 / 500000000) (-104127849 / 200000000) (Real.log (1521 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (340231901 / 1000000000) ≤ -Real.log (1024 / 1439) ∧
    -Real.log (1024 / 1439) ≤ (170115951 / 500000000) := by
  have h := checkLog_sound (w := (415 / 2463)) (n := 12)
    (lo := (340231901 / 1000000000)) (hi := (170115951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439 / 1024) = 1/(1024 / 1439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (340231901 / 1000000000) (170115951 / 500000000) (Real.log (1439 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1439 / 1024) = -Real.log (1024 / 1439) := by
    rw [show ((1439 / 1024) : ℝ) = ((1024 / 1439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (519653537 / 1000000000) ≤ -Real.log (609 / 1024) ∧
    -Real.log (609 / 1024) ≤ (259826769 / 500000000) := by
  have h := checkLog_sound (w := (415 / 1633)) (n := 12)
    (lo := (519653537 / 1000000000)) (hi := (259826769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 609) = 1/(609 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-259826769 / 500000000) (-519653537 / 1000000000) (Real.log (609 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (126808831 / 500000000) ≤ -Real.log (1000000 / 1288679) ∧
    -Real.log (1000000 / 1288679) ≤ (253617663 / 1000000000) := by
  have h := checkLog_sound (w := (288679 / 2288679)) (n := 12)
    (lo := (126808831 / 500000000)) (hi := (253617663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1288679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1288679 / 1000000) = 1/(1000000 / 1288679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (126808831 / 500000000) (253617663 / 1000000000) (Real.log (1288679 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1288679 / 1000000) = -Real.log (1000000 / 1288679) := by
    rw [show ((1288679 / 1000000) : ℝ) = ((1000000 / 1288679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (170315737 / 500000000) ≤ -Real.log (711321 / 1000000) ∧
    -Real.log (711321 / 1000000) ≤ (13625259 / 40000000) := by
  have h := checkLog_sound (w := (288679 / 1711321)) (n := 12)
    (lo := (170315737 / 500000000)) (hi := (13625259 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 711321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 711321) = 1/(711321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13625259 / 40000000) (-170315737 / 500000000) (Real.log (711321 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (253947403 / 1000000000) ≤ -Real.log (62500 / 80569) ∧
    -Real.log (62500 / 80569) ≤ (63486851 / 250000000) := by
  have h := checkLog_sound (w := (18069 / 143069)) (n := 12)
    (lo := (253947403 / 1000000000)) (hi := (63486851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80569 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80569 / 62500) = 1/(62500 / 80569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (253947403 / 1000000000) (63486851 / 250000000) (Real.log (80569 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (80569 / 62500) = -Real.log (62500 / 80569) := by
    rw [show ((80569 / 62500) : ℝ) = ((62500 / 80569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (85307283 / 250000000) ≤ -Real.log (44431 / 62500) ∧
    -Real.log (44431 / 62500) ≤ (341229133 / 1000000000) := by
  have h := checkLog_sound (w := (18069 / 106931)) (n := 12)
    (lo := (85307283 / 250000000)) (hi := (341229133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44431) = 1/(44431 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-341229133 / 1000000000) (-85307283 / 250000000) (Real.log (44431 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (189750559 / 1000000000) ≤ -Real.log (250000 / 302237) ∧
    -Real.log (250000 / 302237) ≤ (1185941 / 6250000) := by
  have h := checkLog_sound (w := (52237 / 552237)) (n := 12)
    (lo := (189750559 / 1000000000)) (hi := (1185941 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302237 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302237 / 250000) = 1/(250000 / 302237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (189750559 / 1000000000) (1185941 / 6250000) (Real.log (302237 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (302237 / 250000) = -Real.log (250000 / 302237) := by
    rw [show ((302237 / 250000) : ℝ) = ((250000 / 302237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (234391573 / 1000000000) ≤ -Real.log (197763 / 250000) ∧
    -Real.log (197763 / 250000) ≤ (117195787 / 500000000) := by
  have h := checkLog_sound (w := (52237 / 447763)) (n := 12)
    (lo := (234391573 / 1000000000)) (hi := (117195787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197763) = 1/(197763 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-117195787 / 500000000) (-234391573 / 1000000000) (Real.log (197763 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (95008849 / 500000000) ≤ -Real.log (1000000 / 1209271) ∧
    -Real.log (1000000 / 1209271) ≤ (190017699 / 1000000000) := by
  have h := checkLog_sound (w := (209271 / 2209271)) (n := 12)
    (lo := (95008849 / 500000000)) (hi := (190017699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209271 / 1000000) = 1/(1000000 / 1209271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95008849 / 500000000) (190017699 / 1000000000) (Real.log (1209271 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1209271 / 1000000) = -Real.log (1000000 / 1209271) := by
    rw [show ((1209271 / 1000000) : ℝ) = ((1000000 / 1209271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (117399987 / 500000000) ≤ -Real.log (790729 / 1000000) ∧
    -Real.log (790729 / 1000000) ≤ (9391999 / 40000000) := by
  have h := checkLog_sound (w := (209271 / 1790729)) (n := 12)
    (lo := (117399987 / 500000000)) (hi := (9391999 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790729) = 1/(790729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-9391999 / 40000000) (-117399987 / 500000000) (Real.log (790729 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (37140571 / 62500000) ≤ -Real.log (100000000000 / 181167011799) ∧
    -Real.log (100000000000 / 181167011799) ≤ (594249137 / 1000000000) := by
  have h := checkLog_sound (w := (81167011799 / 281167011799)) (n := 12)
    (lo := (37140571 / 62500000)) (hi := (594249137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181167011799 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181167011799 / 100000000000) = 1/(100000000000 / 181167011799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (37140571 / 62500000) (594249137 / 1000000000) (Real.log (181167011799 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (181167011799 / 100000000000) = -Real.log (100000000000 / 181167011799) := by
    rw [show ((181167011799 / 100000000000) : ℝ) = ((100000000000 / 181167011799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (74397067 / 125000000) ≤ -Real.log (100000000000 / 181335103869) ∧
    -Real.log (100000000000 / 181335103869) ≤ (595176537 / 1000000000) := by
  have h := checkLog_sound (w := (81335103869 / 281335103869)) (n := 12)
    (lo := (74397067 / 125000000)) (hi := (595176537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181335103869 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181335103869 / 100000000000) = 1/(100000000000 / 181335103869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (74397067 / 125000000) (595176537 / 1000000000) (Real.log (181335103869 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (181335103869 / 100000000000) = -Real.log (100000000000 / 181335103869) := by
    rw [show ((181335103869 / 100000000000) : ℝ) = ((100000000000 / 181335103869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (424142133 / 1000000000) ≤ -Real.log (500000000000 / 764139399179) ∧
    -Real.log (500000000000 / 764139399179) ≤ (212071067 / 500000000) := by
  have h := checkLog_sound (w := (264139399179 / 1264139399179)) (n := 12)
    (lo := (424142133 / 1000000000)) (hi := (212071067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764139399179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764139399179 / 500000000000) = 1/(500000000000 / 764139399179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (424142133 / 1000000000) (212071067 / 500000000) (Real.log (764139399179 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (764139399179 / 500000000000) = -Real.log (500000000000 / 764139399179) := by
    rw [show ((764139399179 / 500000000000) : ℝ) = ((500000000000 / 764139399179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (53102209 / 125000000) ≤ -Real.log (500000000000 / 764655779667) ∧
    -Real.log (500000000000 / 764655779667) ≤ (424817673 / 1000000000) := by
  have h := checkLog_sound (w := (264655779667 / 1264655779667)) (n := 12)
    (lo := (53102209 / 125000000)) (hi := (424817673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764655779667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764655779667 / 500000000000) = 1/(500000000000 / 764655779667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (53102209 / 125000000) (424817673 / 1000000000) (Real.log (764655779667 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (764655779667 / 500000000000) = -Real.log (500000000000 / 764655779667) := by
    rw [show ((764655779667 / 500000000000) : ℝ) = ((500000000000 / 764655779667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0464

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0465Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0465
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

theorem reflection_log_1_neg : (184516411 / 1000000000) ≤ -Real.log (2048 / 2463) ∧
    -Real.log (2048 / 2463) ≤ (46129103 / 250000000) := by
  have h := checkLog_sound (w := (415 / 4511)) (n := 12)
    (lo := (184516411 / 1000000000)) (hi := (46129103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2463 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2463 / 2048) = 1/(2048 / 2463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (184516411 / 1000000000) (46129103 / 250000000) (Real.log (2463 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2463 / 2048) = -Real.log (2048 / 2463) := by
    rw [show ((2463 / 2048) : ℝ) = ((2048 / 2463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (226444893 / 1000000000) ≤ -Real.log (1633 / 2048) ∧
    -Real.log (1633 / 2048) ≤ (113222447 / 500000000) := by
  have h := checkLog_sound (w := (415 / 3681)) (n := 12)
    (lo := (226444893 / 1000000000)) (hi := (113222447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1633) = 1/(1633 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113222447 / 500000000) (-226444893 / 1000000000) (Real.log (1633 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (23034097 / 125000000) ≤ -Real.log (1280 / 1539) ∧
    -Real.log (1280 / 1539) ≤ (184272777 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2819)) (n := 12)
    (lo := (23034097 / 125000000)) (hi := (184272777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539 / 1280) = 1/(1280 / 1539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (23034097 / 125000000) (184272777 / 1000000000) (Real.log (1539 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1539 / 1280) = -Real.log (1280 / 1539) := by
    rw [show ((1539 / 1280) : ℝ) = ((1280 / 1539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (113038769 / 500000000) ≤ -Real.log (1021 / 1280) ∧
    -Real.log (1021 / 1280) ≤ (226077539 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2301)) (n := 12)
    (lo := (113038769 / 500000000)) (hi := (226077539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1021) = 1/(1021 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-226077539 / 1000000000) (-113038769 / 500000000) (Real.log (1021 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (340231901 / 1000000000) ≤ -Real.log (1024 / 1439) ∧
    -Real.log (1024 / 1439) ≤ (170115951 / 500000000) := by
  have h := checkLog_sound (w := (415 / 2463)) (n := 12)
    (lo := (340231901 / 1000000000)) (hi := (170115951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439 / 1024) = 1/(1024 / 1439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (340231901 / 1000000000) (170115951 / 500000000) (Real.log (1439 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1439 / 1024) = -Real.log (1024 / 1439) := by
    rw [show ((1439 / 1024) : ℝ) = ((1024 / 1439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (519653537 / 1000000000) ≤ -Real.log (609 / 1024) ∧
    -Real.log (609 / 1024) ≤ (259826769 / 500000000) := by
  have h := checkLog_sound (w := (415 / 1633)) (n := 12)
    (lo := (519653537 / 1000000000)) (hi := (259826769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 609) = 1/(609 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-259826769 / 500000000) (-519653537 / 1000000000) (Real.log (609 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (169907429 / 500000000) ≤ -Real.log (640 / 899) ∧
    -Real.log (640 / 899) ≤ (339814859 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1539)) (n := 12)
    (lo := (169907429 / 500000000)) (hi := (339814859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899 / 640) = 1/(640 / 899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (169907429 / 500000000) (339814859 / 1000000000) (Real.log (899 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (899 / 640) = -Real.log (640 / 899) := by
    rw [show ((899 / 640) : ℝ) = ((640 / 899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (518668801 / 1000000000) ≤ -Real.log (381 / 640) ∧
    -Real.log (381 / 640) ≤ (259334401 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1021)) (n := 12)
    (lo := (518668801 / 1000000000)) (hi := (259334401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 381) = 1/(381 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-259334401 / 500000000) (-518668801 / 1000000000) (Real.log (381 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (253288589 / 1000000000) ≤ -Real.log (200000 / 257651) ∧
    -Real.log (200000 / 257651) ≤ (25328859 / 100000000) := by
  have h := checkLog_sound (w := (57651 / 457651)) (n := 12)
    (lo := (253288589 / 1000000000)) (hi := (25328859 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257651 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257651 / 200000) = 1/(200000 / 257651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (253288589 / 1000000000) (25328859 / 100000000) (Real.log (257651 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (257651 / 200000) = -Real.log (200000 / 257651) := by
    rw [show ((257651 / 200000) : ℝ) = ((200000 / 257651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (340035577 / 1000000000) ≤ -Real.log (142349 / 200000) ∧
    -Real.log (142349 / 200000) ≤ (170017789 / 500000000) := by
  have h := checkLog_sound (w := (57651 / 342349)) (n := 12)
    (lo := (340035577 / 1000000000)) (hi := (170017789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 142349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 142349) = 1/(142349 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-170017789 / 500000000) (-340035577 / 1000000000) (Real.log (142349 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126809219 / 500000000) ≤ -Real.log (25000 / 32217) ∧
    -Real.log (25000 / 32217) ≤ (253618439 / 1000000000) := by
  have h := checkLog_sound (w := (7217 / 57217)) (n := 12)
    (lo := (126809219 / 500000000)) (hi := (253618439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32217 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32217 / 25000) = 1/(25000 / 32217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126809219 / 500000000) (253618439 / 1000000000) (Real.log (32217 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (32217 / 25000) = -Real.log (25000 / 32217) := by
    rw [show ((32217 / 25000) : ℝ) = ((25000 / 32217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4257911 / 12500000) ≤ -Real.log (17783 / 25000) ∧
    -Real.log (17783 / 25000) ≤ (340632881 / 1000000000) := by
  have h := checkLog_sound (w := (7217 / 42783)) (n := 12)
    (lo := (4257911 / 12500000)) (hi := (340632881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 17783) = 1/(17783 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-340632881 / 1000000000) (-4257911 / 12500000) (Real.log (17783 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (47371251 / 250000000) ≤ -Real.log (1000000 / 1208627) ∧
    -Real.log (1000000 / 1208627) ≤ (37897001 / 200000000) := by
  have h := checkLog_sound (w := (208627 / 2208627)) (n := 12)
    (lo := (47371251 / 250000000)) (hi := (37897001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208627 / 1000000) = 1/(1000000 / 1208627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (47371251 / 250000000) (37897001 / 200000000) (Real.log (1208627 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1208627 / 1000000) = -Real.log (1000000 / 1208627) := by
    rw [show ((1208627 / 1000000) : ℝ) = ((1000000 / 1208627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (233985867 / 1000000000) ≤ -Real.log (791373 / 1000000) ∧
    -Real.log (791373 / 1000000) ≤ (58496467 / 250000000) := by
  have h := checkLog_sound (w := (208627 / 1791373)) (n := 12)
    (lo := (233985867 / 1000000000)) (hi := (58496467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791373) = 1/(791373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-58496467 / 250000000) (-233985867 / 1000000000) (Real.log (791373 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (189751387 / 1000000000) ≤ -Real.log (1000000 / 1208949) ∧
    -Real.log (1000000 / 1208949) ≤ (47437847 / 250000000) := by
  have h := checkLog_sound (w := (208949 / 2208949)) (n := 12)
    (lo := (189751387 / 1000000000)) (hi := (47437847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208949 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208949 / 1000000) = 1/(1000000 / 1208949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (189751387 / 1000000000) (47437847 / 250000000) (Real.log (1208949 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1208949 / 1000000) = -Real.log (1000000 / 1208949) := by
    rw [show ((1208949 / 1000000) : ℝ) = ((1000000 / 1208949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (234392837 / 1000000000) ≤ -Real.log (791051 / 1000000) ∧
    -Real.log (791051 / 1000000) ≤ (117196419 / 500000000) := by
  have h := checkLog_sound (w := (208949 / 1791051)) (n := 12)
    (lo := (234392837 / 1000000000)) (hi := (117196419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791051) = 1/(791051 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-117196419 / 500000000) (-234392837 / 1000000000) (Real.log (791051 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (593324167 / 1000000000) ≤ -Real.log (500000000000 / 904997576379) ∧
    -Real.log (500000000000 / 904997576379) ≤ (74165521 / 125000000) := by
  have h := checkLog_sound (w := (404997576379 / 1404997576379)) (n := 12)
    (lo := (593324167 / 1000000000)) (hi := (74165521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904997576379 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904997576379 / 500000000000) = 1/(500000000000 / 904997576379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (593324167 / 1000000000) (74165521 / 125000000) (Real.log (904997576379 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (904997576379 / 500000000000) = -Real.log (500000000000 / 904997576379) := by
    rw [show ((904997576379 / 500000000000) : ℝ) = ((500000000000 / 904997576379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (297125659 / 500000000) ≤ -Real.log (500000000000 / 905837035371) ∧
    -Real.log (500000000000 / 905837035371) ≤ (594251319 / 1000000000) := by
  have h := checkLog_sound (w := (405837035371 / 1405837035371)) (n := 12)
    (lo := (297125659 / 500000000)) (hi := (594251319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((905837035371 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(905837035371 / 500000000000) = 1/(500000000000 / 905837035371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (297125659 / 500000000) (594251319 / 1000000000) (Real.log (905837035371 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (905837035371 / 500000000000) = -Real.log (500000000000 / 905837035371) := by
    rw [show ((905837035371 / 500000000000) : ℝ) = ((500000000000 / 905837035371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (423470871 / 1000000000) ≤ -Real.log (500000000000 / 763626633711) ∧
    -Real.log (500000000000 / 763626633711) ≤ (52933859 / 125000000) := by
  have h := checkLog_sound (w := (263626633711 / 1263626633711)) (n := 12)
    (lo := (423470871 / 1000000000)) (hi := (52933859 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763626633711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763626633711 / 500000000000) = 1/(500000000000 / 763626633711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (423470871 / 1000000000) (52933859 / 125000000) (Real.log (763626633711 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (763626633711 / 500000000000) = -Real.log (500000000000 / 763626633711) := by
    rw [show ((763626633711 / 500000000000) : ℝ) = ((500000000000 / 763626633711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (16965769 / 40000000) ≤ -Real.log (500000000000 / 764140997231) ∧
    -Real.log (500000000000 / 764140997231) ≤ (212072113 / 500000000) := by
  have h := checkLog_sound (w := (264140997231 / 1264140997231)) (n := 12)
    (lo := (16965769 / 40000000)) (hi := (212072113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764140997231 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764140997231 / 500000000000) = 1/(500000000000 / 764140997231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (16965769 / 40000000) (212072113 / 500000000) (Real.log (764140997231 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (764140997231 / 500000000000) = -Real.log (500000000000 / 764140997231) := by
    rw [show ((764140997231 / 500000000000) : ℝ) = ((500000000000 / 764140997231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0465

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0466Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0466
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

theorem reflection_log_1_neg : (23034097 / 125000000) ≤ -Real.log (1280 / 1539) ∧
    -Real.log (1280 / 1539) ≤ (184272777 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2819)) (n := 12)
    (lo := (23034097 / 125000000)) (hi := (184272777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539 / 1280) = 1/(1280 / 1539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (23034097 / 125000000) (184272777 / 1000000000) (Real.log (1539 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1539 / 1280) = -Real.log (1280 / 1539) := by
    rw [show ((1539 / 1280) : ℝ) = ((1280 / 1539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (113038769 / 500000000) ≤ -Real.log (1021 / 1280) ∧
    -Real.log (1021 / 1280) ≤ (226077539 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2301)) (n := 12)
    (lo := (113038769 / 500000000)) (hi := (226077539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1021) = 1/(1021 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-226077539 / 1000000000) (-113038769 / 500000000) (Real.log (1021 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (92014541 / 500000000) ≤ -Real.log (10240 / 12309) ∧
    -Real.log (10240 / 12309) ≤ (184029083 / 1000000000) := by
  have h := checkLog_sound (w := (2069 / 22549)) (n := 12)
    (lo := (92014541 / 500000000)) (hi := (184029083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12309 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12309 / 10240) = 1/(10240 / 12309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (92014541 / 500000000) (184029083 / 1000000000) (Real.log (12309 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12309 / 10240) = -Real.log (10240 / 12309) := by
    rw [show ((12309 / 10240) : ℝ) = ((10240 / 12309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (225710319 / 1000000000) ≤ -Real.log (8171 / 10240) ∧
    -Real.log (8171 / 10240) ≤ (2821379 / 12500000) := by
  have h := checkLog_sound (w := (2069 / 18411)) (n := 12)
    (lo := (225710319 / 1000000000)) (hi := (2821379 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8171) = 1/(8171 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2821379 / 12500000) (-225710319 / 1000000000) (Real.log (8171 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (169907429 / 500000000) ≤ -Real.log (640 / 899) ∧
    -Real.log (640 / 899) ≤ (339814859 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1539)) (n := 12)
    (lo := (169907429 / 500000000)) (hi := (339814859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899 / 640) = 1/(640 / 899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (169907429 / 500000000) (339814859 / 1000000000) (Real.log (899 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (899 / 640) = -Real.log (640 / 899) := by
    rw [show ((899 / 640) : ℝ) = ((640 / 899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (518668801 / 1000000000) ≤ -Real.log (381 / 640) ∧
    -Real.log (381 / 640) ≤ (259334401 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1021)) (n := 12)
    (lo := (518668801 / 1000000000)) (hi := (259334401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 381) = 1/(381 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-259334401 / 500000000) (-518668801 / 1000000000) (Real.log (381 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8484941 / 25000000) ≤ -Real.log (5120 / 7189) ∧
    -Real.log (5120 / 7189) ≤ (339397641 / 1000000000) := by
  have h := checkLog_sound (w := (2069 / 12309)) (n := 12)
    (lo := (8484941 / 25000000)) (hi := (339397641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7189 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7189 / 5120) = 1/(5120 / 7189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8484941 / 25000000) (339397641 / 1000000000) (Real.log (7189 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7189 / 5120) = -Real.log (5120 / 7189) := by
    rw [show ((7189 / 5120) : ℝ) = ((5120 / 7189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (517685033 / 1000000000) ≤ -Real.log (3051 / 5120) ∧
    -Real.log (3051 / 5120) ≤ (258842517 / 500000000) := by
  have h := checkLog_sound (w := (2069 / 8171)) (n := 12)
    (lo := (517685033 / 1000000000)) (hi := (258842517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3051) = 1/(3051 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-258842517 / 500000000) (-517685033 / 1000000000) (Real.log (3051 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252959407 / 1000000000) ≤ -Real.log (1000000 / 1287831) ∧
    -Real.log (1000000 / 1287831) ≤ (15809963 / 62500000) := by
  have h := checkLog_sound (w := (287831 / 2287831)) (n := 12)
    (lo := (252959407 / 1000000000)) (hi := (15809963 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287831 / 1000000) = 1/(1000000 / 1287831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252959407 / 1000000000) (15809963 / 62500000) (Real.log (1287831 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1287831 / 1000000) = -Real.log (1000000 / 1287831) := by
    rw [show ((1287831 / 1000000) : ℝ) = ((1000000 / 1287831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84860009 / 250000000) ≤ -Real.log (712169 / 1000000) ∧
    -Real.log (712169 / 1000000) ≤ (339440037 / 1000000000) := by
  have h := checkLog_sound (w := (287831 / 1712169)) (n := 12)
    (lo := (84860009 / 250000000)) (hi := (339440037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 712169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 712169) = 1/(712169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-339440037 / 1000000000) (-84860009 / 250000000) (Real.log (712169 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (50657873 / 200000000) ≤ -Real.log (15625 / 20129) ∧
    -Real.log (15625 / 20129) ≤ (126644683 / 500000000) := by
  have h := checkLog_sound (w := (2252 / 17877)) (n := 12)
    (lo := (50657873 / 200000000)) (hi := (126644683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20129 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20129 / 15625) = 1/(15625 / 20129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (50657873 / 200000000) (126644683 / 500000000) (Real.log (20129 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (20129 / 15625) = -Real.log (15625 / 20129) := by
    rw [show ((20129 / 15625) : ℝ) = ((15625 / 20129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (170018491 / 500000000) ≤ -Real.log (11121 / 15625) ∧
    -Real.log (11121 / 15625) ≤ (340036983 / 1000000000) := by
  have h := checkLog_sound (w := (2252 / 13373)) (n := 12)
    (lo := (170018491 / 500000000)) (hi := (340036983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11121) = 1/(11121 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-340036983 / 1000000000) (-170018491 / 500000000) (Real.log (11121 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94609689 / 500000000) ≤ -Real.log (500000 / 604153) ∧
    -Real.log (500000 / 604153) ≤ (189219379 / 1000000000) := by
  have h := checkLog_sound (w := (104153 / 1104153)) (n := 12)
    (lo := (94609689 / 500000000)) (hi := (189219379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604153 / 500000) = 1/(500000 / 604153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94609689 / 500000000) (189219379 / 1000000000) (Real.log (604153 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (604153 / 500000) = -Real.log (500000 / 604153) := by
    rw [show ((604153 / 500000) : ℝ) = ((500000 / 604153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9343213 / 40000000) ≤ -Real.log (395847 / 500000) ∧
    -Real.log (395847 / 500000) ≤ (116790163 / 500000000) := by
  have h := checkLog_sound (w := (104153 / 895847)) (n := 12)
    (lo := (9343213 / 40000000)) (hi := (116790163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 395847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 395847) = 1/(395847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-116790163 / 500000000) (-9343213 / 40000000) (Real.log (395847 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (189485831 / 1000000000) ≤ -Real.log (250000 / 302157) ∧
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


theorem reflection_log_15 : Bounds (189485831 / 1000000000) (23685729 / 125000000) (Real.log (302157 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (302157 / 250000) = -Real.log (250000 / 302157) := by
    rw [show ((302157 / 250000) : ℝ) = ((250000 / 302157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23398713 / 100000000) ≤ -Real.log (197843 / 250000) ∧
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


theorem reflection_log_16 : Bounds (-233987131 / 1000000000) (-23398713 / 100000000) (Real.log (197843 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (148099861 / 250000000) ≤ -Real.log (500000000000 / 904161090977) ∧
    -Real.log (500000000000 / 904161090977) ≤ (118479889 / 200000000) := by
  have h := checkLog_sound (w := (404161090977 / 1404161090977)) (n := 12)
    (lo := (148099861 / 250000000)) (hi := (118479889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904161090977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904161090977 / 500000000000) = 1/(500000000000 / 904161090977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (148099861 / 250000000) (118479889 / 200000000) (Real.log (904161090977 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (904161090977 / 500000000000) = -Real.log (500000000000 / 904161090977) := by
    rw [show ((904161090977 / 500000000000) : ℝ) = ((500000000000 / 904161090977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (148331587 / 250000000) ≤ -Real.log (500000000000 / 904999550401) ∧
    -Real.log (500000000000 / 904999550401) ≤ (593326349 / 1000000000) := by
  have h := checkLog_sound (w := (404999550401 / 1404999550401)) (n := 12)
    (lo := (148331587 / 250000000)) (hi := (593326349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904999550401 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904999550401 / 500000000000) = 1/(500000000000 / 904999550401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (148331587 / 250000000) (593326349 / 1000000000) (Real.log (904999550401 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (904999550401 / 500000000000) = -Real.log (500000000000 / 904999550401) := by
    rw [show ((904999550401 / 500000000000) : ℝ) = ((500000000000 / 904999550401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (52849963 / 125000000) ≤ -Real.log (250000000000 / 381557142027) ∧
    -Real.log (250000000000 / 381557142027) ≤ (84559941 / 200000000) := by
  have h := checkLog_sound (w := (131557142027 / 631557142027)) (n := 12)
    (lo := (52849963 / 125000000)) (hi := (84559941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381557142027 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381557142027 / 250000000000) = 1/(250000000000 / 381557142027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (52849963 / 125000000) (84559941 / 200000000) (Real.log (381557142027 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (381557142027 / 250000000000) = -Real.log (250000000000 / 381557142027) := by
    rw [show ((381557142027 / 250000000000) : ℝ) = ((250000000000 / 381557142027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (211736481 / 500000000) ≤ -Real.log (250000000000 / 381814115233) ∧
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


theorem reflection_log_20 : Bounds (211736481 / 500000000) (423472963 / 1000000000) (Real.log (381814115233 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (381814115233 / 250000000000) = -Real.log (250000000000 / 381814115233) := by
    rw [show ((381814115233 / 250000000000) : ℝ) = ((250000000000 / 381814115233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0466

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0467Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0467
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

theorem reflection_log_1_neg : (92014541 / 500000000) ≤ -Real.log (10240 / 12309) ∧
    -Real.log (10240 / 12309) ≤ (184029083 / 1000000000) := by
  have h := checkLog_sound (w := (2069 / 22549)) (n := 12)
    (lo := (92014541 / 500000000)) (hi := (184029083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12309 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12309 / 10240) = 1/(10240 / 12309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (92014541 / 500000000) (184029083 / 1000000000) (Real.log (12309 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12309 / 10240) = -Real.log (10240 / 12309) := by
    rw [show ((12309 / 10240) : ℝ) = ((10240 / 12309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (225710319 / 1000000000) ≤ -Real.log (8171 / 10240) ∧
    -Real.log (8171 / 10240) ≤ (2821379 / 12500000) := by
  have h := checkLog_sound (w := (2069 / 18411)) (n := 12)
    (lo := (225710319 / 1000000000)) (hi := (2821379 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8171) = 1/(8171 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2821379 / 12500000) (-225710319 / 1000000000) (Real.log (8171 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11486583 / 62500000) ≤ -Real.log (5120 / 6153) ∧
    -Real.log (5120 / 6153) ≤ (183785329 / 1000000000) := by
  have h := checkLog_sound (w := (1033 / 11273)) (n := 12)
    (lo := (11486583 / 62500000)) (hi := (183785329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6153 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6153 / 5120) = 1/(5120 / 6153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11486583 / 62500000) (183785329 / 1000000000) (Real.log (6153 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6153 / 5120) = -Real.log (5120 / 6153) := by
    rw [show ((6153 / 5120) : ℝ) = ((5120 / 6153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (112671617 / 500000000) ≤ -Real.log (4087 / 5120) ∧
    -Real.log (4087 / 5120) ≤ (45068647 / 200000000) := by
  have h := checkLog_sound (w := (1033 / 9207)) (n := 12)
    (lo := (112671617 / 500000000)) (hi := (45068647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4087) = 1/(4087 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45068647 / 200000000) (-112671617 / 500000000) (Real.log (4087 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8484941 / 25000000) ≤ -Real.log (5120 / 7189) ∧
    -Real.log (5120 / 7189) ≤ (339397641 / 1000000000) := by
  have h := checkLog_sound (w := (2069 / 12309)) (n := 12)
    (lo := (8484941 / 25000000)) (hi := (339397641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7189 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7189 / 5120) = 1/(5120 / 7189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8484941 / 25000000) (339397641 / 1000000000) (Real.log (7189 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7189 / 5120) = -Real.log (5120 / 7189) := by
    rw [show ((7189 / 5120) : ℝ) = ((5120 / 7189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (517685033 / 1000000000) ≤ -Real.log (3051 / 5120) ∧
    -Real.log (3051 / 5120) ≤ (258842517 / 500000000) := by
  have h := checkLog_sound (w := (2069 / 8171)) (n := 12)
    (lo := (517685033 / 1000000000)) (hi := (258842517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3051) = 1/(3051 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-258842517 / 500000000) (-517685033 / 1000000000) (Real.log (3051 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (338980249 / 1000000000) ≤ -Real.log (2560 / 3593) ∧
    -Real.log (2560 / 3593) ≤ (1355921 / 4000000) := by
  have h := checkLog_sound (w := (1033 / 6153)) (n := 12)
    (lo := (338980249 / 1000000000)) (hi := (1355921 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3593 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3593 / 2560) = 1/(2560 / 3593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (338980249 / 1000000000) (1355921 / 4000000) (Real.log (3593 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3593 / 2560) = -Real.log (2560 / 3593) := by
    rw [show ((3593 / 2560) : ℝ) = ((2560 / 3593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (64587779 / 125000000) ≤ -Real.log (1527 / 2560) ∧
    -Real.log (1527 / 2560) ≤ (516702233 / 1000000000) := by
  have h := checkLog_sound (w := (1033 / 4087)) (n := 12)
    (lo := (64587779 / 125000000)) (hi := (516702233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1527) = 1/(1527 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-516702233 / 1000000000) (-64587779 / 125000000) (Real.log (1527 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252630117 / 1000000000) ≤ -Real.log (1000000 / 1287407) ∧
    -Real.log (1000000 / 1287407) ≤ (126315059 / 500000000) := by
  have h := checkLog_sound (w := (287407 / 2287407)) (n := 12)
    (lo := (252630117 / 1000000000)) (hi := (126315059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287407 / 1000000) = 1/(1000000 / 1287407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252630117 / 1000000000) (126315059 / 500000000) (Real.log (1287407 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1287407 / 1000000) = -Real.log (1000000 / 1287407) := by
    rw [show ((1287407 / 1000000) : ℝ) = ((1000000 / 1287407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (338844849 / 1000000000) ≤ -Real.log (712593 / 1000000) ∧
    -Real.log (712593 / 1000000) ≤ (6776897 / 20000000) := by
  have h := checkLog_sound (w := (287407 / 1712593)) (n := 12)
    (lo := (338844849 / 1000000000)) (hi := (6776897 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 712593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 712593) = 1/(712593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-6776897 / 20000000) (-338844849 / 1000000000) (Real.log (712593 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31620023 / 125000000) ≤ -Real.log (125000 / 160979) ∧
    -Real.log (125000 / 160979) ≤ (50592037 / 200000000) := by
  have h := checkLog_sound (w := (35979 / 285979)) (n := 12)
    (lo := (31620023 / 125000000)) (hi := (50592037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160979 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160979 / 125000) = 1/(125000 / 160979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31620023 / 125000000) (50592037 / 200000000) (Real.log (160979 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (160979 / 125000) = -Real.log (125000 / 160979) := by
    rw [show ((160979 / 125000) : ℝ) = ((125000 / 160979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2121509 / 6250000) ≤ -Real.log (89021 / 125000) ∧
    -Real.log (89021 / 125000) ≤ (339441441 / 1000000000) := by
  have h := checkLog_sound (w := (35979 / 214021)) (n := 12)
    (lo := (2121509 / 6250000)) (hi := (339441441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89021) = 1/(89021 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-339441441 / 1000000000) (-2121509 / 6250000) (Real.log (89021 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94476841 / 500000000) ≤ -Real.log (200000 / 241597) ∧
    -Real.log (200000 / 241597) ≤ (188953683 / 1000000000) := by
  have h := checkLog_sound (w := (41597 / 441597)) (n := 12)
    (lo := (94476841 / 500000000)) (hi := (188953683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241597 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241597 / 200000) = 1/(200000 / 241597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94476841 / 500000000) (188953683 / 1000000000) (Real.log (241597 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (241597 / 200000) = -Real.log (200000 / 241597) := by
    rw [show ((241597 / 200000) : ℝ) = ((200000 / 241597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (233174947 / 1000000000) ≤ -Real.log (158403 / 200000) ∧
    -Real.log (158403 / 200000) ≤ (58293737 / 250000000) := by
  have h := checkLog_sound (w := (41597 / 358403)) (n := 12)
    (lo := (233174947 / 1000000000)) (hi := (58293737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158403) = 1/(158403 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-58293737 / 250000000) (-233174947 / 1000000000) (Real.log (158403 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (94610103 / 500000000) ≤ -Real.log (1000000 / 1208307) ∧
    -Real.log (1000000 / 1208307) ≤ (189220207 / 1000000000) := by
  have h := checkLog_sound (w := (208307 / 2208307)) (n := 12)
    (lo := (94610103 / 500000000)) (hi := (189220207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208307 / 1000000) = 1/(1000000 / 1208307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (94610103 / 500000000) (189220207 / 1000000000) (Real.log (1208307 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1208307 / 1000000) = -Real.log (1000000 / 1208307) := by
    rw [show ((1208307 / 1000000) : ℝ) = ((1000000 / 1208307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (58395397 / 250000000) ≤ -Real.log (791693 / 1000000) ∧
    -Real.log (791693 / 1000000) ≤ (233581589 / 1000000000) := by
  have h := checkLog_sound (w := (208307 / 1791693)) (n := 12)
    (lo := (58395397 / 250000000)) (hi := (233581589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791693) = 1/(791693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-233581589 / 1000000000) (-58395397 / 250000000) (Real.log (791693 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (295737483 / 500000000) ≤ -Real.log (500000000000 / 903325601009) ∧
    -Real.log (500000000000 / 903325601009) ≤ (591474967 / 1000000000) := by
  have h := checkLog_sound (w := (403325601009 / 1403325601009)) (n := 12)
    (lo := (295737483 / 500000000)) (hi := (591474967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903325601009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903325601009 / 500000000000) = 1/(500000000000 / 903325601009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (295737483 / 500000000) (591474967 / 1000000000) (Real.log (903325601009 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (903325601009 / 500000000000) = -Real.log (500000000000 / 903325601009) := by
    rw [show ((903325601009 / 500000000000) : ℝ) = ((500000000000 / 903325601009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (74050203 / 125000000) ≤ -Real.log (500000000000 / 904163062649) ∧
    -Real.log (500000000000 / 904163062649) ≤ (4739213 / 8000000) := by
  have h := checkLog_sound (w := (404163062649 / 1404163062649)) (n := 12)
    (lo := (74050203 / 125000000)) (hi := (4739213 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904163062649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904163062649 / 500000000000) = 1/(500000000000 / 904163062649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (74050203 / 125000000) (4739213 / 8000000) (Real.log (904163062649 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (904163062649 / 500000000000) = -Real.log (500000000000 / 904163062649) := by
    rw [show ((904163062649 / 500000000000) : ℝ) = ((500000000000 / 904163062649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (42212863 / 100000000) ≤ -Real.log (250000000000 / 381301174851) ∧
    -Real.log (250000000000 / 381301174851) ≤ (422128631 / 1000000000) := by
  have h := checkLog_sound (w := (131301174851 / 631301174851)) (n := 12)
    (lo := (42212863 / 100000000)) (hi := (422128631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381301174851 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381301174851 / 250000000000) = 1/(250000000000 / 381301174851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (42212863 / 100000000) (422128631 / 1000000000) (Real.log (381301174851 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (381301174851 / 250000000000) = -Real.log (250000000000 / 381301174851) := by
    rw [show ((381301174851 / 250000000000) : ℝ) = ((250000000000 / 381301174851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (211400897 / 500000000) ≤ -Real.log (250000000000 / 381557939757) ∧
    -Real.log (250000000000 / 381557939757) ≤ (84560359 / 200000000) := by
  have h := checkLog_sound (w := (131557939757 / 631557939757)) (n := 12)
    (lo := (211400897 / 500000000)) (hi := (84560359 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381557939757 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381557939757 / 250000000000) = 1/(250000000000 / 381557939757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (211400897 / 500000000) (84560359 / 200000000) (Real.log (381557939757 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (381557939757 / 250000000000) = -Real.log (250000000000 / 381557939757) := by
    rw [show ((381557939757 / 250000000000) : ℝ) = ((250000000000 / 381557939757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0467

end


