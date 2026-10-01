-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0100Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0100Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:28:02.831757+00:00
-- url     : https://prove2.me/theorems/a949db69-18d3-4e61-8b63-4a080f4b6008
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0100Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0101Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0100Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0101Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0102Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0103Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0104Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0100Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0101Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0102Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0103Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0104Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0100Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0101Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0102Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0103Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0104Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0100Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0101Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0102Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0103Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0104Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0100Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0100
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

theorem reflection_log_1_neg : (4167479 / 12500000) ≤ -Real.log (2560 / 3573) ∧
    -Real.log (2560 / 3573) ≤ (333398321 / 1000000000) := by
  have h := checkLog_sound (w := (1013 / 6133)) (n := 12)
    (lo := (4167479 / 12500000)) (hi := (333398321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3573 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3573 / 2560) = 1/(2560 / 3573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (4167479 / 12500000) (333398321 / 1000000000) (Real.log (3573 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3573 / 2560) = -Real.log (2560 / 3573) := by
    rw [show ((3573 / 2560) : ℝ) = ((2560 / 3573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (251844843 / 500000000) ≤ -Real.log (1547 / 2560) ∧
    -Real.log (1547 / 2560) ≤ (503689687 / 1000000000) := by
  have h := checkLog_sound (w := (1013 / 4107)) (n := 12)
    (lo := (251844843 / 500000000)) (hi := (503689687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1547) = 1/(1547 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-503689687 / 1000000000) (-251844843 / 500000000) (Real.log (1547 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (332558337 / 1000000000) ≤ -Real.log (256 / 357) ∧
    -Real.log (256 / 357) ≤ (166279169 / 500000000) := by
  have h := checkLog_sound (w := (101 / 613)) (n := 12)
    (lo := (332558337 / 1000000000)) (hi := (166279169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357 / 256) = 1/(256 / 357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (332558337 / 1000000000) (166279169 / 500000000) (Real.log (357 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (357 / 256) = -Real.log (256 / 357) := by
    rw [show ((357 / 256) : ℝ) = ((256 / 357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (501752327 / 1000000000) ≤ -Real.log (155 / 256) ∧
    -Real.log (155 / 256) ≤ (62719041 / 125000000) := by
  have h := checkLog_sound (w := (101 / 411)) (n := 12)
    (lo := (501752327 / 1000000000)) (hi := (62719041 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 155) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 155) = 1/(155 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-62719041 / 125000000) (-501752327 / 1000000000) (Real.log (155 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23320037 / 40000000) ≤ -Real.log (1280 / 2293) ∧
    -Real.log (1280 / 2293) ≤ (291500463 / 500000000) := by
  have h := checkLog_sound (w := (1013 / 3573)) (n := 12)
    (lo := (23320037 / 40000000)) (hi := (291500463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2293 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2293 / 1280) = 1/(1280 / 2293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23320037 / 40000000) (291500463 / 500000000) (Real.log (2293 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2293 / 1280) = -Real.log (1280 / 2293) := by
    rw [show ((2293 / 1280) : ℝ) = ((1280 / 2293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1567366697 / 1000000000) ≤ -Real.log (267 / 1280) ∧
    -Real.log (267 / 1280) ≤ (15673667 / 10000000) := by
  have h := checkLog_sound (w := (53 / 587)) (n := 12)
    (lo := (181072337 / 1000000000)) (hi := (90536169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 267) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 267) = 1/(267 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-15673667 / 10000000) (-1567366697 / 1000000000) (Real.log (267 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (581691739 / 1000000000) ≤ -Real.log (128 / 229) ∧
    -Real.log (128 / 229) ≤ (29084587 / 50000000) := by
  have h := checkLog_sound (w := (101 / 357)) (n := 12)
    (lo := (581691739 / 1000000000)) (hi := (29084587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229 / 128) = 1/(128 / 229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (581691739 / 1000000000) (29084587 / 50000000) (Real.log (229 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (229 / 128) = -Real.log (128 / 229) := by
    rw [show ((229 / 128) : ℝ) = ((128 / 229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (389048349 / 250000000) ≤ -Real.log (27 / 128) ∧
    -Real.log (27 / 128) ≤ (1556193399 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 27) = 1/(27 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1556193399 / 1000000000) (-389048349 / 250000000) (Real.log (27 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (456385699 / 1000000000) ≤ -Real.log (1000000 / 1578359) ∧
    -Real.log (1000000 / 1578359) ≤ (4563857 / 10000000) := by
  have h := checkLog_sound (w := (578359 / 2578359)) (n := 12)
    (lo := (456385699 / 1000000000)) (hi := (4563857 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1578359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1578359 / 1000000) = 1/(1000000 / 1578359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (456385699 / 1000000000) (4563857 / 10000000) (Real.log (1578359 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1578359 / 1000000) = -Real.log (1000000 / 1578359) := by
    rw [show ((1578359 / 1000000) : ℝ) = ((1000000 / 1578359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (863601037 / 1000000000) ≤ -Real.log (421641 / 1000000) ∧
    -Real.log (421641 / 1000000) ≤ (863601039 / 1000000000) := by
  have h := checkLog_sound (w := (78359 / 921641)) (n := 12)
    (lo := (170453857 / 1000000000)) (hi := (85226929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421641) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 421641) = 1/(421641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-863601039 / 1000000000) (-863601037 / 1000000000) (Real.log (421641 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (45758939 / 100000000) ≤ -Real.log (50000 / 79013) ∧
    -Real.log (50000 / 79013) ≤ (457589391 / 1000000000) := by
  have h := checkLog_sound (w := (29013 / 129013)) (n := 12)
    (lo := (45758939 / 100000000)) (hi := (457589391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79013 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79013 / 50000) = 1/(50000 / 79013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (45758939 / 100000000) (457589391 / 1000000000) (Real.log (79013 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (79013 / 50000) = -Real.log (50000 / 79013) := by
    rw [show ((79013 / 50000) : ℝ) = ((50000 / 79013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (434059903 / 500000000) ≤ -Real.log (20987 / 50000) ∧
    -Real.log (20987 / 50000) ≤ (3391093 / 3906250) := by
  have h := checkLog_sound (w := (4013 / 45987)) (n := 12)
    (lo := (87486313 / 500000000)) (hi := (174972627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 20987) = 1/(20987 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3391093 / 3906250) (-434059903 / 500000000) (Real.log (20987 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (37183869 / 100000000) ≤ -Real.log (1000000 / 1450399) ∧
    -Real.log (1000000 / 1450399) ≤ (371838691 / 1000000000) := by
  have h := checkLog_sound (w := (450399 / 2450399)) (n := 12)
    (lo := (37183869 / 100000000)) (hi := (371838691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1450399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1450399 / 1000000) = 1/(1000000 / 1450399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (37183869 / 100000000) (371838691 / 1000000000) (Real.log (1450399 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1450399 / 1000000) = -Real.log (1000000 / 1450399) := by
    rw [show ((1450399 / 1000000) : ℝ) = ((1000000 / 1450399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (299281359 / 500000000) ≤ -Real.log (549601 / 1000000) ∧
    -Real.log (549601 / 1000000) ≤ (598562719 / 1000000000) := by
  have h := checkLog_sound (w := (450399 / 1549601)) (n := 12)
    (lo := (299281359 / 500000000)) (hi := (598562719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 549601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 549601) = 1/(549601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-598562719 / 1000000000) (-299281359 / 500000000) (Real.log (549601 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (373063809 / 1000000000) ≤ -Real.log (1000000 / 1452177) ∧
    -Real.log (1000000 / 1452177) ≤ (37306381 / 100000000) := by
  have h := checkLog_sound (w := (452177 / 2452177)) (n := 12)
    (lo := (373063809 / 1000000000)) (hi := (37306381 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1452177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1452177 / 1000000) = 1/(1000000 / 1452177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (373063809 / 1000000000) (37306381 / 100000000) (Real.log (1452177 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1452177 / 1000000) = -Real.log (1000000 / 1452177) := by
    rw [show ((1452177 / 1000000) : ℝ) = ((1000000 / 1452177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (150450759 / 250000000) ≤ -Real.log (547823 / 1000000) ∧
    -Real.log (547823 / 1000000) ≤ (601803037 / 1000000000) := by
  have h := checkLog_sound (w := (452177 / 1547823)) (n := 12)
    (lo := (150450759 / 250000000)) (hi := (601803037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 547823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 547823) = 1/(547823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-601803037 / 1000000000) (-150450759 / 250000000) (Real.log (547823 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1319986737 / 1000000000) ≤ -Real.log (500000000000 / 1871685865463) ∧
    -Real.log (500000000000 / 1871685865463) ≤ (1319986739 / 1000000000) := by
  have h := checkLog_sound (w := (871685865463 / 2871685865463)) (n := 12)
    (lo := (626839557 / 1000000000)) (hi := (313419779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1871685865463 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1871685865463 / 1000000000000) = 1/(500000000000 / 1871685865463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1319986737 / 1000000000) (1319986739 / 1000000000) (Real.log (1871685865463 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1871685865463 / 500000000000) = -Real.log (500000000000 / 1871685865463) := by
    rw [show ((1871685865463 / 500000000000) : ℝ) = ((500000000000 / 1871685865463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (331427299 / 250000000) ≤ -Real.log (500000000000 / 1882427216849) ∧
    -Real.log (500000000000 / 1882427216849) ≤ (662854599 / 500000000) := by
  have h := checkLog_sound (w := (882427216849 / 2882427216849)) (n := 12)
    (lo := (19767563 / 31250000)) (hi := (632562017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1882427216849 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1882427216849 / 1000000000000) = 1/(500000000000 / 1882427216849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (331427299 / 250000000) (662854599 / 500000000) (Real.log (1882427216849 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1882427216849 / 500000000000) = -Real.log (500000000000 / 1882427216849) := by
    rw [show ((1882427216849 / 500000000000) : ℝ) = ((500000000000 / 1882427216849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (970401409 / 1000000000) ≤ -Real.log (500000000000 / 1319501784021) ∧
    -Real.log (500000000000 / 1319501784021) ≤ (970401411 / 1000000000) := by
  have h := checkLog_sound (w := (319501784021 / 2319501784021)) (n := 12)
    (lo := (277254229 / 1000000000)) (hi := (27725423 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319501784021 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1319501784021 / 1000000000000) = 1/(500000000000 / 1319501784021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (970401409 / 1000000000) (970401411 / 1000000000) (Real.log (1319501784021 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1319501784021 / 500000000000) = -Real.log (500000000000 / 1319501784021) := by
    rw [show ((1319501784021 / 500000000000) : ℝ) = ((500000000000 / 1319501784021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (487433423 / 500000000) ≤ -Real.log (250000000000 / 662703555711) ∧
    -Real.log (250000000000 / 662703555711) ≤ (30464589 / 31250000) := by
  have h := checkLog_sound (w := (162703555711 / 1162703555711)) (n := 12)
    (lo := (140859833 / 500000000)) (hi := (281719667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662703555711 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(662703555711 / 500000000000) = 1/(250000000000 / 662703555711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (487433423 / 500000000) (30464589 / 31250000) (Real.log (662703555711 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (662703555711 / 250000000000) = -Real.log (250000000000 / 662703555711) := by
    rw [show ((662703555711 / 250000000000) : ℝ) = ((250000000000 / 662703555711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0100

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0101Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0101
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

theorem reflection_log_1_neg : (332558337 / 1000000000) ≤ -Real.log (256 / 357) ∧
    -Real.log (256 / 357) ≤ (166279169 / 500000000) := by
  have h := checkLog_sound (w := (101 / 613)) (n := 12)
    (lo := (332558337 / 1000000000)) (hi := (166279169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357 / 256) = 1/(256 / 357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (332558337 / 1000000000) (166279169 / 500000000) (Real.log (357 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (357 / 256) = -Real.log (256 / 357) := by
    rw [show ((357 / 256) : ℝ) = ((256 / 357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (501752327 / 1000000000) ≤ -Real.log (155 / 256) ∧
    -Real.log (155 / 256) ≤ (62719041 / 125000000) := by
  have h := checkLog_sound (w := (101 / 411)) (n := 12)
    (lo := (501752327 / 1000000000)) (hi := (62719041 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 155) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 155) = 1/(155 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-62719041 / 125000000) (-501752327 / 1000000000) (Real.log (155 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331717647 / 1000000000) ≤ -Real.log (2560 / 3567) ∧
    -Real.log (2560 / 3567) ≤ (20732353 / 62500000) := by
  have h := checkLog_sound (w := (1007 / 6127)) (n := 12)
    (lo := (331717647 / 1000000000)) (hi := (20732353 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3567 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3567 / 2560) = 1/(2560 / 3567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331717647 / 1000000000) (20732353 / 62500000) (Real.log (3567 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3567 / 2560) = -Real.log (2560 / 3567) := by
    rw [show ((3567 / 2560) : ℝ) = ((2560 / 3567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (249909357 / 500000000) ≤ -Real.log (1553 / 2560) ∧
    -Real.log (1553 / 2560) ≤ (99963743 / 200000000) := by
  have h := checkLog_sound (w := (1007 / 4113)) (n := 12)
    (lo := (249909357 / 500000000)) (hi := (99963743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1553) = 1/(1553 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-99963743 / 200000000) (-249909357 / 500000000) (Real.log (1553 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (581691739 / 1000000000) ≤ -Real.log (128 / 229) ∧
    -Real.log (128 / 229) ≤ (29084587 / 50000000) := by
  have h := checkLog_sound (w := (101 / 357)) (n := 12)
    (lo := (581691739 / 1000000000)) (hi := (29084587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229 / 128) = 1/(128 / 229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (581691739 / 1000000000) (29084587 / 50000000) (Real.log (229 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (229 / 128) = -Real.log (128 / 229) := by
    rw [show ((229 / 128) : ℝ) = ((128 / 229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (389048349 / 250000000) ≤ -Real.log (27 / 128) ∧
    -Real.log (27 / 128) ≤ (1556193399 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 27) = 1/(27 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1556193399 / 1000000000) (-389048349 / 250000000) (Real.log (27 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (580380837 / 1000000000) ≤ -Real.log (1280 / 2287) ∧
    -Real.log (1280 / 2287) ≤ (290190419 / 500000000) := by
  have h := checkLog_sound (w := (1007 / 3567)) (n := 12)
    (lo := (580380837 / 1000000000)) (hi := (290190419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2287 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2287 / 1280) = 1/(1280 / 2287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (580380837 / 1000000000) (290190419 / 500000000) (Real.log (2287 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2287 / 1280) = -Real.log (1280 / 2287) := by
    rw [show ((2287 / 1280) : ℝ) = ((1280 / 2287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (38628589 / 25000000) ≤ -Real.log (273 / 1280) ∧
    -Real.log (273 / 1280) ≤ (1545143563 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 593)) (n := 12)
    (lo := (397123 / 2500000)) (hi := (158849201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 273) = 1/(273 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1545143563 / 1000000000) (-38628589 / 25000000) (Real.log (273 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45518373 / 100000000) ≤ -Real.log (1000000 / 1576463) ∧
    -Real.log (1000000 / 1576463) ≤ (455183731 / 1000000000) := by
  have h := checkLog_sound (w := (576463 / 2576463)) (n := 12)
    (lo := (45518373 / 100000000)) (hi := (455183731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1576463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1576463 / 1000000) = 1/(1000000 / 1576463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45518373 / 100000000) (455183731 / 1000000000) (Real.log (1576463 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1576463 / 1000000) = -Real.log (1000000 / 1576463) := by
    rw [show ((1576463 / 1000000) : ℝ) = ((1000000 / 1576463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1073893 / 1250000) ≤ -Real.log (423537 / 1000000) ∧
    -Real.log (423537 / 1000000) ≤ (429557201 / 500000000) := by
  have h := checkLog_sound (w := (76463 / 923537)) (n := 12)
    (lo := (8298361 / 50000000)) (hi := (165967221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423537) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 423537) = 1/(423537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-429557201 / 500000000) (-1073893 / 1250000) (Real.log (423537 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1140969 / 2500000) ≤ -Real.log (500000 / 789181) ∧
    -Real.log (500000 / 789181) ≤ (456387601 / 1000000000) := by
  have h := checkLog_sound (w := (289181 / 1289181)) (n := 12)
    (lo := (1140969 / 2500000)) (hi := (456387601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789181 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789181 / 500000) = 1/(500000 / 789181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1140969 / 2500000) (456387601 / 1000000000) (Real.log (789181 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (789181 / 500000) = -Real.log (500000 / 789181) := by
    rw [show ((789181 / 500000) : ℝ) = ((500000 / 789181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (107951019 / 125000000) ≤ -Real.log (210819 / 500000) ∧
    -Real.log (210819 / 500000) ≤ (431804077 / 500000000) := by
  have h := checkLog_sound (w := (39181 / 460819)) (n := 12)
    (lo := (42615243 / 250000000)) (hi := (170460973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 210819) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 210819) = 1/(210819 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-431804077 / 500000000) (-107951019 / 125000000) (Real.log (210819 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (370616901 / 1000000000) ≤ -Real.log (250000 / 362157) ∧
    -Real.log (250000 / 362157) ≤ (185308451 / 500000000) := by
  have h := checkLog_sound (w := (112157 / 612157)) (n := 12)
    (lo := (370616901 / 1000000000)) (hi := (185308451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362157 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362157 / 250000) = 1/(250000 / 362157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (370616901 / 1000000000) (185308451 / 500000000) (Real.log (362157 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (362157 / 250000) = -Real.log (250000 / 362157) := by
    rw [show ((362157 / 250000) : ℝ) = ((250000 / 362157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (595345561 / 1000000000) ≤ -Real.log (137843 / 250000) ∧
    -Real.log (137843 / 250000) ≤ (297672781 / 500000000) := by
  have h := checkLog_sound (w := (112157 / 387843)) (n := 12)
    (lo := (595345561 / 1000000000)) (hi := (297672781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 137843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 137843) = 1/(137843 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-297672781 / 500000000) (-595345561 / 1000000000) (Real.log (137843 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (18591969 / 50000000) ≤ -Real.log (1250 / 1813) ∧
    -Real.log (1250 / 1813) ≤ (371839381 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 3063)) (n := 12)
    (lo := (18591969 / 50000000)) (hi := (371839381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813 / 1250) = 1/(1250 / 1813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18591969 / 50000000) (371839381 / 1000000000) (Real.log (1813 / 1250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1813 / 1250) = -Real.log (1250 / 1813) := by
    rw [show ((1813 / 1250) : ℝ) = ((1250 / 1813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (299282269 / 500000000) ≤ -Real.log (687 / 1250) ∧
    -Real.log (687 / 1250) ≤ (598564539 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 1937)) (n := 12)
    (lo := (299282269 / 500000000)) (hi := (598564539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 687) = 1/(687 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-598564539 / 1000000000) (-299282269 / 500000000) (Real.log (687 / 1250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (131429813 / 100000000) ≤ -Real.log (125000000000 / 465267202157) ∧
    -Real.log (125000000000 / 465267202157) ≤ (328574533 / 250000000) := by
  have h := checkLog_sound (w := (215267202157 / 715267202157)) (n := 12)
    (lo := (12423019 / 20000000)) (hi := (621150951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465267202157 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(465267202157 / 250000000000) = 1/(125000000000 / 465267202157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (131429813 / 100000000) (328574533 / 250000000) (Real.log (465267202157 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (465267202157 / 125000000000) = -Real.log (125000000000 / 465267202157) := by
    rw [show ((465267202157 / 125000000000) : ℝ) = ((125000000000 / 465267202157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (164999469 / 125000000) ≤ -Real.log (250000000000 / 935851370133) ∧
    -Real.log (250000000000 / 935851370133) ≤ (659997877 / 500000000) := by
  have h := checkLog_sound (w := (435851370133 / 1435851370133)) (n := 12)
    (lo := (156712143 / 250000000)) (hi := (626848573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935851370133 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(935851370133 / 500000000000) = 1/(250000000000 / 935851370133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (164999469 / 125000000) (659997877 / 500000000) (Real.log (935851370133 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (935851370133 / 250000000000) = -Real.log (250000000000 / 935851370133) := by
    rw [show ((935851370133 / 250000000000) : ℝ) = ((250000000000 / 935851370133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (482981231 / 500000000) ≤ -Real.log (250000000000 / 656828783471) ∧
    -Real.log (250000000000 / 656828783471) ≤ (30186327 / 31250000) := by
  have h := checkLog_sound (w := (156828783471 / 1156828783471)) (n := 12)
    (lo := (136407641 / 500000000)) (hi := (272815283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656828783471 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(656828783471 / 500000000000) = 1/(250000000000 / 656828783471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (482981231 / 500000000) (30186327 / 31250000) (Real.log (656828783471 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (656828783471 / 250000000000) = -Real.log (250000000000 / 656828783471) := by
    rw [show ((656828783471 / 250000000000) : ℝ) = ((250000000000 / 656828783471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (970403917 / 1000000000) ≤ -Real.log (100000000000 / 263901018923) ∧
    -Real.log (100000000000 / 263901018923) ≤ (970403919 / 1000000000) := by
  have h := checkLog_sound (w := (63901018923 / 463901018923)) (n := 12)
    (lo := (277256737 / 1000000000)) (hi := (138628369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263901018923 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(263901018923 / 200000000000) = 1/(100000000000 / 263901018923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (970403917 / 1000000000) (970403919 / 1000000000) (Real.log (263901018923 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (263901018923 / 100000000000) = -Real.log (100000000000 / 263901018923) := by
    rw [show ((263901018923 / 100000000000) : ℝ) = ((100000000000 / 263901018923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0101

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0102Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0102
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

theorem reflection_log_1_neg : (331717647 / 1000000000) ≤ -Real.log (2560 / 3567) ∧
    -Real.log (2560 / 3567) ≤ (20732353 / 62500000) := by
  have h := checkLog_sound (w := (1007 / 6127)) (n := 12)
    (lo := (331717647 / 1000000000)) (hi := (20732353 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3567 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3567 / 2560) = 1/(2560 / 3567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331717647 / 1000000000) (20732353 / 62500000) (Real.log (3567 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3567 / 2560) = -Real.log (2560 / 3567) := by
    rw [show ((3567 / 2560) : ℝ) = ((2560 / 3567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (249909357 / 500000000) ≤ -Real.log (1553 / 2560) ∧
    -Real.log (1553 / 2560) ≤ (99963743 / 200000000) := by
  have h := checkLog_sound (w := (1007 / 4113)) (n := 12)
    (lo := (249909357 / 500000000)) (hi := (99963743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1553) = 1/(1553 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-99963743 / 200000000) (-249909357 / 500000000) (Real.log (1553 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (330876251 / 1000000000) ≤ -Real.log (640 / 891) ∧
    -Real.log (640 / 891) ≤ (82719063 / 250000000) := by
  have h := checkLog_sound (w := (251 / 1531)) (n := 12)
    (lo := (330876251 / 1000000000)) (hi := (82719063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891 / 640) = 1/(640 / 891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (330876251 / 1000000000) (82719063 / 250000000) (Real.log (891 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (891 / 640) = -Real.log (640 / 891) := by
    rw [show ((891 / 640) : ℝ) = ((640 / 891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (7779513 / 15625000) ≤ -Real.log (389 / 640) ∧
    -Real.log (389 / 640) ≤ (497888833 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 1029)) (n := 12)
    (lo := (7779513 / 15625000)) (hi := (497888833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 389) = 1/(389 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-497888833 / 1000000000) (-7779513 / 15625000) (Real.log (389 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (580380837 / 1000000000) ≤ -Real.log (1280 / 2287) ∧
    -Real.log (1280 / 2287) ≤ (290190419 / 500000000) := by
  have h := checkLog_sound (w := (1007 / 3567)) (n := 12)
    (lo := (580380837 / 1000000000)) (hi := (290190419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2287 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2287 / 1280) = 1/(1280 / 2287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (580380837 / 1000000000) (290190419 / 500000000) (Real.log (2287 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2287 / 1280) = -Real.log (1280 / 2287) := by
    rw [show ((2287 / 1280) : ℝ) = ((1280 / 2287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (38628589 / 25000000) ≤ -Real.log (273 / 1280) ∧
    -Real.log (273 / 1280) ≤ (1545143563 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 593)) (n := 12)
    (lo := (397123 / 2500000)) (hi := (158849201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 273) = 1/(273 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1545143563 / 1000000000) (-38628589 / 25000000) (Real.log (273 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (579068213 / 1000000000) ≤ -Real.log (320 / 571) ∧
    -Real.log (320 / 571) ≤ (289534107 / 500000000) := by
  have h := checkLog_sound (w := (251 / 891)) (n := 12)
    (lo := (579068213 / 1000000000)) (hi := (289534107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571 / 320) = 1/(320 / 571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (579068213 / 1000000000) (289534107 / 500000000) (Real.log (571 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (571 / 320) = -Real.log (320 / 571) := by
    rw [show ((571 / 320) : ℝ) = ((320 / 571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (153421449 / 100000000) ≤ -Real.log (69 / 320) ∧
    -Real.log (69 / 320) ≤ (1534214493 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 69) = 1/(69 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1534214493 / 1000000000) (-153421449 / 100000000) (Real.log (69 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (28373849 / 62500000) ≤ -Real.log (1000000 / 1574569) ∧
    -Real.log (1000000 / 1574569) ≤ (90796317 / 200000000) := by
  have h := checkLog_sound (w := (574569 / 2574569)) (n := 12)
    (lo := (28373849 / 62500000)) (hi := (90796317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1574569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1574569 / 1000000) = 1/(1000000 / 1574569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (28373849 / 62500000) (90796317 / 200000000) (Real.log (1574569 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1574569 / 1000000) = -Real.log (1000000 / 1574569) := by
    rw [show ((1574569 / 1000000) : ℝ) = ((1000000 / 1574569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (170930501 / 200000000) ≤ -Real.log (425431 / 1000000) ∧
    -Real.log (425431 / 1000000) ≤ (854652507 / 1000000000) := by
  have h := checkLog_sound (w := (74569 / 925431)) (n := 12)
    (lo := (6460213 / 40000000)) (hi := (80752663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 425431) = 1/(425431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-854652507 / 1000000000) (-170930501 / 200000000) (Real.log (425431 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (113796091 / 250000000) ≤ -Real.log (62500 / 98529) ∧
    -Real.log (62500 / 98529) ≤ (91036873 / 200000000) := by
  have h := checkLog_sound (w := (36029 / 161029)) (n := 12)
    (lo := (113796091 / 250000000)) (hi := (91036873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98529 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98529 / 62500) = 1/(62500 / 98529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (113796091 / 250000000) (91036873 / 200000000) (Real.log (98529 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98529 / 62500) = -Real.log (62500 / 98529) := by
    rw [show ((98529 / 62500) : ℝ) = ((62500 / 98529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (429558381 / 500000000) ≤ -Real.log (26471 / 62500) ∧
    -Real.log (26471 / 62500) ≤ (214779191 / 250000000) := by
  have h := checkLog_sound (w := (4779 / 57721)) (n := 12)
    (lo := (82984791 / 500000000)) (hi := (165969583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26471) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 26471) = 1/(26471 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-214779191 / 250000000) (-429558381 / 500000000) (Real.log (26471 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (92349441 / 250000000) ≤ -Real.log (1000000 / 1446863) ∧
    -Real.log (1000000 / 1446863) ≤ (73879553 / 200000000) := by
  have h := checkLog_sound (w := (446863 / 2446863)) (n := 12)
    (lo := (92349441 / 250000000)) (hi := (73879553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1446863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1446863 / 1000000) = 1/(1000000 / 1446863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (92349441 / 250000000) (73879553 / 200000000) (Real.log (1446863 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1446863 / 1000000) = -Real.log (1000000 / 1446863) := by
    rw [show ((1446863 / 1000000) : ℝ) = ((1000000 / 1446863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9252337 / 15625000) ≤ -Real.log (553137 / 1000000) ∧
    -Real.log (553137 / 1000000) ≤ (592149569 / 1000000000) := by
  have h := checkLog_sound (w := (446863 / 1553137)) (n := 12)
    (lo := (9252337 / 15625000)) (hi := (592149569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 553137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 553137) = 1/(553137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-592149569 / 1000000000) (-9252337 / 15625000) (Real.log (553137 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (370617591 / 1000000000) ≤ -Real.log (1000000 / 1448629) ∧
    -Real.log (1000000 / 1448629) ≤ (46327199 / 125000000) := by
  have h := checkLog_sound (w := (448629 / 2448629)) (n := 12)
    (lo := (370617591 / 1000000000)) (hi := (46327199 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1448629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1448629 / 1000000) = 1/(1000000 / 1448629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (370617591 / 1000000000) (46327199 / 125000000) (Real.log (1448629 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1448629 / 1000000) = -Real.log (1000000 / 1448629) := by
    rw [show ((1448629 / 1000000) : ℝ) = ((1000000 / 1448629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4762779 / 8000000) ≤ -Real.log (551371 / 1000000) ∧
    -Real.log (551371 / 1000000) ≤ (37209211 / 62500000) := by
  have h := checkLog_sound (w := (448629 / 1551371)) (n := 12)
    (lo := (4762779 / 8000000)) (hi := (37209211 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 551371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 551371) = 1/(551371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-37209211 / 62500000) (-4762779 / 8000000) (Real.log (551371 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1308634089 / 1000000000) ≤ -Real.log (100000000000 / 370111486939) ∧
    -Real.log (100000000000 / 370111486939) ≤ (1308634091 / 1000000000) := by
  have h := checkLog_sound (w := (170111486939 / 570111486939)) (n := 12)
    (lo := (615486909 / 1000000000)) (hi := (61548691 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370111486939 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(370111486939 / 200000000000) = 1/(100000000000 / 370111486939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1308634089 / 1000000000) (1308634091 / 1000000000) (Real.log (370111486939 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (370111486939 / 100000000000) = -Real.log (100000000000 / 370111486939) := by
    rw [show ((370111486939 / 100000000000) : ℝ) = ((100000000000 / 370111486939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (657150563 / 500000000) ≤ -Real.log (62500000000 / 232634297911) ∧
    -Real.log (62500000000 / 232634297911) ≤ (164287641 / 125000000) := by
  have h := checkLog_sound (w := (107634297911 / 357634297911)) (n := 12)
    (lo := (310576973 / 500000000)) (hi := (621153947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232634297911 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(232634297911 / 125000000000) = 1/(62500000000 / 232634297911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (657150563 / 500000000) (164287641 / 125000000) (Real.log (232634297911 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (232634297911 / 62500000000) = -Real.log (62500000000 / 232634297911) := by
    rw [show ((232634297911 / 62500000000) : ℝ) = ((62500000000 / 232634297911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (240386833 / 250000000) ≤ -Real.log (20000000000 / 52314815317) ∧
    -Real.log (20000000000 / 52314815317) ≤ (480773667 / 500000000) := by
  have h := checkLog_sound (w := (12314815317 / 92314815317)) (n := 12)
    (lo := (33550019 / 125000000)) (hi := (268400153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52314815317 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(52314815317 / 40000000000) = 1/(20000000000 / 52314815317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (240386833 / 250000000) (480773667 / 500000000) (Real.log (52314815317 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (52314815317 / 20000000000) = -Real.log (20000000000 / 52314815317) := by
    rw [show ((52314815317 / 20000000000) : ℝ) = ((20000000000 / 52314815317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (482982483 / 500000000) ≤ -Real.log (250000000000 / 656830428151) ∧
    -Real.log (250000000000 / 656830428151) ≤ (120745621 / 125000000) := by
  have h := checkLog_sound (w := (156830428151 / 1156830428151)) (n := 12)
    (lo := (136408893 / 500000000)) (hi := (272817787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656830428151 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(656830428151 / 500000000000) = 1/(250000000000 / 656830428151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (482982483 / 500000000) (120745621 / 125000000) (Real.log (656830428151 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (656830428151 / 250000000000) = -Real.log (250000000000 / 656830428151) := by
    rw [show ((656830428151 / 250000000000) : ℝ) = ((250000000000 / 656830428151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0102

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0103Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0103
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

theorem reflection_log_1_neg : (330876251 / 1000000000) ≤ -Real.log (640 / 891) ∧
    -Real.log (640 / 891) ≤ (82719063 / 250000000) := by
  have h := checkLog_sound (w := (251 / 1531)) (n := 12)
    (lo := (330876251 / 1000000000)) (hi := (82719063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891 / 640) = 1/(640 / 891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (330876251 / 1000000000) (82719063 / 250000000) (Real.log (891 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (891 / 640) = -Real.log (640 / 891) := by
    rw [show ((891 / 640) : ℝ) = ((640 / 891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (7779513 / 15625000) ≤ -Real.log (389 / 640) ∧
    -Real.log (389 / 640) ≤ (497888833 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 1029)) (n := 12)
    (lo := (7779513 / 15625000)) (hi := (497888833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 389) = 1/(389 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-497888833 / 1000000000) (-7779513 / 15625000) (Real.log (389 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66006829 / 200000000) ≤ -Real.log (2560 / 3561) ∧
    -Real.log (2560 / 3561) ≤ (165017073 / 500000000) := by
  have h := checkLog_sound (w := (1001 / 6121)) (n := 12)
    (lo := (66006829 / 200000000)) (hi := (165017073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3561 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3561 / 2560) = 1/(2560 / 3561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66006829 / 200000000) (165017073 / 500000000) (Real.log (3561 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3561 / 2560) = -Real.log (2560 / 3561) := by
    rw [show ((3561 / 2560) : ℝ) = ((2560 / 3561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (123990667 / 250000000) ≤ -Real.log (1559 / 2560) ∧
    -Real.log (1559 / 2560) ≤ (495962669 / 1000000000) := by
  have h := checkLog_sound (w := (1001 / 4119)) (n := 12)
    (lo := (123990667 / 250000000)) (hi := (495962669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1559) = 1/(1559 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-495962669 / 1000000000) (-123990667 / 250000000) (Real.log (1559 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (579068213 / 1000000000) ≤ -Real.log (320 / 571) ∧
    -Real.log (320 / 571) ≤ (289534107 / 500000000) := by
  have h := checkLog_sound (w := (251 / 891)) (n := 12)
    (lo := (579068213 / 1000000000)) (hi := (289534107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571 / 320) = 1/(320 / 571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (579068213 / 1000000000) (289534107 / 500000000) (Real.log (571 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (571 / 320) = -Real.log (320 / 571) := by
    rw [show ((571 / 320) : ℝ) = ((320 / 571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (153421449 / 100000000) ≤ -Real.log (69 / 320) ∧
    -Real.log (69 / 320) ≤ (1534214493 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 69) = 1/(69 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1534214493 / 1000000000) (-153421449 / 100000000) (Real.log (69 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (115550773 / 200000000) ≤ -Real.log (1280 / 2281) ∧
    -Real.log (1280 / 2281) ≤ (288876933 / 500000000) := by
  have h := checkLog_sound (w := (1001 / 3561)) (n := 12)
    (lo := (115550773 / 200000000)) (hi := (288876933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2281 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2281 / 1280) = 1/(1280 / 2281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (115550773 / 200000000) (288876933 / 500000000) (Real.log (2281 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2281 / 1280) = -Real.log (1280 / 2281) := by
    rw [show ((2281 / 1280) : ℝ) = ((1280 / 2281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1523403573 / 1000000000) ≤ -Real.log (279 / 1280) ∧
    -Real.log (279 / 1280) ≤ (190425447 / 125000000) := by
  have h := checkLog_sound (w := (41 / 599)) (n := 12)
    (lo := (137109213 / 1000000000)) (hi := (68554607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 279) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 279) = 1/(279 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-190425447 / 125000000) (-1523403573 / 1000000000) (Real.log (279 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (226389949 / 500000000) ≤ -Real.log (500000 / 786339) ∧
    -Real.log (500000 / 786339) ≤ (452779899 / 1000000000) := by
  have h := checkLog_sound (w := (286339 / 1286339)) (n := 12)
    (lo := (226389949 / 500000000)) (hi := (452779899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786339 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786339 / 500000) = 1/(500000 / 786339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (226389949 / 500000000) (452779899 / 1000000000) (Real.log (786339 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (786339 / 500000) = -Real.log (500000 / 786339) := by
    rw [show ((786339 / 500000) : ℝ) = ((500000 / 786339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (850217451 / 1000000000) ≤ -Real.log (213661 / 500000) ∧
    -Real.log (213661 / 500000) ≤ (850217453 / 1000000000) := by
  have h := checkLog_sound (w := (36339 / 463661)) (n := 12)
    (lo := (157070271 / 1000000000)) (hi := (2454223 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213661) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 213661) = 1/(213661 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-850217453 / 1000000000) (-850217451 / 1000000000) (Real.log (213661 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (453982219 / 1000000000) ≤ -Real.log (100000 / 157457) ∧
    -Real.log (100000 / 157457) ≤ (22699111 / 50000000) := by
  have h := checkLog_sound (w := (57457 / 257457)) (n := 12)
    (lo := (453982219 / 1000000000)) (hi := (22699111 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157457 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157457 / 100000) = 1/(100000 / 157457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (453982219 / 1000000000) (22699111 / 50000000) (Real.log (157457 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (157457 / 100000) = -Real.log (100000 / 157457) := by
    rw [show ((157457 / 100000) : ℝ) = ((100000 / 157457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (106831857 / 125000000) ≤ -Real.log (42543 / 100000) ∧
    -Real.log (42543 / 100000) ≤ (427327429 / 500000000) := by
  have h := checkLog_sound (w := (7457 / 92543)) (n := 12)
    (lo := (40376919 / 250000000)) (hi := (161507677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42543) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 42543) = 1/(42543 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-427327429 / 500000000) (-106831857 / 125000000) (Real.log (42543 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (368181291 / 1000000000) ≤ -Real.log (62500 / 90319) ∧
    -Real.log (62500 / 90319) ≤ (92045323 / 250000000) := by
  have h := checkLog_sound (w := (27819 / 152819)) (n := 12)
    (lo := (368181291 / 1000000000)) (hi := (92045323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90319 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90319 / 62500) = 1/(62500 / 90319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (368181291 / 1000000000) (92045323 / 250000000) (Real.log (90319 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (90319 / 62500) = -Real.log (62500 / 90319) := by
    rw [show ((90319 / 62500) : ℝ) = ((62500 / 90319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (58897457 / 100000000) ≤ -Real.log (34681 / 62500) ∧
    -Real.log (34681 / 62500) ≤ (588974571 / 1000000000) := by
  have h := checkLog_sound (w := (27819 / 97181)) (n := 12)
    (lo := (58897457 / 100000000)) (hi := (588974571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 34681) = 1/(34681 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-588974571 / 1000000000) (-58897457 / 100000000) (Real.log (34681 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (73879691 / 200000000) ≤ -Real.log (62500 / 90429) ∧
    -Real.log (62500 / 90429) ≤ (46174807 / 125000000) := by
  have h := checkLog_sound (w := (27929 / 152929)) (n := 12)
    (lo := (73879691 / 200000000)) (hi := (46174807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90429 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90429 / 62500) = 1/(62500 / 90429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (73879691 / 200000000) (46174807 / 125000000) (Real.log (90429 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90429 / 62500) = -Real.log (62500 / 90429) := by
    rw [show ((90429 / 62500) : ℝ) = ((62500 / 90429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37009461 / 62500000) ≤ -Real.log (34571 / 62500) ∧
    -Real.log (34571 / 62500) ≤ (592151377 / 1000000000) := by
  have h := checkLog_sound (w := (27929 / 97071)) (n := 12)
    (lo := (37009461 / 62500000)) (hi := (592151377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 34571) = 1/(34571 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-592151377 / 1000000000) (-37009461 / 62500000) (Real.log (34571 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1302997349 / 1000000000) ≤ -Real.log (250000000000 / 920077833577) ∧
    -Real.log (250000000000 / 920077833577) ≤ (1302997351 / 1000000000) := by
  have h := checkLog_sound (w := (420077833577 / 1420077833577)) (n := 12)
    (lo := (609850169 / 1000000000)) (hi := (60985017 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((920077833577 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(920077833577 / 500000000000) = 1/(250000000000 / 920077833577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1302997349 / 1000000000) (1302997351 / 1000000000) (Real.log (920077833577 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (920077833577 / 250000000000) = -Real.log (250000000000 / 920077833577) := by
    rw [show ((920077833577 / 250000000000) : ℝ) = ((250000000000 / 920077833577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (52345483 / 40000000) ≤ -Real.log (500000000000 / 1850562959829) ∧
    -Real.log (500000000000 / 1850562959829) ≤ (1308637077 / 1000000000) := by
  have h := checkLog_sound (w := (850562959829 / 2850562959829)) (n := 12)
    (lo := (123097979 / 200000000)) (hi := (76936237 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1850562959829 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1850562959829 / 1000000000000) = 1/(500000000000 / 1850562959829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (52345483 / 40000000) (1308637077 / 1000000000) (Real.log (1850562959829 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1850562959829 / 500000000000) = -Real.log (500000000000 / 1850562959829) := by
    rw [show ((1850562959829 / 500000000000) : ℝ) = ((500000000000 / 1850562959829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (47857793 / 50000000) ≤ -Real.log (250000000000 / 651069750007) ∧
    -Real.log (250000000000 / 651069750007) ≤ (478577931 / 500000000) := by
  have h := checkLog_sound (w := (151069750007 / 1151069750007)) (n := 12)
    (lo := (6600217 / 25000000)) (hi := (264008681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651069750007 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(651069750007 / 500000000000) = 1/(250000000000 / 651069750007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (47857793 / 50000000) (478577931 / 500000000) (Real.log (651069750007 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (651069750007 / 250000000000) = -Real.log (250000000000 / 651069750007) := by
    rw [show ((651069750007 / 250000000000) : ℝ) = ((250000000000 / 651069750007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (961549831 / 1000000000) ≤ -Real.log (500000000000 / 1307873651327) ∧
    -Real.log (500000000000 / 1307873651327) ≤ (961549833 / 1000000000) := by
  have h := checkLog_sound (w := (307873651327 / 2307873651327)) (n := 12)
    (lo := (268402651 / 1000000000)) (hi := (67100663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307873651327 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1307873651327 / 1000000000000) = 1/(500000000000 / 1307873651327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (961549831 / 1000000000) (961549833 / 1000000000) (Real.log (1307873651327 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1307873651327 / 500000000000) = -Real.log (500000000000 / 1307873651327) := by
    rw [show ((1307873651327 / 500000000000) : ℝ) = ((500000000000 / 1307873651327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0103

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0104Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0104
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

theorem reflection_log_1_neg : (66006829 / 200000000) ≤ -Real.log (2560 / 3561) ∧
    -Real.log (2560 / 3561) ≤ (165017073 / 500000000) := by
  have h := checkLog_sound (w := (1001 / 6121)) (n := 12)
    (lo := (66006829 / 200000000)) (hi := (165017073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3561 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3561 / 2560) = 1/(2560 / 3561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66006829 / 200000000) (165017073 / 500000000) (Real.log (3561 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3561 / 2560) = -Real.log (2560 / 3561) := by
    rw [show ((3561 / 2560) : ℝ) = ((2560 / 3561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (123990667 / 250000000) ≤ -Real.log (1559 / 2560) ∧
    -Real.log (1559 / 2560) ≤ (495962669 / 1000000000) := by
  have h := checkLog_sound (w := (1001 / 4119)) (n := 12)
    (lo := (123990667 / 250000000)) (hi := (495962669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1559) = 1/(1559 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-495962669 / 1000000000) (-123990667 / 250000000) (Real.log (1559 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (32919133 / 100000000) ≤ -Real.log (1280 / 1779) ∧
    -Real.log (1280 / 1779) ≤ (329191331 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 3059)) (n := 12)
    (lo := (32919133 / 100000000)) (hi := (329191331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1779 / 1280) = 1/(1280 / 1779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (32919133 / 100000000) (329191331 / 1000000000) (Real.log (1779 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1779 / 1280) = -Real.log (1280 / 1779) := by
    rw [show ((1779 / 1280) : ℝ) = ((1280 / 1779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (494040207 / 1000000000) ≤ -Real.log (781 / 1280) ∧
    -Real.log (781 / 1280) ≤ (30877513 / 62500000) := by
  have h := checkLog_sound (w := (499 / 2061)) (n := 12)
    (lo := (494040207 / 1000000000)) (hi := (30877513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 781) = 1/(781 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30877513 / 62500000) (-494040207 / 1000000000) (Real.log (781 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (115550773 / 200000000) ≤ -Real.log (1280 / 2281) ∧
    -Real.log (1280 / 2281) ≤ (288876933 / 500000000) := by
  have h := checkLog_sound (w := (1001 / 3561)) (n := 12)
    (lo := (115550773 / 200000000)) (hi := (288876933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2281 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2281 / 1280) = 1/(1280 / 2281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (115550773 / 200000000) (288876933 / 500000000) (Real.log (2281 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2281 / 1280) = -Real.log (1280 / 2281) := by
    rw [show ((2281 / 1280) : ℝ) = ((1280 / 2281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1523403573 / 1000000000) ≤ -Real.log (279 / 1280) ∧
    -Real.log (279 / 1280) ≤ (190425447 / 125000000) := by
  have h := checkLog_sound (w := (41 / 599)) (n := 12)
    (lo := (137109213 / 1000000000)) (hi := (68554607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 279) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 279) = 1/(279 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-190425447 / 125000000) (-1523403573 / 1000000000) (Real.log (279 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (576437787 / 1000000000) ≤ -Real.log (640 / 1139) ∧
    -Real.log (640 / 1139) ≤ (144109447 / 250000000) := by
  have h := checkLog_sound (w := (499 / 1779)) (n := 12)
    (lo := (576437787 / 1000000000)) (hi := (144109447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1139 / 640) = 1/(640 / 1139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (576437787 / 1000000000) (144109447 / 250000000) (Real.log (1139 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1139 / 640) = -Real.log (640 / 1139) := by
    rw [show ((1139 / 640) : ℝ) = ((640 / 1139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (378177071 / 250000000) ≤ -Real.log (141 / 640) ∧
    -Real.log (141 / 640) ≤ (1512708287 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 141) = 1/(141 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1512708287 / 1000000000) (-378177071 / 250000000) (Real.log (141 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (11289451 / 25000000) ≤ -Real.log (1000000 / 1570789) ∧
    -Real.log (1000000 / 1570789) ≤ (451578041 / 1000000000) := by
  have h := checkLog_sound (w := (570789 / 2570789)) (n := 12)
    (lo := (11289451 / 25000000)) (hi := (451578041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1570789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1570789 / 1000000) = 1/(1000000 / 1570789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (11289451 / 25000000) (451578041 / 1000000000) (Real.log (1570789 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1570789 / 1000000) = -Real.log (1000000 / 1570789) := by
    rw [show ((1570789 / 1000000) : ℝ) = ((1000000 / 1570789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (422903319 / 500000000) ≤ -Real.log (429211 / 1000000) ∧
    -Real.log (429211 / 1000000) ≤ (10572583 / 12500000) := by
  have h := checkLog_sound (w := (70789 / 929211)) (n := 12)
    (lo := (76329729 / 500000000)) (hi := (152659459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429211) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 429211) = 1/(429211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10572583 / 12500000) (-422903319 / 500000000) (Real.log (429211 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (226390267 / 500000000) ≤ -Real.log (1000000 / 1572679) ∧
    -Real.log (1000000 / 1572679) ≤ (90556107 / 200000000) := by
  have h := checkLog_sound (w := (572679 / 2572679)) (n := 12)
    (lo := (226390267 / 500000000)) (hi := (90556107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1572679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1572679 / 1000000) = 1/(1000000 / 1572679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (226390267 / 500000000) (90556107 / 200000000) (Real.log (1572679 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1572679 / 1000000) = -Real.log (1000000 / 1572679) := by
    rw [show ((1572679 / 1000000) : ℝ) = ((1000000 / 1572679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (850219791 / 1000000000) ≤ -Real.log (427321 / 1000000) ∧
    -Real.log (427321 / 1000000) ≤ (850219793 / 1000000000) := by
  have h := checkLog_sound (w := (72679 / 927321)) (n := 12)
    (lo := (157072611 / 1000000000)) (hi := (39268153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 427321) = 1/(427321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-850219793 / 1000000000) (-850219791 / 1000000000) (Real.log (427321 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (917417 / 2500000) ≤ -Real.log (20000 / 28867) ∧
    -Real.log (20000 / 28867) ≤ (366966801 / 1000000000) := by
  have h := checkLog_sound (w := (8867 / 48867)) (n := 12)
    (lo := (917417 / 2500000)) (hi := (366966801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28867 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28867 / 20000) = 1/(20000 / 28867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (917417 / 2500000) (366966801 / 1000000000) (Real.log (28867 / 20000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (28867 / 20000) = -Real.log (20000 / 28867) := by
    rw [show ((28867 / 20000) : ℝ) = ((20000 / 28867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (292909301 / 500000000) ≤ -Real.log (11133 / 20000) ∧
    -Real.log (11133 / 20000) ≤ (585818603 / 1000000000) := by
  have h := checkLog_sound (w := (8867 / 31133)) (n := 12)
    (lo := (292909301 / 500000000)) (hi := (585818603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 11133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 11133) = 1/(11133 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-585818603 / 1000000000) (-292909301 / 500000000) (Real.log (11133 / 20000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (368181983 / 1000000000) ≤ -Real.log (200000 / 289021) ∧
    -Real.log (200000 / 289021) ≤ (11505687 / 31250000) := by
  have h := checkLog_sound (w := (89021 / 489021)) (n := 12)
    (lo := (368181983 / 1000000000)) (hi := (11505687 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289021 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289021 / 200000) = 1/(200000 / 289021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (368181983 / 1000000000) (11505687 / 31250000) (Real.log (289021 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (289021 / 200000) = -Real.log (200000 / 289021) := by
    rw [show ((289021 / 200000) : ℝ) = ((200000 / 289021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (147244093 / 250000000) ≤ -Real.log (110979 / 200000) ∧
    -Real.log (110979 / 200000) ≤ (588976373 / 1000000000) := by
  have h := checkLog_sound (w := (89021 / 310979)) (n := 12)
    (lo := (147244093 / 250000000)) (hi := (588976373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 110979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 110979) = 1/(110979 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-588976373 / 1000000000) (-147244093 / 250000000) (Real.log (110979 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1297384679 / 1000000000) ≤ -Real.log (500000000000 / 1829856410949) ∧
    -Real.log (500000000000 / 1829856410949) ≤ (1297384681 / 1000000000) := by
  have h := checkLog_sound (w := (829856410949 / 2829856410949)) (n := 12)
    (lo := (604237499 / 1000000000)) (hi := (48339 / 80000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1829856410949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1829856410949 / 1000000000000) = 1/(500000000000 / 1829856410949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1297384679 / 1000000000) (1297384681 / 1000000000) (Real.log (1829856410949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1829856410949 / 500000000000) = -Real.log (500000000000 / 1829856410949) := by
    rw [show ((1829856410949 / 500000000000) : ℝ) = ((500000000000 / 1829856410949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (52120013 / 40000000) ≤ -Real.log (500000000000 / 1840161143497) ∧
    -Real.log (500000000000 / 1840161143497) ≤ (1303000327 / 1000000000) := by
  have h := checkLog_sound (w := (840161143497 / 2840161143497)) (n := 12)
    (lo := (121970629 / 200000000)) (hi := (304926573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1840161143497 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1840161143497 / 1000000000000) = 1/(500000000000 / 1840161143497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (52120013 / 40000000) (1303000327 / 1000000000) (Real.log (1840161143497 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1840161143497 / 500000000000) = -Real.log (500000000000 / 1840161143497) := by
    rw [show ((1840161143497 / 500000000000) : ℝ) = ((500000000000 / 1840161143497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (476392701 / 500000000) ≤ -Real.log (100000000000 / 259292194377) ∧
    -Real.log (100000000000 / 259292194377) ≤ (238196351 / 250000000) := by
  have h := checkLog_sound (w := (59292194377 / 459292194377)) (n := 12)
    (lo := (129819111 / 500000000)) (hi := (259638223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259292194377 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259292194377 / 200000000000) = 1/(100000000000 / 259292194377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (476392701 / 500000000) (238196351 / 250000000) (Real.log (259292194377 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (259292194377 / 100000000000) = -Real.log (100000000000 / 259292194377) := by
    rw [show ((259292194377 / 100000000000) : ℝ) = ((100000000000 / 259292194377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (191431671 / 200000000) ≤ -Real.log (31250000000 / 81383921733) ∧
    -Real.log (31250000000 / 81383921733) ≤ (957158357 / 1000000000) := by
  have h := checkLog_sound (w := (18883921733 / 143883921733)) (n := 12)
    (lo := (10560447 / 40000000)) (hi := (33001397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81383921733 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(81383921733 / 62500000000) = 1/(31250000000 / 81383921733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (191431671 / 200000000) (957158357 / 1000000000) (Real.log (81383921733 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (81383921733 / 31250000000) = -Real.log (31250000000 / 81383921733) := by
    rw [show ((81383921733 / 31250000000) : ℝ) = ((31250000000 / 81383921733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0104

end


