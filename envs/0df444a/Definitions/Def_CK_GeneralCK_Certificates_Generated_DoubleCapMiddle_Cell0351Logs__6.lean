-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0351Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0351Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:15:03.734147+00:00
-- url     : https://prove2.me/theorems/4b10d3d8-5e36-4581-8cc5-874989913f52
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0351Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0352Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0351Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0352Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0353Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0354Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0355Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0356Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0351Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0352Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0353Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0354Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0355Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0356Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0351Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0352Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0353Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0354Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0355Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0356Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0351Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0352Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0353Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0354Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0355Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0356Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0351Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0351
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

theorem reflection_log_1_neg : (105954401 / 500000000) ≤ -Real.log (10240 / 12657) ∧
    -Real.log (10240 / 12657) ≤ (211908803 / 1000000000) := by
  have h := checkLog_sound (w := (2417 / 22897)) (n := 12)
    (lo := (105954401 / 500000000)) (hi := (211908803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12657 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12657 / 10240) = 1/(10240 / 12657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (105954401 / 500000000) (211908803 / 1000000000) (Real.log (12657 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12657 / 10240) = -Real.log (10240 / 12657) := by
    rw [show ((12657 / 10240) : ℝ) = ((10240 / 12657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (134616753 / 500000000) ≤ -Real.log (7823 / 10240) ∧
    -Real.log (7823 / 10240) ≤ (269233507 / 1000000000) := by
  have h := checkLog_sound (w := (2417 / 18063)) (n := 12)
    (lo := (134616753 / 500000000)) (hi := (269233507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7823) = 1/(7823 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-269233507 / 1000000000) (-134616753 / 500000000) (Real.log (7823 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (211671751 / 1000000000) ≤ -Real.log (5120 / 6327) ∧
    -Real.log (5120 / 6327) ≤ (26458969 / 125000000) := by
  have h := checkLog_sound (w := (1207 / 11447)) (n := 12)
    (lo := (211671751 / 1000000000)) (hi := (26458969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6327 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6327 / 5120) = 1/(5120 / 6327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (211671751 / 1000000000) (26458969 / 125000000) (Real.log (6327 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6327 / 5120) = -Real.log (5120 / 6327) := by
    rw [show ((6327 / 5120) : ℝ) = ((5120 / 6327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (53770019 / 200000000) ≤ -Real.log (3913 / 5120) ∧
    -Real.log (3913 / 5120) ≤ (16803131 / 62500000) := by
  have h := checkLog_sound (w := (1207 / 9033)) (n := 12)
    (lo := (53770019 / 200000000)) (hi := (16803131 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3913) = 1/(3913 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16803131 / 62500000) (-53770019 / 200000000) (Real.log (3913 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77333957 / 200000000) ≤ -Real.log (5120 / 7537) ∧
    -Real.log (5120 / 7537) ≤ (193334893 / 500000000) := by
  have h := checkLog_sound (w := (2417 / 12657)) (n := 12)
    (lo := (77333957 / 200000000)) (hi := (193334893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7537 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7537 / 5120) = 1/(5120 / 7537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77333957 / 200000000) (193334893 / 500000000) (Real.log (7537 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7537 / 5120) = -Real.log (5120 / 7537) := by
    rw [show ((7537 / 5120) : ℝ) = ((5120 / 7537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (638792171 / 1000000000) ≤ -Real.log (2703 / 5120) ∧
    -Real.log (2703 / 5120) ≤ (159698043 / 250000000) := by
  have h := checkLog_sound (w := (2417 / 7823)) (n := 12)
    (lo := (638792171 / 1000000000)) (hi := (159698043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2703) = 1/(2703 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159698043 / 250000000) (-638792171 / 1000000000) (Real.log (2703 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (38627167 / 100000000) ≤ -Real.log (2560 / 3767) ∧
    -Real.log (2560 / 3767) ≤ (386271671 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 6327)) (n := 12)
    (lo := (38627167 / 100000000)) (hi := (386271671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3767 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3767 / 2560) = 1/(2560 / 3767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (38627167 / 100000000) (386271671 / 1000000000) (Real.log (3767 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3767 / 2560) = -Real.log (2560 / 3767) := by
    rw [show ((3767 / 2560) : ℝ) = ((2560 / 3767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (637682909 / 1000000000) ≤ -Real.log (1353 / 2560) ∧
    -Real.log (1353 / 2560) ≤ (63768291 / 100000000) := by
  have h := checkLog_sound (w := (1207 / 3913)) (n := 12)
    (lo := (637682909 / 1000000000)) (hi := (63768291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1353) = 1/(1353 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63768291 / 100000000) (-637682909 / 1000000000) (Real.log (1353 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (145139723 / 500000000) ≤ -Real.log (1000000 / 1336801) ∧
    -Real.log (1000000 / 1336801) ≤ (290279447 / 1000000000) := by
  have h := checkLog_sound (w := (336801 / 2336801)) (n := 12)
    (lo := (145139723 / 500000000)) (hi := (290279447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1336801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1336801 / 1000000) = 1/(1000000 / 1336801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (145139723 / 500000000) (290279447 / 1000000000) (Real.log (1336801 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1336801 / 1000000) = -Real.log (1000000 / 1336801) := by
    rw [show ((1336801 / 1000000) : ℝ) = ((1000000 / 1336801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (410680183 / 1000000000) ≤ -Real.log (663199 / 1000000) ∧
    -Real.log (663199 / 1000000) ≤ (51335023 / 125000000) := by
  have h := checkLog_sound (w := (336801 / 1663199)) (n := 12)
    (lo := (410680183 / 1000000000)) (hi := (51335023 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 663199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 663199) = 1/(663199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-51335023 / 125000000) (-410680183 / 1000000000) (Real.log (663199 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (29060031 / 100000000) ≤ -Real.log (100000 / 133723) ∧
    -Real.log (100000 / 133723) ≤ (290600311 / 1000000000) := by
  have h := checkLog_sound (w := (33723 / 233723)) (n := 12)
    (lo := (29060031 / 100000000)) (hi := (290600311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133723 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133723 / 100000) = 1/(100000 / 133723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (29060031 / 100000000) (290600311 / 1000000000) (Real.log (133723 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (133723 / 100000) = -Real.log (100000 / 133723) := by
    rw [show ((133723 / 100000) : ℝ) = ((100000 / 133723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (51415907 / 125000000) ≤ -Real.log (66277 / 100000) ∧
    -Real.log (66277 / 100000) ≤ (411327257 / 1000000000) := by
  have h := checkLog_sound (w := (33723 / 166277)) (n := 12)
    (lo := (51415907 / 125000000)) (hi := (411327257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66277) = 1/(66277 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-411327257 / 1000000000) (-51415907 / 125000000) (Real.log (66277 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (219836489 / 1000000000) ≤ -Real.log (1000000 / 1245873) ∧
    -Real.log (1000000 / 1245873) ≤ (21983649 / 100000000) := by
  have h := checkLog_sound (w := (245873 / 2245873)) (n := 12)
    (lo := (219836489 / 1000000000)) (hi := (21983649 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245873 / 1000000) = 1/(1000000 / 1245873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (219836489 / 1000000000) (21983649 / 100000000) (Real.log (1245873 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1245873 / 1000000) = -Real.log (1000000 / 1245873) := by
    rw [show ((1245873 / 1000000) : ℝ) = ((1000000 / 1245873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (28219449 / 100000000) ≤ -Real.log (754127 / 1000000) ∧
    -Real.log (754127 / 1000000) ≤ (282194491 / 1000000000) := by
  have h := checkLog_sound (w := (245873 / 1754127)) (n := 12)
    (lo := (28219449 / 100000000)) (hi := (282194491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754127) = 1/(754127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-282194491 / 1000000000) (-28219449 / 100000000) (Real.log (754127 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (110052269 / 500000000) ≤ -Real.log (1000000 / 1246207) ∧
    -Real.log (1000000 / 1246207) ≤ (220104539 / 1000000000) := by
  have h := checkLog_sound (w := (246207 / 2246207)) (n := 12)
    (lo := (110052269 / 500000000)) (hi := (220104539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246207 / 1000000) = 1/(1000000 / 1246207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (110052269 / 500000000) (220104539 / 1000000000) (Real.log (1246207 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1246207 / 1000000) = -Real.log (1000000 / 1246207) := by
    rw [show ((1246207 / 1000000) : ℝ) = ((1000000 / 1246207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (70659371 / 250000000) ≤ -Real.log (753793 / 1000000) ∧
    -Real.log (753793 / 1000000) ≤ (56527497 / 200000000) := by
  have h := checkLog_sound (w := (246207 / 1753793)) (n := 12)
    (lo := (70659371 / 250000000)) (hi := (56527497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753793) = 1/(753793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-56527497 / 200000000) (-70659371 / 250000000) (Real.log (753793 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (175239907 / 250000000) ≤ -Real.log (500000000000 / 1007843045601) ∧
    -Real.log (500000000000 / 1007843045601) ≤ (70095963 / 100000000) := by
  have h := checkLog_sound (w := (7843045601 / 2007843045601)) (n := 12)
    (lo := (244139 / 31250000)) (hi := (7812449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1007843045601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1007843045601 / 1000000000000) = 1/(500000000000 / 1007843045601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (175239907 / 250000000) (70095963 / 100000000) (Real.log (1007843045601 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1007843045601 / 500000000000) = -Real.log (500000000000 / 1007843045601) := by
    rw [show ((1007843045601 / 500000000000) : ℝ) = ((500000000000 / 1007843045601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (350963783 / 500000000) ≤ -Real.log (125000000000 / 252204761833) ∧
    -Real.log (125000000000 / 252204761833) ≤ (43870473 / 62500000) := by
  have h := checkLog_sound (w := (2204761833 / 502204761833)) (n := 12)
    (lo := (4390193 / 500000000)) (hi := (8780387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252204761833 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(252204761833 / 250000000000) = 1/(125000000000 / 252204761833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (350963783 / 500000000) (43870473 / 62500000) (Real.log (252204761833 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (252204761833 / 125000000000) = -Real.log (125000000000 / 252204761833) := by
    rw [show ((252204761833 / 125000000000) : ℝ) = ((125000000000 / 252204761833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (502030979 / 1000000000) ≤ -Real.log (500000000000 / 826036595957) ∧
    -Real.log (500000000000 / 826036595957) ≤ (25101549 / 50000000) := by
  have h := checkLog_sound (w := (326036595957 / 1326036595957)) (n := 12)
    (lo := (502030979 / 1000000000)) (hi := (25101549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826036595957 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826036595957 / 500000000000) = 1/(500000000000 / 826036595957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (502030979 / 1000000000) (25101549 / 50000000) (Real.log (826036595957 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (826036595957 / 500000000000) = -Real.log (500000000000 / 826036595957) := by
    rw [show ((826036595957 / 500000000000) : ℝ) = ((500000000000 / 826036595957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (251371011 / 500000000) ≤ -Real.log (100000000000 / 165324830557) ∧
    -Real.log (100000000000 / 165324830557) ≤ (502742023 / 1000000000) := by
  have h := checkLog_sound (w := (65324830557 / 265324830557)) (n := 12)
    (lo := (251371011 / 500000000)) (hi := (502742023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165324830557 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165324830557 / 100000000000) = 1/(100000000000 / 165324830557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (251371011 / 500000000) (502742023 / 1000000000) (Real.log (165324830557 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (165324830557 / 100000000000) = -Real.log (100000000000 / 165324830557) := by
    rw [show ((165324830557 / 100000000000) : ℝ) = ((100000000000 / 165324830557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0351

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0352Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0352
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

theorem reflection_log_1_neg : (211671751 / 1000000000) ≤ -Real.log (5120 / 6327) ∧
    -Real.log (5120 / 6327) ≤ (26458969 / 125000000) := by
  have h := checkLog_sound (w := (1207 / 11447)) (n := 12)
    (lo := (211671751 / 1000000000)) (hi := (26458969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6327 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6327 / 5120) = 1/(5120 / 6327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (211671751 / 1000000000) (26458969 / 125000000) (Real.log (6327 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6327 / 5120) = -Real.log (5120 / 6327) := by
    rw [show ((6327 / 5120) : ℝ) = ((5120 / 6327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (53770019 / 200000000) ≤ -Real.log (3913 / 5120) ∧
    -Real.log (3913 / 5120) ≤ (16803131 / 62500000) := by
  have h := checkLog_sound (w := (1207 / 9033)) (n := 12)
    (lo := (53770019 / 200000000)) (hi := (16803131 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3913) = 1/(3913 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-16803131 / 62500000) (-53770019 / 200000000) (Real.log (3913 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (211434643 / 1000000000) ≤ -Real.log (10240 / 12651) ∧
    -Real.log (10240 / 12651) ≤ (52858661 / 250000000) := by
  have h := checkLog_sound (w := (2411 / 22891)) (n := 12)
    (lo := (211434643 / 1000000000)) (hi := (52858661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12651 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12651 / 10240) = 1/(10240 / 12651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (211434643 / 1000000000) (52858661 / 250000000) (Real.log (12651 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12651 / 10240) = -Real.log (10240 / 12651) := by
    rw [show ((12651 / 10240) : ℝ) = ((10240 / 12651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (268466831 / 1000000000) ≤ -Real.log (7829 / 10240) ∧
    -Real.log (7829 / 10240) ≤ (16779177 / 62500000) := by
  have h := checkLog_sound (w := (2411 / 18069)) (n := 12)
    (lo := (268466831 / 1000000000)) (hi := (16779177 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7829) = 1/(7829 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16779177 / 62500000) (-268466831 / 1000000000) (Real.log (7829 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38627167 / 100000000) ≤ -Real.log (2560 / 3767) ∧
    -Real.log (2560 / 3767) ≤ (386271671 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 6327)) (n := 12)
    (lo := (38627167 / 100000000)) (hi := (386271671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3767 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3767 / 2560) = 1/(2560 / 3767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38627167 / 100000000) (386271671 / 1000000000) (Real.log (3767 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3767 / 2560) = -Real.log (2560 / 3767) := by
    rw [show ((3767 / 2560) : ℝ) = ((2560 / 3767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (637682909 / 1000000000) ≤ -Real.log (1353 / 2560) ∧
    -Real.log (1353 / 2560) ≤ (63768291 / 100000000) := by
  have h := checkLog_sound (w := (1207 / 3913)) (n := 12)
    (lo := (637682909 / 1000000000)) (hi := (63768291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1353) = 1/(1353 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-63768291 / 100000000) (-637682909 / 1000000000) (Real.log (1353 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (96468349 / 250000000) ≤ -Real.log (5120 / 7531) ∧
    -Real.log (5120 / 7531) ≤ (385873397 / 1000000000) := by
  have h := checkLog_sound (w := (2411 / 12651)) (n := 12)
    (lo := (96468349 / 250000000)) (hi := (385873397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7531 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7531 / 5120) = 1/(5120 / 7531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (96468349 / 250000000) (385873397 / 1000000000) (Real.log (7531 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7531 / 5120) = -Real.log (5120 / 7531) := by
    rw [show ((7531 / 5120) : ℝ) = ((5120 / 7531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5092599 / 8000000) ≤ -Real.log (2709 / 5120) ∧
    -Real.log (2709 / 5120) ≤ (159143719 / 250000000) := by
  have h := checkLog_sound (w := (2411 / 7829)) (n := 12)
    (lo := (5092599 / 8000000)) (hi := (159143719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2709) = 1/(2709 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159143719 / 250000000) (-5092599 / 8000000) (Real.log (2709 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (289959227 / 1000000000) ≤ -Real.log (1000000 / 1336373) ∧
    -Real.log (1000000 / 1336373) ≤ (72489807 / 250000000) := by
  have h := checkLog_sound (w := (336373 / 2336373)) (n := 12)
    (lo := (289959227 / 1000000000)) (hi := (72489807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1336373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1336373 / 1000000) = 1/(1000000 / 1336373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (289959227 / 1000000000) (72489807 / 250000000) (Real.log (1336373 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1336373 / 1000000) = -Real.log (1000000 / 1336373) := by
    rw [show ((1336373 / 1000000) : ℝ) = ((1000000 / 1336373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (205017517 / 500000000) ≤ -Real.log (663627 / 1000000) ∧
    -Real.log (663627 / 1000000) ≤ (82007007 / 200000000) := by
  have h := checkLog_sound (w := (336373 / 1663627)) (n := 12)
    (lo := (205017517 / 500000000)) (hi := (82007007 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 663627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 663627) = 1/(663627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-82007007 / 200000000) (-205017517 / 500000000) (Real.log (663627 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145140097 / 500000000) ≤ -Real.log (500000 / 668401) ∧
    -Real.log (500000 / 668401) ≤ (58056039 / 200000000) := by
  have h := checkLog_sound (w := (168401 / 1168401)) (n := 12)
    (lo := (145140097 / 500000000)) (hi := (58056039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668401 / 500000) = 1/(500000 / 668401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145140097 / 500000000) (58056039 / 200000000) (Real.log (668401 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (668401 / 500000) = -Real.log (500000 / 668401) := by
    rw [show ((668401 / 500000) : ℝ) = ((500000 / 668401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (41068169 / 100000000) ≤ -Real.log (331599 / 500000) ∧
    -Real.log (331599 / 500000) ≤ (410681691 / 1000000000) := by
  have h := checkLog_sound (w := (168401 / 831599)) (n := 12)
    (lo := (41068169 / 100000000)) (hi := (410681691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331599) = 1/(331599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-410681691 / 1000000000) (-41068169 / 100000000) (Real.log (331599 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21956917 / 100000000) ≤ -Real.log (50000 / 62277) ∧
    -Real.log (50000 / 62277) ≤ (219569171 / 1000000000) := by
  have h := checkLog_sound (w := (12277 / 112277)) (n := 12)
    (lo := (21956917 / 100000000)) (hi := (219569171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62277 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62277 / 50000) = 1/(50000 / 62277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21956917 / 100000000) (219569171 / 1000000000) (Real.log (62277 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (62277 / 50000) = -Real.log (50000 / 62277) := by
    rw [show ((62277 / 50000) : ℝ) = ((50000 / 62277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (281753017 / 1000000000) ≤ -Real.log (37723 / 50000) ∧
    -Real.log (37723 / 50000) ≤ (140876509 / 500000000) := by
  have h := checkLog_sound (w := (12277 / 87723)) (n := 12)
    (lo := (281753017 / 1000000000)) (hi := (140876509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37723) = 1/(37723 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-140876509 / 500000000) (-281753017 / 1000000000) (Real.log (37723 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219837291 / 1000000000) ≤ -Real.log (500000 / 622937) ∧
    -Real.log (500000 / 622937) ≤ (54959323 / 250000000) := by
  have h := checkLog_sound (w := (122937 / 1122937)) (n := 12)
    (lo := (219837291 / 1000000000)) (hi := (54959323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(622937 / 500000) = 1/(500000 / 622937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219837291 / 1000000000) (54959323 / 250000000) (Real.log (622937 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (622937 / 500000) = -Real.log (500000 / 622937) := by
    rw [show ((622937 / 500000) : ℝ) = ((500000 / 622937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (35274477 / 125000000) ≤ -Real.log (377063 / 500000) ∧
    -Real.log (377063 / 500000) ≤ (282195817 / 1000000000) := by
  have h := checkLog_sound (w := (122937 / 877063)) (n := 12)
    (lo := (35274477 / 125000000)) (hi := (282195817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 377063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 377063) = 1/(377063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-282195817 / 1000000000) (-35274477 / 125000000) (Real.log (377063 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (699994261 / 1000000000) ≤ -Real.log (500000000000 / 1006870576393) ∧
    -Real.log (500000000000 / 1006870576393) ≤ (699994263 / 1000000000) := by
  have h := checkLog_sound (w := (6870576393 / 2006870576393)) (n := 12)
    (lo := (6847081 / 1000000000)) (hi := (3423541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006870576393 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1006870576393 / 1000000000000) = 1/(500000000000 / 1006870576393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (699994261 / 1000000000) (699994263 / 1000000000) (Real.log (1006870576393 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1006870576393 / 500000000000) = -Real.log (500000000000 / 1006870576393) := by
    rw [show ((1006870576393 / 500000000000) : ℝ) = ((500000000000 / 1006870576393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (175240471 / 250000000) ≤ -Real.log (125000000000 / 251961329799) ∧
    -Real.log (125000000000 / 251961329799) ≤ (350480943 / 500000000) := by
  have h := checkLog_sound (w := (1961329799 / 501961329799)) (n := 12)
    (lo := (488419 / 62500000)) (hi := (1562941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251961329799 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(251961329799 / 250000000000) = 1/(125000000000 / 251961329799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (175240471 / 250000000) (350480943 / 500000000) (Real.log (251961329799 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (251961329799 / 125000000000) = -Real.log (125000000000 / 251961329799) := by
    rw [show ((251961329799 / 125000000000) : ℝ) = ((125000000000 / 251961329799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (125330547 / 250000000) ≤ -Real.log (500000000000 / 825451316173) ∧
    -Real.log (500000000000 / 825451316173) ≤ (501322189 / 1000000000) := by
  have h := checkLog_sound (w := (325451316173 / 1325451316173)) (n := 12)
    (lo := (125330547 / 250000000)) (hi := (501322189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825451316173 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825451316173 / 500000000000) = 1/(500000000000 / 825451316173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (125330547 / 250000000) (501322189 / 1000000000) (Real.log (825451316173 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (825451316173 / 500000000000) = -Real.log (500000000000 / 825451316173) := by
    rw [show ((825451316173 / 500000000000) : ℝ) = ((500000000000 / 825451316173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (502033107 / 1000000000) ≤ -Real.log (250000000000 / 413019177167) ∧
    -Real.log (250000000000 / 413019177167) ≤ (125508277 / 250000000) := by
  have h := checkLog_sound (w := (163019177167 / 663019177167)) (n := 12)
    (lo := (502033107 / 1000000000)) (hi := (125508277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413019177167 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413019177167 / 250000000000) = 1/(250000000000 / 413019177167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (502033107 / 1000000000) (125508277 / 250000000) (Real.log (413019177167 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (413019177167 / 250000000000) = -Real.log (250000000000 / 413019177167) := by
    rw [show ((413019177167 / 250000000000) : ℝ) = ((250000000000 / 413019177167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0352

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0353Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0353
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

theorem reflection_log_1_neg : (211434643 / 1000000000) ≤ -Real.log (10240 / 12651) ∧
    -Real.log (10240 / 12651) ≤ (52858661 / 250000000) := by
  have h := checkLog_sound (w := (2411 / 22891)) (n := 12)
    (lo := (211434643 / 1000000000)) (hi := (52858661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12651 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12651 / 10240) = 1/(10240 / 12651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (211434643 / 1000000000) (52858661 / 250000000) (Real.log (12651 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12651 / 10240) = -Real.log (10240 / 12651) := by
    rw [show ((12651 / 10240) : ℝ) = ((10240 / 12651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (268466831 / 1000000000) ≤ -Real.log (7829 / 10240) ∧
    -Real.log (7829 / 10240) ≤ (16779177 / 62500000) := by
  have h := checkLog_sound (w := (2411 / 18069)) (n := 12)
    (lo := (268466831 / 1000000000)) (hi := (16779177 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7829) = 1/(7829 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-16779177 / 62500000) (-268466831 / 1000000000) (Real.log (7829 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5279937 / 25000000) ≤ -Real.log (1280 / 1581) ∧
    -Real.log (1280 / 1581) ≤ (211197481 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 2861)) (n := 12)
    (lo := (5279937 / 25000000)) (hi := (211197481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1581 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1581 / 1280) = 1/(1280 / 1581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5279937 / 25000000) (211197481 / 1000000000) (Real.log (1581 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1581 / 1280) = -Real.log (1280 / 1581) := by
    rw [show ((1581 / 1280) : ℝ) = ((1280 / 1581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (134041857 / 500000000) ≤ -Real.log (979 / 1280) ∧
    -Real.log (979 / 1280) ≤ (53616743 / 200000000) := by
  have h := checkLog_sound (w := (301 / 2259)) (n := 12)
    (lo := (134041857 / 500000000)) (hi := (53616743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 979) = 1/(979 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-53616743 / 200000000) (-134041857 / 500000000) (Real.log (979 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (96468349 / 250000000) ≤ -Real.log (5120 / 7531) ∧
    -Real.log (5120 / 7531) ≤ (385873397 / 1000000000) := by
  have h := checkLog_sound (w := (2411 / 12651)) (n := 12)
    (lo := (96468349 / 250000000)) (hi := (385873397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7531 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7531 / 5120) = 1/(5120 / 7531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (96468349 / 250000000) (385873397 / 1000000000) (Real.log (7531 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7531 / 5120) = -Real.log (5120 / 7531) := by
    rw [show ((7531 / 5120) : ℝ) = ((5120 / 7531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5092599 / 8000000) ≤ -Real.log (2709 / 5120) ∧
    -Real.log (2709 / 5120) ≤ (159143719 / 250000000) := by
  have h := checkLog_sound (w := (2411 / 7829)) (n := 12)
    (lo := (5092599 / 8000000)) (hi := (159143719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2709) = 1/(2709 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159143719 / 250000000) (-5092599 / 8000000) (Real.log (2709 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (385474963 / 1000000000) ≤ -Real.log (640 / 941) ∧
    -Real.log (640 / 941) ≤ (96368741 / 250000000) := by
  have h := checkLog_sound (w := (301 / 1581)) (n := 12)
    (lo := (385474963 / 1000000000)) (hi := (96368741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941 / 640) = 1/(640 / 941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (385474963 / 1000000000) (96368741 / 250000000) (Real.log (941 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (941 / 640) = -Real.log (640 / 941) := by
    rw [show ((941 / 640) : ℝ) = ((640 / 941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (158867017 / 250000000) ≤ -Real.log (339 / 640) ∧
    -Real.log (339 / 640) ≤ (635468069 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 979)) (n := 12)
    (lo := (158867017 / 250000000)) (hi := (635468069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 339) = 1/(339 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-635468069 / 1000000000) (-158867017 / 250000000) (Real.log (339 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (144819453 / 500000000) ≤ -Real.log (200000 / 267189) ∧
    -Real.log (200000 / 267189) ≤ (289638907 / 1000000000) := by
  have h := checkLog_sound (w := (67189 / 467189)) (n := 12)
    (lo := (144819453 / 500000000)) (hi := (289638907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267189 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267189 / 200000) = 1/(200000 / 267189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (144819453 / 500000000) (289638907 / 1000000000) (Real.log (267189 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (267189 / 200000) = -Real.log (200000 / 267189) := by
    rw [show ((267189 / 200000) : ℝ) = ((200000 / 267189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (409390301 / 1000000000) ≤ -Real.log (132811 / 200000) ∧
    -Real.log (132811 / 200000) ≤ (204695151 / 500000000) := by
  have h := checkLog_sound (w := (67189 / 332811)) (n := 12)
    (lo := (409390301 / 1000000000)) (hi := (204695151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132811) = 1/(132811 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-204695151 / 500000000) (-409390301 / 1000000000) (Real.log (132811 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (36244997 / 125000000) ≤ -Real.log (500000 / 668187) ∧
    -Real.log (500000 / 668187) ≤ (289959977 / 1000000000) := by
  have h := checkLog_sound (w := (168187 / 1168187)) (n := 12)
    (lo := (36244997 / 125000000)) (hi := (289959977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668187 / 500000) = 1/(500000 / 668187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (36244997 / 125000000) (289959977 / 1000000000) (Real.log (668187 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (668187 / 500000) = -Real.log (500000 / 668187) := by
    rw [show ((668187 / 500000) : ℝ) = ((500000 / 668187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (410036541 / 1000000000) ≤ -Real.log (331813 / 500000) ∧
    -Real.log (331813 / 500000) ≤ (205018271 / 500000000) := by
  have h := checkLog_sound (w := (168187 / 831813)) (n := 12)
    (lo := (410036541 / 1000000000)) (hi := (205018271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331813) = 1/(331813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-205018271 / 500000000) (-410036541 / 1000000000) (Real.log (331813 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (27412823 / 125000000) ≤ -Real.log (125000 / 155651) ∧
    -Real.log (125000 / 155651) ≤ (43860517 / 200000000) := by
  have h := checkLog_sound (w := (30651 / 280651)) (n := 12)
    (lo := (27412823 / 125000000)) (hi := (43860517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155651 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155651 / 125000) = 1/(125000 / 155651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (27412823 / 125000000) (43860517 / 200000000) (Real.log (155651 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (155651 / 125000) = -Real.log (125000 / 155651) := by
    rw [show ((155651 / 125000) : ℝ) = ((125000 / 155651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (35164133 / 125000000) ≤ -Real.log (94349 / 125000) ∧
    -Real.log (94349 / 125000) ≤ (56262613 / 200000000) := by
  have h := checkLog_sound (w := (30651 / 219349)) (n := 12)
    (lo := (35164133 / 125000000)) (hi := (56262613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94349) = 1/(94349 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-56262613 / 200000000) (-35164133 / 125000000) (Real.log (94349 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219569973 / 1000000000) ≤ -Real.log (1000000 / 1245541) ∧
    -Real.log (1000000 / 1245541) ≤ (109784987 / 500000000) := by
  have h := checkLog_sound (w := (245541 / 2245541)) (n := 12)
    (lo := (219569973 / 1000000000)) (hi := (109784987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245541 / 1000000) = 1/(1000000 / 1245541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219569973 / 1000000000) (109784987 / 500000000) (Real.log (1245541 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1245541 / 1000000) = -Real.log (1000000 / 1245541) := by
    rw [show ((1245541 / 1000000) : ℝ) = ((1000000 / 1245541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140877171 / 500000000) ≤ -Real.log (754459 / 1000000) ∧
    -Real.log (754459 / 1000000) ≤ (281754343 / 1000000000) := by
  have h := checkLog_sound (w := (245541 / 1754459)) (n := 12)
    (lo := (140877171 / 500000000)) (hi := (281754343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754459) = 1/(754459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-281754343 / 1000000000) (-140877171 / 500000000) (Real.log (754459 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (699029207 / 1000000000) ≤ -Real.log (100000000000 / 201179872149) ∧
    -Real.log (100000000000 / 201179872149) ≤ (699029209 / 1000000000) := by
  have h := checkLog_sound (w := (1179872149 / 401179872149)) (n := 12)
    (lo := (5882027 / 1000000000)) (hi := (1470507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201179872149 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(201179872149 / 200000000000) = 1/(100000000000 / 201179872149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (699029207 / 1000000000) (699029209 / 1000000000) (Real.log (201179872149 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (201179872149 / 100000000000) = -Real.log (100000000000 / 201179872149) := by
    rw [show ((201179872149 / 100000000000) : ℝ) = ((100000000000 / 201179872149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (174999129 / 250000000) ≤ -Real.log (31250000000 / 62929552941) ∧
    -Real.log (31250000000 / 62929552941) ≤ (349998259 / 500000000) := by
  have h := checkLog_sound (w := (429552941 / 125429552941)) (n := 12)
    (lo := (856167 / 125000000)) (hi := (6849337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62929552941 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62929552941 / 62500000000) = 1/(31250000000 / 62929552941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (174999129 / 250000000) (349998259 / 500000000) (Real.log (62929552941 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (62929552941 / 31250000000) = -Real.log (31250000000 / 62929552941) := by
    rw [show ((62929552941 / 31250000000) : ℝ) = ((31250000000 / 62929552941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15644239 / 31250000) ≤ -Real.log (50000000000 / 82486830809) ∧
    -Real.log (50000000000 / 82486830809) ≤ (500615649 / 1000000000) := by
  have h := checkLog_sound (w := (32486830809 / 132486830809)) (n := 12)
    (lo := (15644239 / 31250000)) (hi := (500615649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82486830809 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82486830809 / 50000000000) = 1/(50000000000 / 82486830809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15644239 / 31250000) (500615649 / 1000000000) (Real.log (82486830809 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (82486830809 / 50000000000) = -Real.log (50000000000 / 82486830809) := by
    rw [show ((82486830809 / 50000000000) : ℝ) = ((50000000000 / 82486830809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (125331079 / 250000000) ≤ -Real.log (500000000000 / 825453072997) ∧
    -Real.log (500000000000 / 825453072997) ≤ (501324317 / 1000000000) := by
  have h := checkLog_sound (w := (325453072997 / 1325453072997)) (n := 12)
    (lo := (125331079 / 250000000)) (hi := (501324317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825453072997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825453072997 / 500000000000) = 1/(500000000000 / 825453072997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (125331079 / 250000000) (501324317 / 1000000000) (Real.log (825453072997 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (825453072997 / 500000000000) = -Real.log (500000000000 / 825453072997) := by
    rw [show ((825453072997 / 500000000000) : ℝ) = ((500000000000 / 825453072997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0353

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0354Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0354
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

theorem reflection_log_1_neg : (5279937 / 25000000) ≤ -Real.log (1280 / 1581) ∧
    -Real.log (1280 / 1581) ≤ (211197481 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 2861)) (n := 12)
    (lo := (5279937 / 25000000)) (hi := (211197481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1581 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1581 / 1280) = 1/(1280 / 1581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5279937 / 25000000) (211197481 / 1000000000) (Real.log (1581 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1581 / 1280) = -Real.log (1280 / 1581) := by
    rw [show ((1581 / 1280) : ℝ) = ((1280 / 1581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (134041857 / 500000000) ≤ -Real.log (979 / 1280) ∧
    -Real.log (979 / 1280) ≤ (53616743 / 200000000) := by
  have h := checkLog_sound (w := (301 / 2259)) (n := 12)
    (lo := (134041857 / 500000000)) (hi := (53616743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 979) = 1/(979 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-53616743 / 200000000) (-134041857 / 500000000) (Real.log (979 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10548013 / 50000000) ≤ -Real.log (2048 / 2529) ∧
    -Real.log (2048 / 2529) ≤ (210960261 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 4577)) (n := 12)
    (lo := (10548013 / 50000000)) (hi := (210960261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2529 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2529 / 2048) = 1/(2048 / 2529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10548013 / 50000000) (210960261 / 1000000000) (Real.log (2529 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2529 / 2048) = -Real.log (2048 / 2529) := by
    rw [show ((2529 / 2048) : ℝ) = ((2048 / 2529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (267700743 / 1000000000) ≤ -Real.log (1567 / 2048) ∧
    -Real.log (1567 / 2048) ≤ (33462593 / 125000000) := by
  have h := checkLog_sound (w := (481 / 3615)) (n := 12)
    (lo := (267700743 / 1000000000)) (hi := (33462593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1567) = 1/(1567 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33462593 / 125000000) (-267700743 / 1000000000) (Real.log (1567 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (385474963 / 1000000000) ≤ -Real.log (640 / 941) ∧
    -Real.log (640 / 941) ≤ (96368741 / 250000000) := by
  have h := checkLog_sound (w := (301 / 1581)) (n := 12)
    (lo := (385474963 / 1000000000)) (hi := (96368741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941 / 640) = 1/(640 / 941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (385474963 / 1000000000) (96368741 / 250000000) (Real.log (941 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (941 / 640) = -Real.log (640 / 941) := by
    rw [show ((941 / 640) : ℝ) = ((640 / 941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (158867017 / 250000000) ≤ -Real.log (339 / 640) ∧
    -Real.log (339 / 640) ≤ (635468069 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 979)) (n := 12)
    (lo := (158867017 / 250000000)) (hi := (635468069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 339) = 1/(339 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-635468069 / 1000000000) (-158867017 / 250000000) (Real.log (339 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (385076371 / 1000000000) ≤ -Real.log (1024 / 1505) ∧
    -Real.log (1024 / 1505) ≤ (96269093 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2529)) (n := 12)
    (lo := (385076371 / 1000000000)) (hi := (96269093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1505 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1505 / 1024) = 1/(1024 / 1505) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (385076371 / 1000000000) (96269093 / 250000000) (Real.log (1505 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1505 / 1024) = -Real.log (1024 / 1505) := by
    rw [show ((1505 / 1024) : ℝ) = ((1024 / 1505) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126872497 / 200000000) ≤ -Real.log (543 / 1024) ∧
    -Real.log (543 / 1024) ≤ (317181243 / 500000000) := by
  have h := checkLog_sound (w := (481 / 1567)) (n := 12)
    (lo := (126872497 / 200000000)) (hi := (317181243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 543) = 1/(543 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-317181243 / 500000000) (-126872497 / 200000000) (Real.log (543 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (289319231 / 1000000000) ≤ -Real.log (500000 / 667759) ∧
    -Real.log (500000 / 667759) ≤ (4520613 / 15625000) := by
  have h := checkLog_sound (w := (167759 / 1167759)) (n := 12)
    (lo := (289319231 / 1000000000)) (hi := (4520613 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667759 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667759 / 500000) = 1/(500000 / 667759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (289319231 / 1000000000) (4520613 / 15625000) (Real.log (667759 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (667759 / 500000) = -Real.log (500000 / 667759) := by
    rw [show ((667759 / 500000) : ℝ) = ((500000 / 667759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (408747489 / 1000000000) ≤ -Real.log (332241 / 500000) ∧
    -Real.log (332241 / 500000) ≤ (40874749 / 100000000) := by
  have h := checkLog_sound (w := (167759 / 832241)) (n := 12)
    (lo := (408747489 / 1000000000)) (hi := (40874749 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 332241) = 1/(332241 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-40874749 / 100000000) (-408747489 / 1000000000) (Real.log (332241 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (57927931 / 200000000) ≤ -Real.log (500000 / 667973) ∧
    -Real.log (500000 / 667973) ≤ (36204957 / 125000000) := by
  have h := checkLog_sound (w := (167973 / 1167973)) (n := 12)
    (lo := (57927931 / 200000000)) (hi := (36204957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667973 / 500000) = 1/(500000 / 667973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (57927931 / 200000000) (36204957 / 125000000) (Real.log (667973 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (667973 / 500000) = -Real.log (500000 / 667973) := by
    rw [show ((667973 / 500000) : ℝ) = ((500000 / 667973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (409391807 / 1000000000) ≤ -Real.log (332027 / 500000) ∧
    -Real.log (332027 / 500000) ≤ (6396747 / 15625000) := by
  have h := checkLog_sound (w := (167973 / 832027)) (n := 12)
    (lo := (409391807 / 1000000000)) (hi := (6396747 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 332027) = 1/(332027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6396747 / 15625000) (-409391807 / 1000000000) (Real.log (332027 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (109517963 / 500000000) ≤ -Real.log (250000 / 311219) ∧
    -Real.log (250000 / 311219) ≤ (219035927 / 1000000000) := by
  have h := checkLog_sound (w := (61219 / 561219)) (n := 12)
    (lo := (109517963 / 500000000)) (hi := (219035927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311219 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311219 / 250000) = 1/(250000 / 311219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (109517963 / 500000000) (219035927 / 1000000000) (Real.log (311219 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (311219 / 250000) = -Real.log (250000 / 311219) := by
    rw [show ((311219 / 250000) : ℝ) = ((250000 / 311219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (35109163 / 125000000) ≤ -Real.log (188781 / 250000) ∧
    -Real.log (188781 / 250000) ≤ (56174661 / 200000000) := by
  have h := checkLog_sound (w := (61219 / 438781)) (n := 12)
    (lo := (35109163 / 125000000)) (hi := (56174661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188781) = 1/(188781 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-56174661 / 200000000) (-35109163 / 125000000) (Real.log (188781 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219303387 / 1000000000) ≤ -Real.log (1000000 / 1245209) ∧
    -Real.log (1000000 / 1245209) ≤ (54825847 / 250000000) := by
  have h := checkLog_sound (w := (245209 / 2245209)) (n := 12)
    (lo := (219303387 / 1000000000)) (hi := (54825847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245209 / 1000000) = 1/(1000000 / 1245209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219303387 / 1000000000) (54825847 / 250000000) (Real.log (1245209 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1245209 / 1000000) = -Real.log (1000000 / 1245209) := by
    rw [show ((1245209 / 1000000) : ℝ) = ((1000000 / 1245209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (281314389 / 1000000000) ≤ -Real.log (754791 / 1000000) ∧
    -Real.log (754791 / 1000000) ≤ (28131439 / 100000000) := by
  have h := checkLog_sound (w := (245209 / 1754791)) (n := 12)
    (lo := (281314389 / 1000000000)) (hi := (28131439 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754791) = 1/(754791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-28131439 / 100000000) (-281314389 / 1000000000) (Real.log (754791 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4362917 / 6250000) ≤ -Real.log (500000000000 / 1004931661053) ∧
    -Real.log (500000000000 / 1004931661053) ≤ (349033361 / 500000000) := by
  have h := checkLog_sound (w := (4931661053 / 2004931661053)) (n := 12)
    (lo := (245977 / 50000000)) (hi := (4919541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1004931661053 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1004931661053 / 1000000000000) = 1/(500000000000 / 1004931661053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4362917 / 6250000) (349033361 / 500000000) (Real.log (1004931661053 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1004931661053 / 500000000000) = -Real.log (500000000000 / 1004931661053) := by
    rw [show ((1004931661053 / 500000000000) : ℝ) = ((500000000000 / 1004931661053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (349515731 / 500000000) ≤ -Real.log (500000000000 / 1005901628483) ∧
    -Real.log (500000000000 / 1005901628483) ≤ (87378933 / 125000000) := by
  have h := checkLog_sound (w := (5901628483 / 2005901628483)) (n := 12)
    (lo := (2942141 / 500000000)) (hi := (5884283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1005901628483 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1005901628483 / 1000000000000) = 1/(500000000000 / 1005901628483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (349515731 / 500000000) (87378933 / 125000000) (Real.log (1005901628483 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1005901628483 / 500000000000) = -Real.log (500000000000 / 1005901628483) := by
    rw [show ((1005901628483 / 500000000000) : ℝ) = ((500000000000 / 1005901628483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (499909231 / 1000000000) ≤ -Real.log (500000000000 / 824285812661) ∧
    -Real.log (500000000000 / 824285812661) ≤ (31244327 / 62500000) := by
  have h := checkLog_sound (w := (324285812661 / 1324285812661)) (n := 12)
    (lo := (499909231 / 1000000000)) (hi := (31244327 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824285812661 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824285812661 / 500000000000) = 1/(500000000000 / 824285812661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (499909231 / 1000000000) (31244327 / 62500000) (Real.log (824285812661 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (824285812661 / 500000000000) = -Real.log (500000000000 / 824285812661) := by
    rw [show ((824285812661 / 500000000000) : ℝ) = ((500000000000 / 824285812661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (31288611 / 62500000) ≤ -Real.log (500000000000 / 824870063369) ∧
    -Real.log (500000000000 / 824870063369) ≤ (500617777 / 1000000000) := by
  have h := checkLog_sound (w := (324870063369 / 1324870063369)) (n := 12)
    (lo := (31288611 / 62500000)) (hi := (500617777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824870063369 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824870063369 / 500000000000) = 1/(500000000000 / 824870063369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (31288611 / 62500000) (500617777 / 1000000000) (Real.log (824870063369 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (824870063369 / 500000000000) = -Real.log (500000000000 / 824870063369) := by
    rw [show ((824870063369 / 500000000000) : ℝ) = ((500000000000 / 824870063369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0354

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0355Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0355
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

theorem reflection_log_1_neg : (10548013 / 50000000) ≤ -Real.log (2048 / 2529) ∧
    -Real.log (2048 / 2529) ≤ (210960261 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 4577)) (n := 12)
    (lo := (10548013 / 50000000)) (hi := (210960261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2529 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2529 / 2048) = 1/(2048 / 2529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10548013 / 50000000) (210960261 / 1000000000) (Real.log (2529 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2529 / 2048) = -Real.log (2048 / 2529) := by
    rw [show ((2529 / 2048) : ℝ) = ((2048 / 2529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (267700743 / 1000000000) ≤ -Real.log (1567 / 2048) ∧
    -Real.log (1567 / 2048) ≤ (33462593 / 125000000) := by
  have h := checkLog_sound (w := (481 / 3615)) (n := 12)
    (lo := (267700743 / 1000000000)) (hi := (33462593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1567) = 1/(1567 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33462593 / 125000000) (-267700743 / 1000000000) (Real.log (1567 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (26340373 / 125000000) ≤ -Real.log (5120 / 6321) ∧
    -Real.log (5120 / 6321) ≤ (42144597 / 200000000) := by
  have h := checkLog_sound (w := (1201 / 11441)) (n := 12)
    (lo := (26340373 / 125000000)) (hi := (42144597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6321 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6321 / 5120) = 1/(5120 / 6321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (26340373 / 125000000) (42144597 / 200000000) (Real.log (6321 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6321 / 5120) = -Real.log (5120 / 6321) := by
    rw [show ((6321 / 5120) : ℝ) = ((5120 / 6321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (267317919 / 1000000000) ≤ -Real.log (3919 / 5120) ∧
    -Real.log (3919 / 5120) ≤ (1670737 / 6250000) := by
  have h := checkLog_sound (w := (1201 / 9039)) (n := 12)
    (lo := (267317919 / 1000000000)) (hi := (1670737 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3919) = 1/(3919 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1670737 / 6250000) (-267317919 / 1000000000) (Real.log (3919 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (385076371 / 1000000000) ≤ -Real.log (1024 / 1505) ∧
    -Real.log (1024 / 1505) ≤ (96269093 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2529)) (n := 12)
    (lo := (385076371 / 1000000000)) (hi := (96269093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1505 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1505 / 1024) = 1/(1024 / 1505) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (385076371 / 1000000000) (96269093 / 250000000) (Real.log (1505 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1505 / 1024) = -Real.log (1024 / 1505) := by
    rw [show ((1505 / 1024) : ℝ) = ((1024 / 1505) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (126872497 / 200000000) ≤ -Real.log (543 / 1024) ∧
    -Real.log (543 / 1024) ≤ (317181243 / 500000000) := by
  have h := checkLog_sound (w := (481 / 1567)) (n := 12)
    (lo := (126872497 / 200000000)) (hi := (317181243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 543) = 1/(543 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-317181243 / 500000000) (-126872497 / 200000000) (Real.log (543 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19233881 / 50000000) ≤ -Real.log (2560 / 3761) ∧
    -Real.log (2560 / 3761) ≤ (384677621 / 1000000000) := by
  have h := checkLog_sound (w := (1201 / 6321)) (n := 12)
    (lo := (19233881 / 50000000)) (hi := (384677621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3761 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3761 / 2560) = 1/(2560 / 3761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (19233881 / 50000000) (384677621 / 1000000000) (Real.log (3761 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3761 / 2560) = -Real.log (2560 / 3761) := by
    rw [show ((3761 / 2560) : ℝ) = ((2560 / 3761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (633258123 / 1000000000) ≤ -Real.log (1359 / 2560) ∧
    -Real.log (1359 / 2560) ≤ (158314531 / 250000000) := by
  have h := checkLog_sound (w := (1201 / 3919)) (n := 12)
    (lo := (633258123 / 1000000000)) (hi := (158314531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1359) = 1/(1359 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-158314531 / 250000000) (-633258123 / 1000000000) (Real.log (1359 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (57799741 / 200000000) ≤ -Real.log (100000 / 133509) ∧
    -Real.log (100000 / 133509) ≤ (144499353 / 500000000) := by
  have h := checkLog_sound (w := (33509 / 233509)) (n := 12)
    (lo := (57799741 / 200000000)) (hi := (144499353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133509 / 100000) = 1/(100000 / 133509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (57799741 / 200000000) (144499353 / 500000000) (Real.log (133509 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (133509 / 100000) = -Real.log (100000 / 133509) := by
    rw [show ((133509 / 100000) : ℝ) = ((100000 / 133509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81620717 / 200000000) ≤ -Real.log (66491 / 100000) ∧
    -Real.log (66491 / 100000) ≤ (204051793 / 500000000) := by
  have h := checkLog_sound (w := (33509 / 166491)) (n := 12)
    (lo := (81620717 / 200000000)) (hi := (204051793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66491) = 1/(66491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-204051793 / 500000000) (-81620717 / 200000000) (Real.log (66491 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (14465999 / 50000000) ≤ -Real.log (1000000 / 1335519) ∧
    -Real.log (1000000 / 1335519) ≤ (289319981 / 1000000000) := by
  have h := checkLog_sound (w := (335519 / 2335519)) (n := 12)
    (lo := (14465999 / 50000000)) (hi := (289319981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1335519 / 1000000) = 1/(1000000 / 1335519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (14465999 / 50000000) (289319981 / 1000000000) (Real.log (1335519 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1335519 / 1000000) = -Real.log (1000000 / 1335519) := by
    rw [show ((1335519 / 1000000) : ℝ) = ((1000000 / 1335519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (204374497 / 500000000) ≤ -Real.log (664481 / 1000000) ∧
    -Real.log (664481 / 1000000) ≤ (81749799 / 200000000) := by
  have h := checkLog_sound (w := (335519 / 1664481)) (n := 12)
    (lo := (204374497 / 500000000)) (hi := (81749799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 664481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 664481) = 1/(664481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-81749799 / 200000000) (-204374497 / 500000000) (Real.log (664481 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (109384197 / 500000000) ≤ -Real.log (1000000 / 1244543) ∧
    -Real.log (1000000 / 1244543) ≤ (43753679 / 200000000) := by
  have h := checkLog_sound (w := (244543 / 2244543)) (n := 12)
    (lo := (109384197 / 500000000)) (hi := (43753679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244543 / 1000000) = 1/(1000000 / 1244543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (109384197 / 500000000) (43753679 / 200000000) (Real.log (1244543 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1244543 / 1000000) = -Real.log (1000000 / 1244543) := by
    rw [show ((1244543 / 1000000) : ℝ) = ((1000000 / 1244543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (140216207 / 500000000) ≤ -Real.log (755457 / 1000000) ∧
    -Real.log (755457 / 1000000) ≤ (56086483 / 200000000) := by
  have h := checkLog_sound (w := (244543 / 1755457)) (n := 12)
    (lo := (140216207 / 500000000)) (hi := (56086483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755457) = 1/(755457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-56086483 / 200000000) (-140216207 / 500000000) (Real.log (755457 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219036729 / 1000000000) ≤ -Real.log (1000000 / 1244877) ∧
    -Real.log (1000000 / 1244877) ≤ (21903673 / 100000000) := by
  have h := checkLog_sound (w := (244877 / 2244877)) (n := 12)
    (lo := (219036729 / 1000000000)) (hi := (21903673 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244877 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244877 / 1000000) = 1/(1000000 / 1244877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219036729 / 1000000000) (21903673 / 100000000) (Real.log (1244877 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1244877 / 1000000) = -Real.log (1000000 / 1244877) := by
    rw [show ((1244877 / 1000000) : ℝ) = ((1000000 / 1244877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (280874629 / 1000000000) ≤ -Real.log (755123 / 1000000) ∧
    -Real.log (755123 / 1000000) ≤ (28087463 / 100000000) := by
  have h := checkLog_sound (w := (244877 / 1755123)) (n := 12)
    (lo := (280874629 / 1000000000)) (hi := (28087463 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755123) = 1/(755123 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-28087463 / 100000000) (-280874629 / 1000000000) (Real.log (755123 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (69710229 / 100000000) ≤ -Real.log (500000000000 / 1003962942353) ∧
    -Real.log (500000000000 / 1003962942353) ≤ (174275573 / 250000000) := by
  have h := checkLog_sound (w := (3962942353 / 2003962942353)) (n := 12)
    (lo := (395511 / 100000000)) (hi := (3955111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1003962942353 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1003962942353 / 1000000000000) = 1/(500000000000 / 1003962942353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (69710229 / 100000000) (174275573 / 250000000) (Real.log (1003962942353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1003962942353 / 500000000000) = -Real.log (500000000000 / 1003962942353) := by
    rw [show ((1003962942353 / 500000000000) : ℝ) = ((500000000000 / 1003962942353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (698068973 / 1000000000) ≤ -Real.log (125000000000 / 251233481469) ∧
    -Real.log (125000000000 / 251233481469) ≤ (27922759 / 40000000) := by
  have h := checkLog_sound (w := (1233481469 / 501233481469)) (n := 12)
    (lo := (4921793 / 1000000000)) (hi := (2460897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251233481469 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(251233481469 / 250000000000) = 1/(125000000000 / 251233481469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (698068973 / 1000000000) (27922759 / 40000000) (Real.log (251233481469 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (251233481469 / 125000000000) = -Real.log (125000000000 / 251233481469) := by
    rw [show ((251233481469 / 125000000000) : ℝ) = ((125000000000 / 251233481469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (499200809 / 1000000000) ≤ -Real.log (25000000000 / 41185103851) ∧
    -Real.log (25000000000 / 41185103851) ≤ (49920081 / 100000000) := by
  have h := checkLog_sound (w := (16185103851 / 66185103851)) (n := 12)
    (lo := (499200809 / 1000000000)) (hi := (49920081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41185103851 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41185103851 / 25000000000) = 1/(25000000000 / 41185103851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (499200809 / 1000000000) (49920081 / 100000000) (Real.log (41185103851 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (41185103851 / 25000000000) = -Real.log (25000000000 / 41185103851) := by
    rw [show ((41185103851 / 25000000000) : ℝ) = ((25000000000 / 41185103851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (249955679 / 500000000) ≤ -Real.log (500000000000 / 824287566397) ∧
    -Real.log (500000000000 / 824287566397) ≤ (499911359 / 1000000000) := by
  have h := checkLog_sound (w := (324287566397 / 1324287566397)) (n := 12)
    (lo := (249955679 / 500000000)) (hi := (499911359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824287566397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824287566397 / 500000000000) = 1/(500000000000 / 824287566397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (249955679 / 500000000) (499911359 / 1000000000) (Real.log (824287566397 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (824287566397 / 500000000000) = -Real.log (500000000000 / 824287566397) := by
    rw [show ((824287566397 / 500000000000) : ℝ) = ((500000000000 / 824287566397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0355

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0356Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0356
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

theorem reflection_log_1_neg : (26340373 / 125000000) ≤ -Real.log (5120 / 6321) ∧
    -Real.log (5120 / 6321) ≤ (42144597 / 200000000) := by
  have h := checkLog_sound (w := (1201 / 11441)) (n := 12)
    (lo := (26340373 / 125000000)) (hi := (42144597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6321 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6321 / 5120) = 1/(5120 / 6321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (26340373 / 125000000) (42144597 / 200000000) (Real.log (6321 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6321 / 5120) = -Real.log (5120 / 6321) := by
    rw [show ((6321 / 5120) : ℝ) = ((5120 / 6321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (267317919 / 1000000000) ≤ -Real.log (3919 / 5120) ∧
    -Real.log (3919 / 5120) ≤ (1670737 / 6250000) := by
  have h := checkLog_sound (w := (1201 / 9039)) (n := 12)
    (lo := (267317919 / 1000000000)) (hi := (1670737 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3919) = 1/(3919 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1670737 / 6250000) (-267317919 / 1000000000) (Real.log (3919 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (52621413 / 250000000) ≤ -Real.log (10240 / 12639) ∧
    -Real.log (10240 / 12639) ≤ (210485653 / 1000000000) := by
  have h := checkLog_sound (w := (2399 / 22879)) (n := 12)
    (lo := (52621413 / 250000000)) (hi := (210485653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12639 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12639 / 10240) = 1/(10240 / 12639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (52621413 / 250000000) (210485653 / 1000000000) (Real.log (12639 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12639 / 10240) = -Real.log (10240 / 12639) := by
    rw [show ((12639 / 10240) : ℝ) = ((10240 / 12639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (133467621 / 500000000) ≤ -Real.log (7841 / 10240) ∧
    -Real.log (7841 / 10240) ≤ (266935243 / 1000000000) := by
  have h := checkLog_sound (w := (2399 / 18081)) (n := 12)
    (lo := (133467621 / 500000000)) (hi := (266935243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7841) = 1/(7841 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-266935243 / 1000000000) (-133467621 / 500000000) (Real.log (7841 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19233881 / 50000000) ≤ -Real.log (2560 / 3761) ∧
    -Real.log (2560 / 3761) ≤ (384677621 / 1000000000) := by
  have h := checkLog_sound (w := (1201 / 6321)) (n := 12)
    (lo := (19233881 / 50000000)) (hi := (384677621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3761 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3761 / 2560) = 1/(2560 / 3761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19233881 / 50000000) (384677621 / 1000000000) (Real.log (3761 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3761 / 2560) = -Real.log (2560 / 3761) := by
    rw [show ((3761 / 2560) : ℝ) = ((2560 / 3761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (633258123 / 1000000000) ≤ -Real.log (1359 / 2560) ∧
    -Real.log (1359 / 2560) ≤ (158314531 / 250000000) := by
  have h := checkLog_sound (w := (1201 / 3919)) (n := 12)
    (lo := (633258123 / 1000000000)) (hi := (158314531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1359) = 1/(1359 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-158314531 / 250000000) (-633258123 / 1000000000) (Real.log (1359 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (384278711 / 1000000000) ≤ -Real.log (5120 / 7519) ∧
    -Real.log (5120 / 7519) ≤ (48034839 / 125000000) := by
  have h := checkLog_sound (w := (2399 / 12639)) (n := 12)
    (lo := (384278711 / 1000000000)) (hi := (48034839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7519 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7519 / 5120) = 1/(5120 / 7519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (384278711 / 1000000000) (48034839 / 125000000) (Real.log (7519 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7519 / 5120) = -Real.log (5120 / 7519) := by
    rw [show ((7519 / 5120) : ℝ) = ((5120 / 7519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (632154979 / 1000000000) ≤ -Real.log (2721 / 5120) ∧
    -Real.log (2721 / 5120) ≤ (31607749 / 50000000) := by
  have h := checkLog_sound (w := (2399 / 7841)) (n := 12)
    (lo := (632154979 / 1000000000)) (hi := (31607749 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2721) = 1/(2721 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-31607749 / 50000000) (-632154979 / 1000000000) (Real.log (2721 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (72169519 / 250000000) ≤ -Real.log (500000 / 667331) ∧
    -Real.log (500000 / 667331) ≤ (288678077 / 1000000000) := by
  have h := checkLog_sound (w := (167331 / 1167331)) (n := 12)
    (lo := (72169519 / 250000000)) (hi := (288678077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667331 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667331 / 500000) = 1/(500000 / 667331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (72169519 / 250000000) (288678077 / 1000000000) (Real.log (667331 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (667331 / 500000) = -Real.log (500000 / 667331) := by
    rw [show ((667331 / 500000) : ℝ) = ((500000 / 667331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1591641 / 3906250) ≤ -Real.log (332669 / 500000) ∧
    -Real.log (332669 / 500000) ≤ (407460097 / 1000000000) := by
  have h := checkLog_sound (w := (167331 / 832669)) (n := 12)
    (lo := (1591641 / 3906250)) (hi := (407460097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 332669) = 1/(332669 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-407460097 / 1000000000) (-1591641 / 3906250) (Real.log (332669 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (144499727 / 500000000) ≤ -Real.log (1000000 / 1335091) ∧
    -Real.log (1000000 / 1335091) ≤ (57799891 / 200000000) := by
  have h := checkLog_sound (w := (335091 / 2335091)) (n := 12)
    (lo := (144499727 / 500000000)) (hi := (57799891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1335091 / 1000000) = 1/(1000000 / 1335091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (144499727 / 500000000) (57799891 / 200000000) (Real.log (1335091 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1335091 / 1000000) = -Real.log (1000000 / 1335091) := by
    rw [show ((1335091 / 1000000) : ℝ) = ((1000000 / 1335091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (408105089 / 1000000000) ≤ -Real.log (664909 / 1000000) ∧
    -Real.log (664909 / 1000000) ≤ (40810509 / 100000000) := by
  have h := checkLog_sound (w := (335091 / 1664909)) (n := 12)
    (lo := (408105089 / 1000000000)) (hi := (40810509 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 664909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 664909) = 1/(664909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-40810509 / 100000000) (-408105089 / 1000000000) (Real.log (664909 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (109250797 / 500000000) ≤ -Real.log (1000000 / 1244211) ∧
    -Real.log (1000000 / 1244211) ≤ (43700319 / 200000000) := by
  have h := checkLog_sound (w := (244211 / 2244211)) (n := 12)
    (lo := (109250797 / 500000000)) (hi := (43700319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244211 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244211 / 1000000) = 1/(1000000 / 1244211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (109250797 / 500000000) (43700319 / 200000000) (Real.log (1244211 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1244211 / 1000000) = -Real.log (1000000 / 1244211) := by
    rw [show ((1244211 / 1000000) : ℝ) = ((1000000 / 1244211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (139996521 / 500000000) ≤ -Real.log (755789 / 1000000) ∧
    -Real.log (755789 / 1000000) ≤ (279993043 / 1000000000) := by
  have h := checkLog_sound (w := (244211 / 1755789)) (n := 12)
    (lo := (139996521 / 500000000)) (hi := (279993043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755789) = 1/(755789 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-279993043 / 1000000000) (-139996521 / 500000000) (Real.log (755789 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (218769197 / 1000000000) ≤ -Real.log (15625 / 19446) ∧
    -Real.log (15625 / 19446) ≤ (109384599 / 500000000) := by
  have h := checkLog_sound (w := (3821 / 35071)) (n := 12)
    (lo := (218769197 / 1000000000)) (hi := (109384599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19446 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19446 / 15625) = 1/(15625 / 19446) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (218769197 / 1000000000) (109384599 / 500000000) (Real.log (19446 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (19446 / 15625) = -Real.log (15625 / 19446) := by
    rw [show ((19446 / 15625) : ℝ) = ((15625 / 19446) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140216869 / 500000000) ≤ -Real.log (11804 / 15625) ∧
    -Real.log (11804 / 15625) ≤ (280433739 / 1000000000) := by
  have h := checkLog_sound (w := (3821 / 27429)) (n := 12)
    (lo := (140216869 / 500000000)) (hi := (280433739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11804) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11804) = 1/(11804 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-280433739 / 1000000000) (-140216869 / 500000000) (Real.log (11804 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (174034543 / 250000000) ≤ -Real.log (500000000000 / 1002995469971) ∧
    -Real.log (500000000000 / 1002995469971) ≤ (348069087 / 500000000) := by
  have h := checkLog_sound (w := (2995469971 / 2002995469971)) (n := 12)
    (lo := (186937 / 62500000)) (hi := (2990993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002995469971 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002995469971 / 1000000000000) = 1/(500000000000 / 1002995469971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (174034543 / 250000000) (348069087 / 500000000) (Real.log (1002995469971 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1002995469971 / 500000000000) = -Real.log (500000000000 / 1002995469971) := by
    rw [show ((1002995469971 / 500000000000) : ℝ) = ((500000000000 / 1002995469971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (697104543 / 1000000000) ≤ -Real.log (250000000000 / 501982602131) ∧
    -Real.log (250000000000 / 501982602131) ≤ (139420909 / 200000000) := by
  have h := checkLog_sound (w := (1982602131 / 1001982602131)) (n := 12)
    (lo := (3957363 / 1000000000)) (hi := (989341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((501982602131 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(501982602131 / 500000000000) = 1/(250000000000 / 501982602131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (697104543 / 1000000000) (139420909 / 200000000) (Real.log (501982602131 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (501982602131 / 250000000000) = -Real.log (250000000000 / 501982602131) := by
    rw [show ((501982602131 / 250000000000) : ℝ) = ((250000000000 / 501982602131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (124623659 / 250000000) ≤ -Real.log (125000000000 / 205780151603) ∧
    -Real.log (125000000000 / 205780151603) ≤ (498494637 / 1000000000) := by
  have h := checkLog_sound (w := (80780151603 / 330780151603)) (n := 12)
    (lo := (124623659 / 250000000)) (hi := (498494637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205780151603 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205780151603 / 125000000000) = 1/(125000000000 / 205780151603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (124623659 / 250000000) (498494637 / 1000000000) (Real.log (205780151603 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (205780151603 / 125000000000) = -Real.log (125000000000 / 205780151603) := by
    rw [show ((205780151603 / 125000000000) : ℝ) = ((125000000000 / 205780151603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (62400367 / 125000000) ≤ -Real.log (500000000000 / 823703829211) ∧
    -Real.log (500000000000 / 823703829211) ≤ (499202937 / 1000000000) := by
  have h := checkLog_sound (w := (323703829211 / 1323703829211)) (n := 12)
    (lo := (62400367 / 125000000)) (hi := (499202937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823703829211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823703829211 / 500000000000) = 1/(500000000000 / 823703829211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (62400367 / 125000000) (499202937 / 1000000000) (Real.log (823703829211 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (823703829211 / 500000000000) = -Real.log (500000000000 / 823703829211) := by
    rw [show ((823703829211 / 500000000000) : ℝ) = ((500000000000 / 823703829211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0356

end


