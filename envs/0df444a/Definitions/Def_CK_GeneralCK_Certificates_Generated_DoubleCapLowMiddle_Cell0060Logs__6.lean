-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0060Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0060Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:01:33.394369+00:00
-- url     : https://prove2.me/theorems/287a83ea-4f44-46ec-9b5b-a28f36dbbe6f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0060Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0061Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0060Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0061Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0062Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0063Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0064Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0060Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0061Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0062Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0063Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0064Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0060Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0061Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0062Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0063Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0064Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0060Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0061Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0062Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0063Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0064Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0065Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0060Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0060
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

theorem reflection_log_1_neg : (678117811 / 1000000000) ≤ -Real.log (20480 / 40349) ∧
    -Real.log (20480 / 40349) ≤ (169529453 / 250000000) := by
  have h := checkLog_sound (w := (19869 / 60829)) (n := 12)
    (lo := (678117811 / 1000000000)) (hi := (169529453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40349 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40349 / 20480) = 1/(20480 / 40349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678117811 / 1000000000) (169529453 / 250000000) (Real.log (40349 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40349 / 20480) = -Real.log (20480 / 40349) := by
    rw [show ((40349 / 20480) : ℝ) = ((20480 / 40349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3512107117 / 1000000000) ≤ -Real.log (611 / 20480) ∧
    -Real.log (611 / 20480) ≤ (3512107123 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 1251)) (n := 12)
    (lo := (46371217 / 1000000000)) (hi := (23185609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 611) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 611) = 1/(611 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3512107123 / 1000000000) (-3512107117 / 1000000000) (Real.log (611 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169505907 / 250000000) ≤ -Real.log (51200 / 100863) ∧
    -Real.log (51200 / 100863) ≤ (678023629 / 1000000000) := by
  have h := checkLog_sound (w := (49663 / 152063)) (n := 12)
    (lo := (169505907 / 250000000)) (hi := (678023629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100863 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100863 / 51200) = 1/(51200 / 100863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (169505907 / 250000000) (678023629 / 1000000000) (Real.log (100863 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100863 / 51200) = -Real.log (51200 / 100863) := by
    rw [show ((100863 / 51200) : ℝ) = ((51200 / 100863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (438238383 / 125000000) ≤ -Real.log (1537 / 51200) ∧
    -Real.log (1537 / 51200) ≤ (350590707 / 100000000) := by
  have h := checkLog_sound (w := (63 / 3137)) (n := 12)
    (lo := (10042791 / 250000000)) (hi := (8034233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1537) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1537) = 1/(1537 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-350590707 / 100000000) (-438238383 / 125000000) (Real.log (1537 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (165714777 / 250000000) ≤ -Real.log (10240 / 19869) ∧
    -Real.log (10240 / 19869) ≤ (662859109 / 1000000000) := by
  have h := checkLog_sound (w := (9629 / 30109)) (n := 12)
    (lo := (165714777 / 250000000)) (hi := (662859109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19869 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19869 / 10240) = 1/(10240 / 19869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (165714777 / 250000000) (662859109 / 1000000000) (Real.log (19869 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19869 / 10240) = -Real.log (10240 / 19869) := by
    rw [show ((19869 / 10240) : ℝ) = ((10240 / 19869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2818959937 / 1000000000) ≤ -Real.log (611 / 10240) ∧
    -Real.log (611 / 10240) ≤ (1409479971 / 500000000) := by
  have h := checkLog_sound (w := (29 / 1251)) (n := 12)
    (lo := (46371217 / 1000000000)) (hi := (23185609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 611) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 611) = 1/(611 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1409479971 / 500000000) (-2818959937 / 1000000000) (Real.log (611 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (662667837 / 1000000000) ≤ -Real.log (25600 / 49663) ∧
    -Real.log (25600 / 49663) ≤ (331333919 / 500000000) := by
  have h := checkLog_sound (w := (24063 / 75263)) (n := 12)
    (lo := (662667837 / 1000000000)) (hi := (331333919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49663 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49663 / 25600) = 1/(25600 / 49663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (662667837 / 1000000000) (331333919 / 500000000) (Real.log (49663 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49663 / 25600) = -Real.log (25600 / 49663) := by
    rw [show ((49663 / 25600) : ℝ) = ((25600 / 49663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (703189971 / 250000000) ≤ -Real.log (1537 / 25600) ∧
    -Real.log (1537 / 25600) ≤ (2812759889 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 3137)) (n := 12)
    (lo := (10042791 / 250000000)) (hi := (8034233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1537) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1537) = 1/(1537 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2812759889 / 1000000000) (-703189971 / 250000000) (Real.log (1537 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680519789 / 1000000000) ≤ -Real.log (125000 / 246863) ∧
    -Real.log (125000 / 246863) ≤ (68051979 / 100000000) := by
  have h := checkLog_sound (w := (121863 / 371863)) (n := 12)
    (lo := (680519789 / 1000000000)) (hi := (68051979 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246863 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246863 / 125000) = 1/(125000 / 246863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (680519789 / 1000000000) (68051979 / 100000000) (Real.log (246863 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (246863 / 125000) = -Real.log (125000 / 246863) := by
    rw [show ((246863 / 125000) : ℝ) = ((125000 / 246863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (737009361 / 200000000) ≤ -Real.log (3137 / 125000) ∧
    -Real.log (3137 / 125000) ≤ (3685046811 / 1000000000) := by
  have h := checkLog_sound (w := (3077 / 28173)) (n := 12)
    (lo := (43862181 / 200000000)) (hi := (109655453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12548) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12548) = 1/(3137 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3685046811 / 1000000000) (-737009361 / 200000000) (Real.log (3137 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680595233 / 1000000000) ≤ -Real.log (1000000 / 1975053) ∧
    -Real.log (1000000 / 1975053) ≤ (340297617 / 500000000) := by
  have h := checkLog_sound (w := (975053 / 2975053)) (n := 12)
    (lo := (680595233 / 1000000000)) (hi := (340297617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975053 / 1000000) = 1/(1000000 / 1975053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680595233 / 1000000000) (340297617 / 500000000) (Real.log (1975053 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975053 / 1000000) = -Real.log (1000000 / 1975053) := by
    rw [show ((1975053 / 1000000) : ℝ) = ((1000000 / 1975053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3691001701 / 1000000000) ≤ -Real.log (24947 / 1000000) ∧
    -Real.log (24947 / 1000000) ≤ (3691001707 / 1000000000) := by
  have h := checkLog_sound (w := (6303 / 56197)) (n := 12)
    (lo := (225265801 / 1000000000)) (hi := (112632901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24947) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24947) = 1/(24947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3691001707 / 1000000000) (-3691001701 / 1000000000) (Real.log (24947 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (34022141 / 50000000) ≤ -Real.log (31250 / 61711) ∧
    -Real.log (31250 / 61711) ≤ (680442821 / 1000000000) := by
  have h := checkLog_sound (w := (30461 / 92961)) (n := 12)
    (lo := (34022141 / 50000000)) (hi := (680442821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61711 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61711 / 31250) = 1/(31250 / 61711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (34022141 / 50000000) (680442821 / 1000000000) (Real.log (61711 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61711 / 31250) = -Real.log (31250 / 61711) := by
    rw [show ((61711 / 31250) : ℝ) = ((31250 / 61711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3679008331 / 1000000000) ≤ -Real.log (789 / 31250) ∧
    -Real.log (789 / 31250) ≤ (3679008337 / 1000000000) := by
  have h := checkLog_sound (w := (3001 / 28249)) (n := 12)
    (lo := (213272431 / 1000000000)) (hi := (13329527 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12624) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12624) = 1/(789 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3679008337 / 1000000000) (-3679008331 / 1000000000) (Real.log (789 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680519283 / 1000000000) ≤ -Real.log (1000000 / 1974903) ∧
    -Real.log (1000000 / 1974903) ≤ (170129821 / 250000000) := by
  have h := checkLog_sound (w := (974903 / 2974903)) (n := 12)
    (lo := (680519283 / 1000000000)) (hi := (170129821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974903 / 1000000) = 1/(1000000 / 1974903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680519283 / 1000000000) (170129821 / 250000000) (Real.log (1974903 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1974903 / 1000000) = -Real.log (1000000 / 1974903) := by
    rw [show ((1974903 / 1000000) : ℝ) = ((1000000 / 1974903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3685006959 / 1000000000) ≤ -Real.log (25097 / 1000000) ∧
    -Real.log (25097 / 1000000) ≤ (737001393 / 200000000) := by
  have h := checkLog_sound (w := (6153 / 56347)) (n := 12)
    (lo := (219271059 / 1000000000)) (hi := (10963553 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25097) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25097) = 1/(25097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-737001393 / 200000000) (-3685006959 / 1000000000) (Real.log (25097 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2182783297 / 500000000) ≤ -Real.log (500000000000 / 39346987567739) ∧
    -Real.log (500000000000 / 39346987567739) ≤ (4365566601 / 1000000000) := by
  have h := checkLog_sound (w := (7346987567739 / 71346987567739)) (n := 12)
    (lo := (103341757 / 500000000)) (hi := (41336703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39346987567739 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39346987567739 / 32000000000000) = 1/(500000000000 / 39346987567739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2182783297 / 500000000) (4365566601 / 1000000000) (Real.log (39346987567739 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (39346987567739 / 500000000000) = -Real.log (500000000000 / 39346987567739) := by
    rw [show ((39346987567739 / 500000000000) : ℝ) = ((500000000000 / 39346987567739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2185798467 / 500000000) ≤ -Real.log (100000000000 / 7916996031587) ∧
    -Real.log (100000000000 / 7916996031587) ≤ (4371596941 / 1000000000) := by
  have h := checkLog_sound (w := (1516996031587 / 14316996031587)) (n := 12)
    (lo := (106356927 / 500000000)) (hi := (42542771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7916996031587 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7916996031587 / 6400000000000) = 1/(100000000000 / 7916996031587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2185798467 / 500000000) (4371596941 / 1000000000) (Real.log (7916996031587 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7916996031587 / 100000000000) = -Real.log (100000000000 / 7916996031587) := by
    rw [show ((7916996031587 / 100000000000) : ℝ) = ((100000000000 / 7916996031587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4359451151 / 1000000000) ≤ -Real.log (31250000000 / 2444193599493) ∧
    -Real.log (31250000000 / 2444193599493) ≤ (2179725579 / 500000000) := by
  have h := checkLog_sound (w := (444193599493 / 4444193599493)) (n := 12)
    (lo := (200568071 / 1000000000)) (hi := (25071009 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2444193599493 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2444193599493 / 2000000000000) = 1/(31250000000 / 2444193599493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4359451151 / 1000000000) (2179725579 / 500000000) (Real.log (2444193599493 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2444193599493 / 31250000000) = -Real.log (31250000000 / 2444193599493) := by
    rw [show ((2444193599493 / 31250000000) : ℝ) = ((31250000000 / 2444193599493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4365526241 / 1000000000) ≤ -Real.log (125000000000 / 9836349962147) ∧
    -Real.log (125000000000 / 9836349962147) ≤ (545690781 / 125000000) := by
  have h := checkLog_sound (w := (1836349962147 / 17836349962147)) (n := 12)
    (lo := (206643161 / 1000000000)) (hi := (103321581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9836349962147 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9836349962147 / 8000000000000) = 1/(125000000000 / 9836349962147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4365526241 / 1000000000) (545690781 / 125000000) (Real.log (9836349962147 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9836349962147 / 125000000000) = -Real.log (125000000000 / 9836349962147) := by
    rw [show ((9836349962147 / 125000000000) : ℝ) = ((125000000000 / 9836349962147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0060

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0061Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0061
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

theorem reflection_log_1_neg : (169505907 / 250000000) ≤ -Real.log (51200 / 100863) ∧
    -Real.log (51200 / 100863) ≤ (678023629 / 1000000000) := by
  have h := checkLog_sound (w := (49663 / 152063)) (n := 12)
    (lo := (169505907 / 250000000)) (hi := (678023629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100863 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100863 / 51200) = 1/(51200 / 100863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169505907 / 250000000) (678023629 / 1000000000) (Real.log (100863 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100863 / 51200) = -Real.log (51200 / 100863) := by
    rw [show ((100863 / 51200) : ℝ) = ((51200 / 100863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (438238383 / 125000000) ≤ -Real.log (1537 / 51200) ∧
    -Real.log (1537 / 51200) ≤ (350590707 / 100000000) := by
  have h := checkLog_sound (w := (63 / 3137)) (n := 12)
    (lo := (10042791 / 250000000)) (hi := (8034233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1537) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1537) = 1/(1537 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-350590707 / 100000000) (-438238383 / 125000000) (Real.log (1537 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169482359 / 250000000) ≤ -Real.log (102400 / 201707) ∧
    -Real.log (102400 / 201707) ≤ (677929437 / 1000000000) := by
  have h := checkLog_sound (w := (99307 / 304107)) (n := 12)
    (lo := (169482359 / 250000000)) (hi := (677929437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201707 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201707 / 102400) = 1/(102400 / 201707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (169482359 / 250000000) (677929437 / 1000000000) (Real.log (201707 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201707 / 102400) = -Real.log (102400 / 201707) := by
    rw [show ((201707 / 102400) : ℝ) = ((102400 / 201707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (54683519 / 15625000) ≤ -Real.log (3093 / 102400) ∧
    -Real.log (3093 / 102400) ≤ (1749872611 / 500000000) := by
  have h := checkLog_sound (w := (107 / 6293)) (n := 12)
    (lo := (8502329 / 250000000)) (hi := (34009317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3093) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3093) = 1/(3093 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1749872611 / 500000000) (-54683519 / 15625000) (Real.log (3093 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (662667837 / 1000000000) ≤ -Real.log (25600 / 49663) ∧
    -Real.log (25600 / 49663) ≤ (331333919 / 500000000) := by
  have h := checkLog_sound (w := (24063 / 75263)) (n := 12)
    (lo := (662667837 / 1000000000)) (hi := (331333919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49663 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49663 / 25600) = 1/(25600 / 49663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (662667837 / 1000000000) (331333919 / 500000000) (Real.log (49663 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49663 / 25600) = -Real.log (25600 / 49663) := by
    rw [show ((49663 / 25600) : ℝ) = ((25600 / 49663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (703189971 / 250000000) ≤ -Real.log (1537 / 25600) ∧
    -Real.log (1537 / 25600) ≤ (2812759889 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 3137)) (n := 12)
    (lo := (10042791 / 250000000)) (hi := (8034233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1537) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1537) = 1/(1537 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2812759889 / 1000000000) (-703189971 / 250000000) (Real.log (1537 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (662476529 / 1000000000) ≤ -Real.log (51200 / 99307) ∧
    -Real.log (51200 / 99307) ≤ (66247653 / 100000000) := by
  have h := checkLog_sound (w := (48107 / 150507)) (n := 12)
    (lo := (662476529 / 1000000000)) (hi := (66247653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99307 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99307 / 51200) = 1/(51200 / 99307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (662476529 / 1000000000) (66247653 / 100000000) (Real.log (99307 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99307 / 51200) = -Real.log (51200 / 99307) := by
    rw [show ((99307 / 51200) : ℝ) = ((51200 / 99307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (701649509 / 250000000) ≤ -Real.log (3093 / 51200) ∧
    -Real.log (3093 / 51200) ≤ (2806598041 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 6293)) (n := 12)
    (lo := (8502329 / 250000000)) (hi := (34009317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3093) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3093) = 1/(3093 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2806598041 / 1000000000) (-701649509 / 250000000) (Real.log (3093 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85055669 / 125000000) ≤ -Real.log (1000000 / 1974757) ∧
    -Real.log (1000000 / 1974757) ≤ (680445353 / 1000000000) := by
  have h := checkLog_sound (w := (974757 / 2974757)) (n := 12)
    (lo := (85055669 / 125000000)) (hi := (680445353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974757 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974757 / 1000000) = 1/(1000000 / 1974757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85055669 / 125000000) (680445353 / 1000000000) (Real.log (1974757 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1974757 / 1000000) = -Real.log (1000000 / 1974757) := by
    rw [show ((1974757 / 1000000) : ℝ) = ((1000000 / 1974757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1839603193 / 500000000) ≤ -Real.log (25243 / 1000000) ∧
    -Real.log (25243 / 1000000) ≤ (459900799 / 125000000) := by
  have h := checkLog_sound (w := (6007 / 56493)) (n := 12)
    (lo := (106735243 / 500000000)) (hi := (213470487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25243) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25243) = 1/(25243 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-459900799 / 125000000) (-1839603193 / 500000000) (Real.log (25243 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136104059 / 200000000) ≤ -Real.log (200000 / 394981) ∧
    -Real.log (200000 / 394981) ≤ (85065037 / 125000000) := by
  have h := checkLog_sound (w := (194981 / 594981)) (n := 12)
    (lo := (136104059 / 200000000)) (hi := (85065037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394981 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394981 / 200000) = 1/(200000 / 394981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136104059 / 200000000) (85065037 / 125000000) (Real.log (394981 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (394981 / 200000) = -Real.log (200000 / 394981) := by
    rw [show ((394981 / 200000) : ℝ) = ((200000 / 394981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3685086653 / 1000000000) ≤ -Real.log (5019 / 200000) ∧
    -Real.log (5019 / 200000) ≤ (3685086659 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 11269)) (n := 12)
    (lo := (219350753 / 1000000000)) (hi := (109675377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5019) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5019) = 1/(5019 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3685086659 / 1000000000) (-3685086653 / 1000000000) (Real.log (5019 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680366859 / 1000000000) ≤ -Real.log (500000 / 987301) ∧
    -Real.log (500000 / 987301) ≤ (34018343 / 50000000) := by
  have h := checkLog_sound (w := (487301 / 1487301)) (n := 12)
    (lo := (680366859 / 1000000000)) (hi := (34018343 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987301 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987301 / 500000) = 1/(500000 / 987301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680366859 / 1000000000) (34018343 / 50000000) (Real.log (987301 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987301 / 500000) = -Real.log (500000 / 987301) := by
    rw [show ((987301 / 500000) : ℝ) = ((500000 / 987301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (734616969 / 200000000) ≤ -Real.log (12699 / 500000) ∧
    -Real.log (12699 / 500000) ≤ (3673084851 / 1000000000) := by
  have h := checkLog_sound (w := (1463 / 14162)) (n := 12)
    (lo := (41469789 / 200000000)) (hi := (103674473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12699) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12699) = 1/(12699 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3673084851 / 1000000000) (-734616969 / 200000000) (Real.log (12699 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680443327 / 1000000000) ≤ -Real.log (1000000 / 1974753) ∧
    -Real.log (1000000 / 1974753) ≤ (10631927 / 15625000) := by
  have h := checkLog_sound (w := (974753 / 2974753)) (n := 12)
    (lo := (680443327 / 1000000000)) (hi := (10631927 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974753 / 1000000) = 1/(1000000 / 1974753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680443327 / 1000000000) (10631927 / 15625000) (Real.log (1974753 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1974753 / 1000000) = -Real.log (1000000 / 1974753) := by
    rw [show ((1974753 / 1000000) : ℝ) = ((1000000 / 1974753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3679047939 / 1000000000) ≤ -Real.log (25247 / 1000000) ∧
    -Real.log (25247 / 1000000) ≤ (735809589 / 200000000) := by
  have h := checkLog_sound (w := (6003 / 56497)) (n := 12)
    (lo := (213312039 / 1000000000)) (hi := (5332801 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25247) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25247) = 1/(25247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-735809589 / 200000000) (-3679047939 / 1000000000) (Real.log (25247 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2179825869 / 500000000) ≤ -Real.log (500000000000 / 39114942756407) ∧
    -Real.log (500000000000 / 39114942756407) ≤ (871930349 / 200000000) := by
  have h := checkLog_sound (w := (7114942756407 / 71114942756407)) (n := 12)
    (lo := (100384329 / 500000000)) (hi := (200768659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39114942756407 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39114942756407 / 32000000000000) = 1/(500000000000 / 39114942756407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2179825869 / 500000000) (871930349 / 200000000) (Real.log (39114942756407 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (39114942756407 / 500000000000) = -Real.log (500000000000 / 39114942756407) := by
    rw [show ((39114942756407 / 500000000000) : ℝ) = ((500000000000 / 39114942756407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1091401737 / 250000000) ≤ -Real.log (500000000000 / 39348575413429) ∧
    -Real.log (500000000000 / 39348575413429) ≤ (873121391 / 200000000) := by
  have h := checkLog_sound (w := (7348575413429 / 71348575413429)) (n := 12)
    (lo := (51680967 / 250000000)) (hi := (206723869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39348575413429 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39348575413429 / 32000000000000) = 1/(500000000000 / 39348575413429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1091401737 / 250000000) (873121391 / 200000000) (Real.log (39348575413429 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (39348575413429 / 500000000000) = -Real.log (500000000000 / 39348575413429) := by
    rw [show ((39348575413429 / 500000000000) : ℝ) = ((500000000000 / 39348575413429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4353451703 / 1000000000) ≤ -Real.log (500000000000 / 38873178990471) ∧
    -Real.log (500000000000 / 38873178990471) ≤ (435345171 / 100000000) := by
  have h := checkLog_sound (w := (6873178990471 / 70873178990471)) (n := 12)
    (lo := (194568623 / 1000000000)) (hi := (12160539 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38873178990471 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38873178990471 / 32000000000000) = 1/(500000000000 / 38873178990471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4353451703 / 1000000000) (435345171 / 100000000) (Real.log (38873178990471 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (38873178990471 / 500000000000) = -Real.log (500000000000 / 38873178990471) := by
    rw [show ((38873178990471 / 500000000000) : ℝ) = ((500000000000 / 38873178990471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2179745633 / 500000000) ≤ -Real.log (125000000000 / 9777166594051) ∧
    -Real.log (125000000000 / 9777166594051) ≤ (4359491273 / 1000000000) := by
  have h := checkLog_sound (w := (1777166594051 / 17777166594051)) (n := 12)
    (lo := (100304093 / 500000000)) (hi := (200608187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9777166594051 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9777166594051 / 8000000000000) = 1/(125000000000 / 9777166594051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2179745633 / 500000000) (4359491273 / 1000000000) (Real.log (9777166594051 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9777166594051 / 125000000000) = -Real.log (125000000000 / 9777166594051) := by
    rw [show ((9777166594051 / 125000000000) : ℝ) = ((125000000000 / 9777166594051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0061

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0062Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0062
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

theorem reflection_log_1_neg : (169482359 / 250000000) ≤ -Real.log (102400 / 201707) ∧
    -Real.log (102400 / 201707) ≤ (677929437 / 1000000000) := by
  have h := checkLog_sound (w := (99307 / 304107)) (n := 12)
    (lo := (169482359 / 250000000)) (hi := (677929437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201707 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201707 / 102400) = 1/(102400 / 201707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169482359 / 250000000) (677929437 / 1000000000) (Real.log (201707 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201707 / 102400) = -Real.log (102400 / 201707) := by
    rw [show ((201707 / 102400) : ℝ) = ((102400 / 201707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (54683519 / 15625000) ≤ -Real.log (3093 / 102400) ∧
    -Real.log (3093 / 102400) ≤ (1749872611 / 500000000) := by
  have h := checkLog_sound (w := (107 / 6293)) (n := 12)
    (lo := (8502329 / 250000000)) (hi := (34009317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3093) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3093) = 1/(3093 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1749872611 / 500000000) (-54683519 / 15625000) (Real.log (3093 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169458809 / 250000000) ≤ -Real.log (12800 / 25211) ∧
    -Real.log (12800 / 25211) ≤ (677835237 / 1000000000) := by
  have h := checkLog_sound (w := (12411 / 38011)) (n := 12)
    (lo := (169458809 / 250000000)) (hi := (677835237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25211 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25211 / 12800) = 1/(12800 / 25211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (169458809 / 250000000) (677835237 / 1000000000) (Real.log (25211 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25211 / 12800) = -Real.log (12800 / 25211) := by
    rw [show ((25211 / 12800) : ℝ) = ((12800 / 25211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3493621103 / 1000000000) ≤ -Real.log (389 / 12800) ∧
    -Real.log (389 / 12800) ≤ (3493621109 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 789)) (n := 12)
    (lo := (27885203 / 1000000000)) (hi := (6971301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 389) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 389) = 1/(389 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3493621109 / 1000000000) (-3493621103 / 1000000000) (Real.log (389 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (662476529 / 1000000000) ≤ -Real.log (51200 / 99307) ∧
    -Real.log (51200 / 99307) ≤ (66247653 / 100000000) := by
  have h := checkLog_sound (w := (48107 / 150507)) (n := 12)
    (lo := (662476529 / 1000000000)) (hi := (66247653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99307 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99307 / 51200) = 1/(51200 / 99307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (662476529 / 1000000000) (66247653 / 100000000) (Real.log (99307 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99307 / 51200) = -Real.log (51200 / 99307) := by
    rw [show ((99307 / 51200) : ℝ) = ((51200 / 99307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (701649509 / 250000000) ≤ -Real.log (3093 / 51200) ∧
    -Real.log (3093 / 51200) ≤ (2806598041 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 6293)) (n := 12)
    (lo := (8502329 / 250000000)) (hi := (34009317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3093) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3093) = 1/(3093 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2806598041 / 1000000000) (-701649509 / 250000000) (Real.log (3093 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (132457037 / 200000000) ≤ -Real.log (6400 / 12411) ∧
    -Real.log (6400 / 12411) ≤ (331142593 / 500000000) := by
  have h := checkLog_sound (w := (6011 / 18811)) (n := 12)
    (lo := (132457037 / 200000000)) (hi := (331142593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12411 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12411 / 6400) = 1/(6400 / 12411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (132457037 / 200000000) (331142593 / 500000000) (Real.log (12411 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12411 / 6400) = -Real.log (6400 / 12411) := by
    rw [show ((12411 / 6400) : ℝ) = ((6400 / 12411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2800473923 / 1000000000) ≤ -Real.log (389 / 6400) ∧
    -Real.log (389 / 6400) ≤ (350059241 / 125000000) := by
  have h := checkLog_sound (w := (11 / 789)) (n := 12)
    (lo := (27885203 / 1000000000)) (hi := (6971301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 389) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 389) = 1/(389 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-350059241 / 125000000) (-2800473923 / 1000000000) (Real.log (389 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170092601 / 250000000) ≤ -Real.log (1000000 / 1974609) ∧
    -Real.log (1000000 / 1974609) ≤ (136074081 / 200000000) := by
  have h := checkLog_sound (w := (974609 / 2974609)) (n := 12)
    (lo := (170092601 / 250000000)) (hi := (136074081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974609 / 1000000) = 1/(1000000 / 1974609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170092601 / 250000000) (136074081 / 200000000) (Real.log (1974609 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1974609 / 1000000) = -Real.log (1000000 / 1974609) := by
    rw [show ((1974609 / 1000000) : ℝ) = ((1000000 / 1974609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (734672099 / 200000000) ≤ -Real.log (25391 / 1000000) ∧
    -Real.log (25391 / 1000000) ≤ (3673360501 / 1000000000) := by
  have h := checkLog_sound (w := (5859 / 56641)) (n := 12)
    (lo := (41524919 / 200000000)) (hi := (51906149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25391) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25391) = 1/(25391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3673360501 / 1000000000) (-734672099 / 200000000) (Real.log (25391 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680445859 / 1000000000) ≤ -Real.log (500000 / 987379) ∧
    -Real.log (500000 / 987379) ≤ (34022293 / 50000000) := by
  have h := checkLog_sound (w := (487379 / 1487379)) (n := 12)
    (lo := (680445859 / 1000000000)) (hi := (34022293 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987379 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987379 / 500000) = 1/(500000 / 987379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680445859 / 1000000000) (34022293 / 50000000) (Real.log (987379 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (987379 / 500000) = -Real.log (500000 / 987379) := by
    rw [show ((987379 / 500000) : ℝ) = ((500000 / 987379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1839623001 / 500000000) ≤ -Real.log (12621 / 500000) ∧
    -Real.log (12621 / 500000) ≤ (459905751 / 125000000) := by
  have h := checkLog_sound (w := (1502 / 14123)) (n := 12)
    (lo := (106755051 / 500000000)) (hi := (213510103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12621) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12621) = 1/(12621 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-459905751 / 125000000) (-1839623001 / 500000000) (Real.log (12621 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680291397 / 1000000000) ≤ -Real.log (1000000 / 1974453) ∧
    -Real.log (1000000 / 1974453) ≤ (340145699 / 500000000) := by
  have h := checkLog_sound (w := (974453 / 2974453)) (n := 12)
    (lo := (680291397 / 1000000000)) (hi := (340145699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974453 / 1000000) = 1/(1000000 / 1974453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680291397 / 1000000000) (340145699 / 500000000) (Real.log (1974453 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1974453 / 1000000) = -Real.log (1000000 / 1974453) := by
    rw [show ((1974453 / 1000000) : ℝ) = ((1000000 / 1974453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3667235383 / 1000000000) ≤ -Real.log (25547 / 1000000) ∧
    -Real.log (25547 / 1000000) ≤ (3667235389 / 1000000000) := by
  have h := checkLog_sound (w := (5703 / 56797)) (n := 12)
    (lo := (201499483 / 1000000000)) (hi := (50374871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25547) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25547) = 1/(25547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3667235389 / 1000000000) (-3667235383 / 1000000000) (Real.log (25547 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136073473 / 200000000) ≤ -Real.log (1000000 / 1974603) ∧
    -Real.log (1000000 / 1974603) ≤ (340183683 / 500000000) := by
  have h := checkLog_sound (w := (974603 / 2974603)) (n := 12)
    (lo := (136073473 / 200000000)) (hi := (340183683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974603 / 1000000) = 1/(1000000 / 1974603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136073473 / 200000000) (340183683 / 500000000) (Real.log (1974603 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1974603 / 1000000) = -Real.log (1000000 / 1974603) := by
    rw [show ((1974603 / 1000000) : ℝ) = ((1000000 / 1974603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3673124219 / 1000000000) ≤ -Real.log (25397 / 1000000) ∧
    -Real.log (25397 / 1000000) ≤ (146924969 / 40000000) := by
  have h := checkLog_sound (w := (5853 / 56647)) (n := 12)
    (lo := (207388319 / 1000000000)) (hi := (1296177 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25397) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25397) = 1/(25397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-146924969 / 40000000) (-3673124219 / 1000000000) (Real.log (25397 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4353730899 / 1000000000) ≤ -Real.log (125000000000 / 9721008428183) ∧
    -Real.log (125000000000 / 9721008428183) ≤ (2176865453 / 500000000) := by
  have h := checkLog_sound (w := (1721008428183 / 17721008428183)) (n := 12)
    (lo := (194847819 / 1000000000)) (hi := (9742391 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9721008428183 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9721008428183 / 8000000000000) = 1/(125000000000 / 9721008428183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4353730899 / 1000000000) (2176865453 / 500000000) (Real.log (9721008428183 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9721008428183 / 125000000000) = -Real.log (125000000000 / 9721008428183) := by
    rw [show ((9721008428183 / 125000000000) : ℝ) = ((125000000000 / 9721008428183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (217984593 / 50000000) ≤ -Real.log (50000000000 / 3911651216227) ∧
    -Real.log (50000000000 / 3911651216227) ≤ (4359691867 / 1000000000) := by
  have h := checkLog_sound (w := (711651216227 / 7111651216227)) (n := 12)
    (lo := (10040439 / 50000000)) (hi := (200808781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3911651216227 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3911651216227 / 3200000000000) = 1/(50000000000 / 3911651216227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (217984593 / 50000000) (4359691867 / 1000000000) (Real.log (3911651216227 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3911651216227 / 50000000000) = -Real.log (50000000000 / 3911651216227) := by
    rw [show ((3911651216227 / 50000000000) : ℝ) = ((50000000000 / 3911651216227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (217376339 / 50000000) ≤ -Real.log (125000000000 / 9660884839707) ∧
    -Real.log (125000000000 / 9660884839707) ≤ (4347526787 / 1000000000) := by
  have h := checkLog_sound (w := (1660884839707 / 17660884839707)) (n := 12)
    (lo := (1886437 / 10000000)) (hi := (188643701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9660884839707 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9660884839707 / 8000000000000) = 1/(125000000000 / 9660884839707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (217376339 / 50000000) (4347526787 / 1000000000) (Real.log (9660884839707 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9660884839707 / 125000000000) = -Real.log (125000000000 / 9660884839707) := by
    rw [show ((9660884839707 / 125000000000) : ℝ) = ((125000000000 / 9660884839707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (34011653 / 7812500) ≤ -Real.log (500000000000 / 38874729298737) ∧
    -Real.log (500000000000 / 38874729298737) ≤ (4353491591 / 1000000000) := by
  have h := checkLog_sound (w := (6874729298737 / 70874729298737)) (n := 12)
    (lo := (24326063 / 125000000)) (hi := (38921701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38874729298737 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38874729298737 / 32000000000000) = 1/(500000000000 / 38874729298737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (34011653 / 7812500) (4353491591 / 1000000000) (Real.log (38874729298737 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (38874729298737 / 500000000000) = -Real.log (500000000000 / 38874729298737) := by
    rw [show ((38874729298737 / 500000000000) : ℝ) = ((500000000000 / 38874729298737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0062

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0063Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0063
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

theorem reflection_log_1_neg : (169458809 / 250000000) ≤ -Real.log (12800 / 25211) ∧
    -Real.log (12800 / 25211) ≤ (677835237 / 1000000000) := by
  have h := checkLog_sound (w := (12411 / 38011)) (n := 12)
    (lo := (169458809 / 250000000)) (hi := (677835237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25211 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25211 / 12800) = 1/(12800 / 25211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169458809 / 250000000) (677835237 / 1000000000) (Real.log (25211 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25211 / 12800) = -Real.log (12800 / 25211) := by
    rw [show ((25211 / 12800) : ℝ) = ((12800 / 25211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3493621103 / 1000000000) ≤ -Real.log (389 / 12800) ∧
    -Real.log (389 / 12800) ≤ (3493621109 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 789)) (n := 12)
    (lo := (27885203 / 1000000000)) (hi := (6971301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 389) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 389) = 1/(389 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3493621109 / 1000000000) (-3493621103 / 1000000000) (Real.log (389 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (338870513 / 500000000) ≤ -Real.log (102400 / 201669) ∧
    -Real.log (102400 / 201669) ≤ (677741027 / 1000000000) := by
  have h := checkLog_sound (w := (99269 / 304069)) (n := 12)
    (lo := (338870513 / 500000000)) (hi := (677741027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201669 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201669 / 102400) = 1/(102400 / 201669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (338870513 / 500000000) (677741027 / 1000000000) (Real.log (201669 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201669 / 102400) = -Real.log (102400 / 201669) := by
    rw [show ((201669 / 102400) : ℝ) = ((102400 / 201669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3487534267 / 1000000000) ≤ -Real.log (3131 / 102400) ∧
    -Real.log (3131 / 102400) ≤ (3487534273 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 6331)) (n := 12)
    (lo := (21798367 / 1000000000)) (hi := (681199 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3131) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3131) = 1/(3131 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3487534273 / 1000000000) (-3487534267 / 1000000000) (Real.log (3131 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (132457037 / 200000000) ≤ -Real.log (6400 / 12411) ∧
    -Real.log (6400 / 12411) ≤ (331142593 / 500000000) := by
  have h := checkLog_sound (w := (6011 / 18811)) (n := 12)
    (lo := (132457037 / 200000000)) (hi := (331142593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12411 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12411 / 6400) = 1/(6400 / 12411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (132457037 / 200000000) (331142593 / 500000000) (Real.log (12411 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12411 / 6400) = -Real.log (6400 / 12411) := by
    rw [show ((12411 / 6400) : ℝ) = ((6400 / 12411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2800473923 / 1000000000) ≤ -Real.log (389 / 6400) ∧
    -Real.log (389 / 6400) ≤ (350059241 / 125000000) := by
  have h := checkLog_sound (w := (11 / 789)) (n := 12)
    (lo := (27885203 / 1000000000)) (hi := (6971301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 389) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 389) = 1/(389 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-350059241 / 125000000) (-2800473923 / 1000000000) (Real.log (389 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (165523451 / 250000000) ≤ -Real.log (51200 / 99269) ∧
    -Real.log (51200 / 99269) ≤ (132418761 / 200000000) := by
  have h := checkLog_sound (w := (48069 / 150469)) (n := 12)
    (lo := (165523451 / 250000000)) (hi := (132418761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99269 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99269 / 51200) = 1/(51200 / 99269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (165523451 / 250000000) (132418761 / 200000000) (Real.log (99269 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99269 / 51200) = -Real.log (51200 / 99269) := by
    rw [show ((99269 / 51200) : ℝ) = ((51200 / 99269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2794387087 / 1000000000) ≤ -Real.log (3131 / 51200) ∧
    -Real.log (3131 / 51200) ≤ (698596773 / 250000000) := by
  have h := checkLog_sound (w := (69 / 6331)) (n := 12)
    (lo := (21798367 / 1000000000)) (hi := (681199 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3131) = 1/(3131 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-698596773 / 250000000) (-2794387087 / 1000000000) (Real.log (3131 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680295449 / 1000000000) ≤ -Real.log (1000000 / 1974461) ∧
    -Real.log (1000000 / 1974461) ≤ (13605909 / 20000000) := by
  have h := checkLog_sound (w := (974461 / 2974461)) (n := 12)
    (lo := (680295449 / 1000000000)) (hi := (13605909 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974461 / 1000000) = 1/(1000000 / 1974461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (680295449 / 1000000000) (13605909 / 20000000) (Real.log (1974461 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1974461 / 1000000) = -Real.log (1000000 / 1974461) := by
    rw [show ((1974461 / 1000000) : ℝ) = ((1000000 / 1974461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (183377429 / 50000000) ≤ -Real.log (25539 / 1000000) ∧
    -Real.log (25539 / 1000000) ≤ (1833774293 / 500000000) := by
  have h := checkLog_sound (w := (5711 / 56789)) (n := 12)
    (lo := (5045317 / 25000000)) (hi := (201812681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25539) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25539) = 1/(25539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1833774293 / 500000000) (-183377429 / 50000000) (Real.log (25539 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68037091 / 100000000) ≤ -Real.log (100000 / 197461) ∧
    -Real.log (100000 / 197461) ≤ (680370911 / 1000000000) := by
  have h := checkLog_sound (w := (97461 / 297461)) (n := 12)
    (lo := (68037091 / 100000000)) (hi := (680370911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197461 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197461 / 100000) = 1/(100000 / 197461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68037091 / 100000000) (680370911 / 1000000000) (Real.log (197461 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (197461 / 100000) = -Real.log (100000 / 197461) := by
    rw [show ((197461 / 100000) : ℝ) = ((100000 / 197461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (91834997 / 25000000) ≤ -Real.log (2539 / 100000) ∧
    -Real.log (2539 / 100000) ≤ (1836699943 / 500000000) := by
  have h := checkLog_sound (w := (293 / 2832)) (n := 12)
    (lo := (10383199 / 50000000)) (hi := (207663981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2539) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2539) = 1/(2539 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1836699943 / 500000000) (-91834997 / 25000000) (Real.log (2539 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5314183 / 7812500) ≤ -Real.log (1000000 / 1974303) ∧
    -Real.log (1000000 / 1974303) ≤ (27208617 / 40000000) := by
  have h := checkLog_sound (w := (974303 / 2974303)) (n := 12)
    (lo := (5314183 / 7812500)) (hi := (27208617 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974303 / 1000000) = 1/(1000000 / 1974303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5314183 / 7812500) (27208617 / 40000000) (Real.log (1974303 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1974303 / 1000000) = -Real.log (1000000 / 1974303) := by
    rw [show ((1974303 / 1000000) : ℝ) = ((1000000 / 1974303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1830690511 / 500000000) ≤ -Real.log (25697 / 1000000) ∧
    -Real.log (25697 / 1000000) ≤ (915345257 / 250000000) := by
  have h := checkLog_sound (w := (5553 / 56947)) (n := 12)
    (lo := (97822561 / 500000000)) (hi := (195645123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25697) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25697) = 1/(25697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-915345257 / 250000000) (-1830690511 / 500000000) (Real.log (25697 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10629561 / 15625000) ≤ -Real.log (500000 / 987227) ∧
    -Real.log (500000 / 987227) ≤ (136058381 / 200000000) := by
  have h := checkLog_sound (w := (487227 / 1487227)) (n := 12)
    (lo := (10629561 / 15625000)) (hi := (136058381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987227 / 500000) = 1/(500000 / 987227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10629561 / 15625000) (136058381 / 200000000) (Real.log (987227 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (987227 / 500000) = -Real.log (500000 / 987227) := by
    rw [show ((987227 / 500000) : ℝ) = ((500000 / 987227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3667274527 / 1000000000) ≤ -Real.log (12773 / 500000) ∧
    -Real.log (12773 / 500000) ≤ (3667274533 / 1000000000) := by
  have h := checkLog_sound (w := (1426 / 14199)) (n := 12)
    (lo := (201538627 / 1000000000)) (hi := (50384657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12773) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12773) = 1/(12773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3667274533 / 1000000000) (-3667274527 / 1000000000) (Real.log (12773 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4347844029 / 1000000000) ≤ -Real.log (125000000000 / 9663950232977) ∧
    -Real.log (125000000000 / 9663950232977) ≤ (1086961009 / 250000000) := by
  have h := checkLog_sound (w := (1663950232977 / 17663950232977)) (n := 12)
    (lo := (188960949 / 1000000000)) (hi := (3779219 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9663950232977 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9663950232977 / 8000000000000) = 1/(125000000000 / 9663950232977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4347844029 / 1000000000) (1086961009 / 250000000) (Real.log (9663950232977 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9663950232977 / 125000000000) = -Real.log (125000000000 / 9663950232977) := by
    rw [show ((9663950232977 / 125000000000) : ℝ) = ((125000000000 / 9663950232977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (435377079 / 100000000) ≤ -Real.log (15625000000 / 1215174527373) ∧
    -Real.log (15625000000 / 1215174527373) ≤ (4353770797 / 1000000000) := by
  have h := checkLog_sound (w := (215174527373 / 2215174527373)) (n := 12)
    (lo := (19488771 / 100000000)) (hi := (194887711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215174527373 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1215174527373 / 1000000000000) = 1/(15625000000 / 1215174527373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (435377079 / 100000000) (4353770797 / 1000000000) (Real.log (1215174527373 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1215174527373 / 15625000000) = -Real.log (15625000000 / 1215174527373) := by
    rw [show ((1215174527373 / 15625000000) : ℝ) = ((15625000000 / 1215174527373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2170798223 / 500000000) ≤ -Real.log (100000000000 / 7683009689847) ∧
    -Real.log (100000000000 / 7683009689847) ≤ (4341596453 / 1000000000) := by
  have h := checkLog_sound (w := (1283009689847 / 14083009689847)) (n := 12)
    (lo := (91356683 / 500000000)) (hi := (182713367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7683009689847 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7683009689847 / 6400000000000) = 1/(100000000000 / 7683009689847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2170798223 / 500000000) (4341596453 / 1000000000) (Real.log (7683009689847 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7683009689847 / 100000000000) = -Real.log (100000000000 / 7683009689847) := by
    rw [show ((7683009689847 / 100000000000) : ℝ) = ((100000000000 / 7683009689847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4347566431 / 1000000000) ≤ -Real.log (250000000000 / 19322535817741) ∧
    -Real.log (250000000000 / 19322535817741) ≤ (2173783219 / 500000000) := by
  have h := checkLog_sound (w := (3322535817741 / 35322535817741)) (n := 12)
    (lo := (188683351 / 1000000000)) (hi := (23585419 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19322535817741 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19322535817741 / 16000000000000) = 1/(250000000000 / 19322535817741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4347566431 / 1000000000) (2173783219 / 500000000) (Real.log (19322535817741 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (19322535817741 / 250000000000) = -Real.log (250000000000 / 19322535817741) := by
    rw [show ((19322535817741 / 250000000000) : ℝ) = ((250000000000 / 19322535817741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0063

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0064Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0064
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

theorem reflection_log_1_neg : (338870513 / 500000000) ≤ -Real.log (102400 / 201669) ∧
    -Real.log (102400 / 201669) ≤ (677741027 / 1000000000) := by
  have h := checkLog_sound (w := (99269 / 304069)) (n := 12)
    (lo := (338870513 / 500000000)) (hi := (677741027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201669 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201669 / 102400) = 1/(102400 / 201669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (338870513 / 500000000) (677741027 / 1000000000) (Real.log (201669 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201669 / 102400) = -Real.log (102400 / 201669) := by
    rw [show ((201669 / 102400) : ℝ) = ((102400 / 201669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3487534267 / 1000000000) ≤ -Real.log (3131 / 102400) ∧
    -Real.log (3131 / 102400) ≤ (3487534273 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 6331)) (n := 12)
    (lo := (21798367 / 1000000000)) (hi := (681199 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3131) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3131) = 1/(3131 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3487534273 / 1000000000) (-3487534267 / 1000000000) (Real.log (3131 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (84705851 / 125000000) ≤ -Real.log (2048 / 4033) ∧
    -Real.log (2048 / 4033) ≤ (677646809 / 1000000000) := by
  have h := checkLog_sound (w := (1985 / 6081)) (n := 12)
    (lo := (84705851 / 125000000)) (hi := (677646809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4033 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4033 / 2048) = 1/(2048 / 4033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (84705851 / 125000000) (677646809 / 1000000000) (Real.log (4033 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4033 / 2048) = -Real.log (2048 / 4033) := by
    rw [show ((4033 / 2048) : ℝ) = ((2048 / 4033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (108796383 / 31250000) ≤ -Real.log (63 / 2048) ∧
    -Real.log (63 / 2048) ≤ (1740742131 / 500000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(64 / 63) = 1/(63 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1740742131 / 500000000) (-108796383 / 31250000) (Real.log (63 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (165523451 / 250000000) ≤ -Real.log (51200 / 99269) ∧
    -Real.log (51200 / 99269) ≤ (132418761 / 200000000) := by
  have h := checkLog_sound (w := (48069 / 150469)) (n := 12)
    (lo := (165523451 / 250000000)) (hi := (132418761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99269 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99269 / 51200) = 1/(51200 / 99269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (165523451 / 250000000) (132418761 / 200000000) (Real.log (99269 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99269 / 51200) = -Real.log (51200 / 99269) := by
    rw [show ((99269 / 51200) : ℝ) = ((51200 / 99269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2794387087 / 1000000000) ≤ -Real.log (3131 / 51200) ∧
    -Real.log (3131 / 51200) ≤ (698596773 / 250000000) := by
  have h := checkLog_sound (w := (69 / 6331)) (n := 12)
    (lo := (21798367 / 1000000000)) (hi := (681199 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3131) = 1/(3131 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-698596773 / 250000000) (-2794387087 / 1000000000) (Real.log (3131 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (661902387 / 1000000000) ≤ -Real.log (1024 / 1985) ∧
    -Real.log (1024 / 1985) ≤ (165475597 / 250000000) := by
  have h := checkLog_sound (w := (961 / 3009)) (n := 12)
    (lo := (661902387 / 1000000000)) (hi := (165475597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1985 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1985 / 1024) = 1/(1024 / 1985) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (661902387 / 1000000000) (165475597 / 250000000) (Real.log (1985 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1985 / 1024) = -Real.log (1024 / 1985) := by
    rw [show ((1985 / 1024) : ℝ) = ((1024 / 1985) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (697084269 / 250000000) ≤ -Real.log (63 / 1024) ∧
    -Real.log (63 / 1024) ≤ (2788337081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(64 / 63) = 1/(63 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2788337081 / 1000000000) (-697084269 / 250000000) (Real.log (63 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170055249 / 250000000) ≤ -Real.log (500000 / 987157) ∧
    -Real.log (500000 / 987157) ≤ (680220997 / 1000000000) := by
  have h := checkLog_sound (w := (487157 / 1487157)) (n := 12)
    (lo := (170055249 / 250000000)) (hi := (680220997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987157 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987157 / 500000) = 1/(500000 / 987157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170055249 / 250000000) (680220997 / 1000000000) (Real.log (987157 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (987157 / 500000) = -Real.log (500000 / 987157) := by
    rw [show ((987157 / 500000) : ℝ) = ((500000 / 987157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3661809179 / 1000000000) ≤ -Real.log (12843 / 500000) ∧
    -Real.log (12843 / 500000) ≤ (732361837 / 200000000) := by
  have h := checkLog_sound (w := (1391 / 14234)) (n := 12)
    (lo := (196073279 / 1000000000)) (hi := (612729 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12843) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12843) = 1/(12843 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-732361837 / 200000000) (-3661809179 / 1000000000) (Real.log (12843 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170073989 / 250000000) ≤ -Real.log (500000 / 987231) ∧
    -Real.log (500000 / 987231) ≤ (680295957 / 1000000000) := by
  have h := checkLog_sound (w := (487231 / 1487231)) (n := 12)
    (lo := (170073989 / 250000000)) (hi := (680295957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987231 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987231 / 500000) = 1/(500000 / 987231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170073989 / 250000000) (680295957 / 1000000000) (Real.log (987231 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (987231 / 500000) = -Real.log (500000 / 987231) := by
    rw [show ((987231 / 500000) : ℝ) = ((500000 / 987231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3667587737 / 1000000000) ≤ -Real.log (12769 / 500000) ∧
    -Real.log (12769 / 500000) ≤ (3667587743 / 1000000000) := by
  have h := checkLog_sound (w := (1428 / 14197)) (n := 12)
    (lo := (201851837 / 1000000000)) (hi := (100925919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12769) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12769) = 1/(12769 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3667587743 / 1000000000) (-3667587737 / 1000000000) (Real.log (12769 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136027889 / 200000000) ≤ -Real.log (1000000 / 1974153) ∧
    -Real.log (1000000 / 1974153) ≤ (340069723 / 500000000) := by
  have h := checkLog_sound (w := (974153 / 2974153)) (n := 12)
    (lo := (136027889 / 200000000)) (hi := (340069723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974153 / 1000000) = 1/(1000000 / 1974153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136027889 / 200000000) (340069723 / 500000000) (Real.log (1974153 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1974153 / 1000000) = -Real.log (1000000 / 1974153) := by
    rw [show ((1974153 / 1000000) : ℝ) = ((1000000 / 1974153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (114236273 / 31250000) ≤ -Real.log (25847 / 1000000) ∧
    -Real.log (25847 / 1000000) ≤ (1827780371 / 500000000) := by
  have h := checkLog_sound (w := (5403 / 57097)) (n := 12)
    (lo := (47456209 / 250000000)) (hi := (189824837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25847) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25847) = 1/(25847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1827780371 / 500000000) (-114236273 / 31250000) (Real.log (25847 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680215931 / 1000000000) ≤ -Real.log (31250 / 61697) ∧
    -Real.log (31250 / 61697) ≤ (170053983 / 250000000) := by
  have h := checkLog_sound (w := (30447 / 92947)) (n := 12)
    (lo := (680215931 / 1000000000)) (hi := (170053983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61697 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61697 / 31250) = 1/(31250 / 61697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680215931 / 1000000000) (170053983 / 250000000) (Real.log (61697 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (61697 / 31250) = -Real.log (31250 / 61697) := by
    rw [show ((61697 / 31250) : ℝ) = ((31250 / 61697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1830709969 / 500000000) ≤ -Real.log (803 / 31250) ∧
    -Real.log (803 / 31250) ≤ (457677493 / 125000000) := by
  have h := checkLog_sound (w := (2777 / 28473)) (n := 12)
    (lo := (97842019 / 500000000)) (hi := (195684039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12848) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12848) = 1/(803 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-457677493 / 125000000) (-1830709969 / 500000000) (Real.log (803 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (173681207 / 40000000) ≤ -Real.log (12500000000 / 960792844351) ∧
    -Real.log (12500000000 / 960792844351) ≤ (2171015091 / 500000000) := by
  have h := checkLog_sound (w := (160792844351 / 1760792844351)) (n := 12)
    (lo := (36629419 / 200000000)) (hi := (22893387 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960792844351 / 800000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(960792844351 / 800000000000) = 1/(12500000000 / 960792844351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (173681207 / 40000000) (2171015091 / 500000000) (Real.log (960792844351 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (960792844351 / 12500000000) = -Real.log (12500000000 / 960792844351) := by
    rw [show ((960792844351 / 12500000000) : ℝ) = ((12500000000 / 960792844351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1086970923 / 250000000) ≤ -Real.log (50000000000 / 3865733416869) ∧
    -Real.log (50000000000 / 3865733416869) ≤ (4347883699 / 1000000000) := by
  have h := checkLog_sound (w := (665733416869 / 7065733416869)) (n := 12)
    (lo := (47250153 / 250000000)) (hi := (189000613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3865733416869 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3865733416869 / 3200000000000) = 1/(50000000000 / 3865733416869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1086970923 / 250000000) (4347883699 / 1000000000) (Real.log (3865733416869 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3865733416869 / 50000000000) = -Real.log (50000000000 / 3865733416869) := by
    rw [show ((3865733416869 / 50000000000) : ℝ) = ((50000000000 / 3865733416869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4335700181 / 1000000000) ≤ -Real.log (62500000000 / 4773651197431) ∧
    -Real.log (62500000000 / 4773651197431) ≤ (1083925047 / 250000000) := by
  have h := checkLog_sound (w := (773651197431 / 8773651197431)) (n := 12)
    (lo := (176817101 / 1000000000)) (hi := (88408551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4773651197431 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4773651197431 / 4000000000000) = 1/(62500000000 / 4773651197431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4335700181 / 1000000000) (1083925047 / 250000000) (Real.log (4773651197431 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4773651197431 / 62500000000) = -Real.log (62500000000 / 4773651197431) := by
    rw [show ((4773651197431 / 62500000000) : ℝ) = ((62500000000 / 4773651197431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4341635869 / 1000000000) ≤ -Real.log (250000000000 / 19208281444583) ∧
    -Real.log (250000000000 / 19208281444583) ≤ (1085408969 / 250000000) := by
  have h := checkLog_sound (w := (3208281444583 / 35208281444583)) (n := 12)
    (lo := (182752789 / 1000000000)) (hi := (18275279 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19208281444583 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19208281444583 / 16000000000000) = 1/(250000000000 / 19208281444583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4341635869 / 1000000000) (1085408969 / 250000000) (Real.log (19208281444583 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (19208281444583 / 250000000000) = -Real.log (250000000000 / 19208281444583) := by
    rw [show ((19208281444583 / 250000000000) : ℝ) = ((250000000000 / 19208281444583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0064

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0065
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

theorem reflection_log_1_neg : (84705851 / 125000000) ≤ -Real.log (2048 / 4033) ∧
    -Real.log (2048 / 4033) ≤ (677646809 / 1000000000) := by
  have h := checkLog_sound (w := (1985 / 6081)) (n := 12)
    (lo := (84705851 / 125000000)) (hi := (677646809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4033 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4033 / 2048) = 1/(2048 / 4033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (84705851 / 125000000) (677646809 / 1000000000) (Real.log (4033 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4033 / 2048) = -Real.log (2048 / 4033) := by
    rw [show ((4033 / 2048) : ℝ) = ((2048 / 4033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (108796383 / 31250000) ≤ -Real.log (63 / 2048) ∧
    -Real.log (63 / 2048) ≤ (1740742131 / 500000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(64 / 63) = 1/(63 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1740742131 / 500000000) (-108796383 / 31250000) (Real.log (63 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (677552581 / 1000000000) ≤ -Real.log (102400 / 201631) ∧
    -Real.log (102400 / 201631) ≤ (338776291 / 500000000) := by
  have h := checkLog_sound (w := (99231 / 304031)) (n := 12)
    (lo := (677552581 / 1000000000)) (hi := (338776291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201631 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201631 / 102400) = 1/(102400 / 201631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (677552581 / 1000000000) (338776291 / 500000000) (Real.log (201631 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201631 / 102400) = -Real.log (102400 / 201631) := by
    rw [show ((201631 / 102400) : ℝ) = ((102400 / 201631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3475470629 / 1000000000) ≤ -Real.log (3169 / 102400) ∧
    -Real.log (3169 / 102400) ≤ (695094127 / 200000000) := by
  have h := checkLog_sound (w := (31 / 6369)) (n := 12)
    (lo := (9734729 / 1000000000)) (hi := (973473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3169) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3169) = 1/(3169 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-695094127 / 200000000) (-3475470629 / 1000000000) (Real.log (3169 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (661902387 / 1000000000) ≤ -Real.log (1024 / 1985) ∧
    -Real.log (1024 / 1985) ≤ (165475597 / 250000000) := by
  have h := checkLog_sound (w := (961 / 3009)) (n := 12)
    (lo := (661902387 / 1000000000)) (hi := (165475597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1985 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1985 / 1024) = 1/(1024 / 1985) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (661902387 / 1000000000) (165475597 / 250000000) (Real.log (1985 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1985 / 1024) = -Real.log (1024 / 1985) := by
    rw [show ((1985 / 1024) : ℝ) = ((1024 / 1985) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (697084269 / 250000000) ≤ -Real.log (63 / 1024) ∧
    -Real.log (63 / 1024) ≤ (2788337081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(64 / 63) = 1/(63 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2788337081 / 1000000000) (-697084269 / 250000000) (Real.log (63 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (661710933 / 1000000000) ≤ -Real.log (51200 / 99231) ∧
    -Real.log (51200 / 99231) ≤ (330855467 / 500000000) := by
  have h := checkLog_sound (w := (48031 / 150431)) (n := 12)
    (lo := (661710933 / 1000000000)) (hi := (330855467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99231 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99231 / 51200) = 1/(51200 / 99231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (661710933 / 1000000000) (330855467 / 500000000) (Real.log (99231 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99231 / 51200) = -Real.log (51200 / 99231) := by
    rw [show ((99231 / 51200) : ℝ) = ((51200 / 99231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2782323449 / 1000000000) ≤ -Real.log (3169 / 51200) ∧
    -Real.log (3169 / 51200) ≤ (1391161727 / 500000000) := by
  have h := checkLog_sound (w := (31 / 6369)) (n := 12)
    (lo := (9734729 / 1000000000)) (hi := (973473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3169) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3169) = 1/(3169 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1391161727 / 500000000) (-2782323449 / 1000000000) (Real.log (3169 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68014603 / 100000000) ≤ -Real.log (500000 / 987083) ∧
    -Real.log (500000 / 987083) ≤ (680146031 / 1000000000) := by
  have h := checkLog_sound (w := (487083 / 1487083)) (n := 12)
    (lo := (68014603 / 100000000)) (hi := (680146031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987083 / 500000) = 1/(500000 / 987083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68014603 / 100000000) (680146031 / 1000000000) (Real.log (987083 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (987083 / 500000) = -Real.log (500000 / 987083) := by
    rw [show ((987083 / 500000) : ℝ) = ((500000 / 987083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1828031911 / 500000000) ≤ -Real.log (12917 / 500000) ∧
    -Real.log (12917 / 500000) ≤ (914015957 / 250000000) := by
  have h := checkLog_sound (w := (1354 / 14271)) (n := 12)
    (lo := (95163961 / 500000000)) (hi := (190327923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12917) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12917) = 1/(12917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-914015957 / 250000000) (-1828031911 / 500000000) (Real.log (12917 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340110751 / 500000000) ≤ -Real.log (200000 / 394863) ∧
    -Real.log (200000 / 394863) ≤ (680221503 / 1000000000) := by
  have h := checkLog_sound (w := (194863 / 594863)) (n := 12)
    (lo := (340110751 / 500000000)) (hi := (680221503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394863 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394863 / 200000) = 1/(200000 / 394863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340110751 / 500000000) (680221503 / 1000000000) (Real.log (394863 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (394863 / 200000) = -Real.log (200000 / 394863) := by
    rw [show ((394863 / 200000) : ℝ) = ((200000 / 394863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (228865507 / 62500000) ≤ -Real.log (5137 / 200000) ∧
    -Real.log (5137 / 200000) ≤ (1830924059 / 500000000) := by
  have h := checkLog_sound (w := (1113 / 11387)) (n := 12)
    (lo := (49028053 / 250000000)) (hi := (196112213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5137) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5137) = 1/(5137 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1830924059 / 500000000) (-228865507 / 62500000) (Real.log (5137 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680063967 / 1000000000) ≤ -Real.log (250000 / 493501) ∧
    -Real.log (250000 / 493501) ≤ (21251999 / 31250000) := by
  have h := checkLog_sound (w := (243501 / 743501)) (n := 12)
    (lo := (680063967 / 1000000000)) (hi := (21251999 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493501 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493501 / 250000) = 1/(250000 / 493501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680063967 / 1000000000) (21251999 / 31250000) (Real.log (493501 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (493501 / 250000) = -Real.log (250000 / 493501) := by
    rw [show ((493501 / 250000) : ℝ) = ((250000 / 493501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (912453149 / 250000000) ≤ -Real.log (6499 / 250000) ∧
    -Real.log (6499 / 250000) ≤ (1824906301 / 500000000) := by
  have h := checkLog_sound (w := (2627 / 28623)) (n := 12)
    (lo := (23009587 / 125000000)) (hi := (184076697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12998) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12998) = 1/(6499 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1824906301 / 500000000) (-912453149 / 250000000) (Real.log (6499 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42508747 / 62500000) ≤ -Real.log (500000 / 987077) ∧
    -Real.log (500000 / 987077) ≤ (680139953 / 1000000000) := by
  have h := checkLog_sound (w := (487077 / 1487077)) (n := 12)
    (lo := (42508747 / 62500000)) (hi := (680139953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987077 / 500000) = 1/(500000 / 987077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42508747 / 62500000) (680139953 / 1000000000) (Real.log (987077 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (987077 / 500000) = -Real.log (500000 / 987077) := by
    rw [show ((987077 / 500000) : ℝ) = ((500000 / 987077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1827799713 / 500000000) ≤ -Real.log (12923 / 500000) ∧
    -Real.log (12923 / 500000) ≤ (456949929 / 125000000) := by
  have h := checkLog_sound (w := (1351 / 14274)) (n := 12)
    (lo := (94931763 / 500000000)) (hi := (189863527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12923) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12923) = 1/(12923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-456949929 / 125000000) (-1827799713 / 500000000) (Real.log (12923 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1084052463 / 250000000) ≤ -Real.log (125000000000 / 9552169621429) ∧
    -Real.log (125000000000 / 9552169621429) ≤ (4336209859 / 1000000000) := by
  have h := checkLog_sound (w := (1552169621429 / 17552169621429)) (n := 12)
    (lo := (44331693 / 250000000)) (hi := (177326773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9552169621429 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9552169621429 / 8000000000000) = 1/(125000000000 / 9552169621429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1084052463 / 250000000) (4336209859 / 1000000000) (Real.log (9552169621429 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9552169621429 / 125000000000) = -Real.log (125000000000 / 9552169621429) := by
    rw [show ((9552169621429 / 125000000000) : ℝ) = ((125000000000 / 9552169621429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2171034807 / 500000000) ≤ -Real.log (125000000000 / 9608307377847) ∧
    -Real.log (125000000000 / 9608307377847) ≤ (4342069621 / 1000000000) := by
  have h := checkLog_sound (w := (1608307377847 / 17608307377847)) (n := 12)
    (lo := (91593267 / 500000000)) (hi := (36637307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9608307377847 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9608307377847 / 8000000000000) = 1/(125000000000 / 9608307377847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2171034807 / 500000000) (4342069621 / 1000000000) (Real.log (9608307377847 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9608307377847 / 125000000000) = -Real.log (125000000000 / 9608307377847) := by
    rw [show ((9608307377847 / 125000000000) : ℝ) = ((125000000000 / 9608307377847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2164938281 / 500000000) ≤ -Real.log (250000000000 / 18983728265887) ∧
    -Real.log (250000000000 / 18983728265887) ≤ (4329876569 / 1000000000) := by
  have h := checkLog_sound (w := (2983728265887 / 34983728265887)) (n := 12)
    (lo := (85496741 / 500000000)) (hi := (170993483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18983728265887 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18983728265887 / 16000000000000) = 1/(250000000000 / 18983728265887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2164938281 / 500000000) (4329876569 / 1000000000) (Real.log (18983728265887 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (18983728265887 / 250000000000) = -Real.log (250000000000 / 18983728265887) := by
    rw [show ((18983728265887 / 250000000000) : ℝ) = ((250000000000 / 18983728265887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4335739377 / 1000000000) ≤ -Real.log (500000000000 / 38190706492301) ∧
    -Real.log (500000000000 / 38190706492301) ≤ (541967423 / 125000000) := by
  have h := checkLog_sound (w := (6190706492301 / 70190706492301)) (n := 12)
    (lo := (176856297 / 1000000000)) (hi := (88428149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38190706492301 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38190706492301 / 32000000000000) = 1/(500000000000 / 38190706492301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4335739377 / 1000000000) (541967423 / 125000000) (Real.log (38190706492301 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (38190706492301 / 500000000000) = -Real.log (500000000000 / 38190706492301) := by
    rw [show ((38190706492301 / 500000000000) : ℝ) = ((500000000000 / 38190706492301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0065

end


