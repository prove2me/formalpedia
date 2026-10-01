-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0087Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0087Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:56:32.835447+00:00
-- url     : https://prove2.me/theorems/87b6d1dc-745c-4c6e-af0d-ae707741f160
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0087Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0088Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0087Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0088Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0089Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0090Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0091Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0087Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0088Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0089Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0090Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0091Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0087Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0088Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0089Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0090Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0091Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0087Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0088Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0089Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0090Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0091Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0087Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0087
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

theorem reflection_log_1_neg : (673870781 / 1000000000) ≤ -Real.log (10240 / 20089) ∧
    -Real.log (10240 / 20089) ≤ (336935391 / 500000000) := by
  have h := checkLog_sound (w := (9849 / 30329)) (n := 12)
    (lo := (673870781 / 1000000000)) (hi := (336935391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20089 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20089 / 10240) = 1/(10240 / 20089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (673870781 / 1000000000) (336935391 / 500000000) (Real.log (20089 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20089 / 10240) = -Real.log (10240 / 20089) := by
    rw [show ((20089 / 10240) : ℝ) = ((10240 / 20089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (408168667 / 125000000) ≤ -Real.log (391 / 10240) ∧
    -Real.log (391 / 10240) ≤ (3265349341 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 1031)) (n := 12)
    (lo := (61595077 / 125000000)) (hi := (492760617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 391) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 391) = 1/(391 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3265349341 / 1000000000) (-408168667 / 125000000) (Real.log (391 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134736321 / 200000000) ≤ -Real.log (25600 / 50213) ∧
    -Real.log (25600 / 50213) ≤ (336840803 / 500000000) := by
  have h := checkLog_sound (w := (24613 / 75813)) (n := 12)
    (lo := (134736321 / 200000000)) (hi := (336840803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50213 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50213 / 25600) = 1/(25600 / 50213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134736321 / 200000000) (336840803 / 500000000) (Real.log (50213 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50213 / 25600) = -Real.log (25600 / 50213) := by
    rw [show ((50213 / 25600) : ℝ) = ((25600 / 50213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (813919397 / 250000000) ≤ -Real.log (987 / 25600) ∧
    -Real.log (987 / 25600) ≤ (3255677593 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 2587)) (n := 12)
    (lo := (120772217 / 250000000)) (hi := (483088869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 987) = 1/(987 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3255677593 / 1000000000) (-813919397 / 250000000) (Real.log (987 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10222117 / 15625000) ≤ -Real.log (5120 / 9849) ∧
    -Real.log (5120 / 9849) ≤ (654215489 / 1000000000) := by
  have h := checkLog_sound (w := (4729 / 14969)) (n := 12)
    (lo := (10222117 / 15625000)) (hi := (654215489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9849 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9849 / 5120) = 1/(5120 / 9849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10222117 / 15625000) (654215489 / 1000000000) (Real.log (9849 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9849 / 5120) = -Real.log (5120 / 9849) := by
    rw [show ((9849 / 5120) : ℝ) = ((5120 / 9849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (643050539 / 250000000) ≤ -Real.log (391 / 5120) ∧
    -Real.log (391 / 5120) ≤ (32152527 / 12500000) := by
  have h := checkLog_sound (w := (249 / 1031)) (n := 12)
    (lo := (61595077 / 125000000)) (hi := (492760617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 391) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 391) = 1/(391 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-32152527 / 12500000) (-643050539 / 250000000) (Real.log (391 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (653829587 / 1000000000) ≤ -Real.log (12800 / 24613) ∧
    -Real.log (12800 / 24613) ≤ (163457397 / 250000000) := by
  have h := checkLog_sound (w := (11813 / 37413)) (n := 12)
    (lo := (653829587 / 1000000000)) (hi := (163457397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24613 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24613 / 12800) = 1/(12800 / 24613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (653829587 / 1000000000) (163457397 / 250000000) (Real.log (24613 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24613 / 12800) = -Real.log (12800 / 24613) := by
    rw [show ((24613 / 12800) : ℝ) = ((12800 / 24613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (320316301 / 125000000) ≤ -Real.log (987 / 12800) ∧
    -Real.log (987 / 12800) ≤ (640632603 / 250000000) := by
  have h := checkLog_sound (w := (613 / 2587)) (n := 12)
    (lo := (120772217 / 250000000)) (hi := (483088869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 987) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 987) = 1/(987 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-640632603 / 250000000) (-320316301 / 125000000) (Real.log (987 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (677109257 / 1000000000) ≤ -Real.log (50000 / 98409) ∧
    -Real.log (50000 / 98409) ≤ (338554629 / 500000000) := by
  have h := checkLog_sound (w := (48409 / 148409)) (n := 12)
    (lo := (677109257 / 1000000000)) (hi := (338554629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98409 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98409 / 50000) = 1/(50000 / 98409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (677109257 / 1000000000) (338554629 / 500000000) (Real.log (98409 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (98409 / 50000) = -Real.log (50000 / 98409) := by
    rw [show ((98409 / 50000) : ℝ) = ((50000 / 98409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3447660253 / 1000000000) ≤ -Real.log (1591 / 50000) ∧
    -Real.log (1591 / 50000) ≤ (1723830129 / 500000000) := by
  have h := checkLog_sound (w := (767 / 2358)) (n := 12)
    (lo := (675071533 / 1000000000)) (hi := (337535767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1591) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1591) = 1/(1591 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1723830129 / 500000000) (-3447660253 / 1000000000) (Real.log (1591 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (677257099 / 1000000000) ≤ -Real.log (1000000 / 1968471) ∧
    -Real.log (1000000 / 1968471) ≤ (6772571 / 10000000) := by
  have h := checkLog_sound (w := (968471 / 2968471)) (n := 12)
    (lo := (677257099 / 1000000000)) (hi := (6772571 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968471 / 1000000) = 1/(1000000 / 1968471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (677257099 / 1000000000) (6772571 / 10000000) (Real.log (1968471 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1968471 / 1000000) = -Real.log (1000000 / 1968471) := by
    rw [show ((1968471 / 1000000) : ℝ) = ((1000000 / 1968471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3456847519 / 1000000000) ≤ -Real.log (31529 / 1000000) ∧
    -Real.log (31529 / 1000000) ≤ (864211881 / 250000000) := by
  have h := checkLog_sound (w := (30971 / 94029)) (n := 12)
    (lo := (684258799 / 1000000000)) (hi := (1710647 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31529) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 31529) = 1/(31529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-864211881 / 250000000) (-3456847519 / 1000000000) (Real.log (31529 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67697359 / 100000000) ≤ -Real.log (1000000 / 1967913) ∧
    -Real.log (1000000 / 1967913) ≤ (676973591 / 1000000000) := by
  have h := checkLog_sound (w := (967913 / 2967913)) (n := 12)
    (lo := (67697359 / 100000000)) (hi := (676973591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967913 / 1000000) = 1/(1000000 / 1967913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67697359 / 100000000) (676973591 / 1000000000) (Real.log (1967913 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1967913 / 1000000) = -Real.log (1000000 / 1967913) := by
    rw [show ((1967913 / 1000000) : ℝ) = ((1000000 / 1967913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3439304313 / 1000000000) ≤ -Real.log (32087 / 1000000) ∧
    -Real.log (32087 / 1000000) ≤ (1719652159 / 500000000) := by
  have h := checkLog_sound (w := (30413 / 94587)) (n := 12)
    (lo := (666715593 / 1000000000)) (hi := (333357797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32087) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32087) = 1/(32087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1719652159 / 500000000) (-3439304313 / 1000000000) (Real.log (32087 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1354249 / 2000000) ≤ -Real.log (100000 / 196821) ∧
    -Real.log (100000 / 196821) ≤ (677124501 / 1000000000) := by
  have h := checkLog_sound (w := (96821 / 296821)) (n := 12)
    (lo := (1354249 / 2000000)) (hi := (677124501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196821 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196821 / 100000) = 1/(100000 / 196821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1354249 / 2000000) (677124501 / 1000000000) (Real.log (196821 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (196821 / 100000) = -Real.log (100000 / 196821) := by
    rw [show ((196821 / 100000) : ℝ) = ((100000 / 196821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3448603501 / 1000000000) ≤ -Real.log (3179 / 100000) ∧
    -Real.log (3179 / 100000) ≤ (1724301753 / 500000000) := by
  have h := checkLog_sound (w := (3071 / 9429)) (n := 12)
    (lo := (676014781 / 1000000000)) (hi := (338007391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3179) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3179) = 1/(3179 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1724301753 / 500000000) (-3448603501 / 1000000000) (Real.log (3179 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4124769511 / 1000000000) ≤ -Real.log (250000000000 / 15463387806411) ∧
    -Real.log (250000000000 / 15463387806411) ≤ (4124769517 / 1000000000) := by
  have h := checkLog_sound (w := (7463387806411 / 23463387806411)) (n := 12)
    (lo := (659033611 / 1000000000)) (hi := (164758403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15463387806411 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15463387806411 / 8000000000000) = 1/(250000000000 / 15463387806411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4124769511 / 1000000000) (4124769517 / 1000000000) (Real.log (15463387806411 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15463387806411 / 250000000000) = -Real.log (250000000000 / 15463387806411) := by
    rw [show ((15463387806411 / 250000000000) : ℝ) = ((250000000000 / 15463387806411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2067052309 / 500000000) ≤ -Real.log (62500000000 / 3902104015351) ∧
    -Real.log (62500000000 / 3902104015351) ≤ (258381539 / 62500000) := by
  have h := checkLog_sound (w := (1902104015351 / 5902104015351)) (n := 12)
    (lo := (334184359 / 500000000)) (hi := (668368719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3902104015351 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3902104015351 / 2000000000000) = 1/(62500000000 / 3902104015351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2067052309 / 500000000) (258381539 / 62500000) (Real.log (3902104015351 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3902104015351 / 62500000000) = -Real.log (62500000000 / 3902104015351) := by
    rw [show ((3902104015351 / 62500000000) : ℝ) = ((62500000000 / 3902104015351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2058138951 / 500000000) ≤ -Real.log (250000000000 / 15332634711877) ∧
    -Real.log (250000000000 / 15332634711877) ≤ (1029069477 / 250000000) := by
  have h := checkLog_sound (w := (7332634711877 / 23332634711877)) (n := 12)
    (lo := (325271001 / 500000000)) (hi := (650542003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15332634711877 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15332634711877 / 8000000000000) = 1/(250000000000 / 15332634711877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2058138951 / 500000000) (1029069477 / 250000000) (Real.log (15332634711877 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (15332634711877 / 250000000000) = -Real.log (250000000000 / 15332634711877) := by
    rw [show ((15332634711877 / 250000000000) : ℝ) = ((250000000000 / 15332634711877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4125728001 / 1000000000) ≤ -Real.log (125000000000 / 7739108210129) ∧
    -Real.log (125000000000 / 7739108210129) ≤ (4125728007 / 1000000000) := by
  have h := checkLog_sound (w := (3739108210129 / 11739108210129)) (n := 12)
    (lo := (659992101 / 1000000000)) (hi := (329996051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7739108210129 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7739108210129 / 4000000000000) = 1/(125000000000 / 7739108210129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4125728001 / 1000000000) (4125728007 / 1000000000) (Real.log (7739108210129 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7739108210129 / 125000000000) = -Real.log (125000000000 / 7739108210129) := by
    rw [show ((7739108210129 / 125000000000) : ℝ) = ((125000000000 / 7739108210129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0087

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0088Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0088
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

theorem reflection_log_1_neg : (134736321 / 200000000) ≤ -Real.log (25600 / 50213) ∧
    -Real.log (25600 / 50213) ≤ (336840803 / 500000000) := by
  have h := checkLog_sound (w := (24613 / 75813)) (n := 12)
    (lo := (134736321 / 200000000)) (hi := (336840803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50213 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50213 / 25600) = 1/(25600 / 50213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134736321 / 200000000) (336840803 / 500000000) (Real.log (50213 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50213 / 25600) = -Real.log (25600 / 50213) := by
    rw [show ((50213 / 25600) : ℝ) = ((25600 / 50213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (813919397 / 250000000) ≤ -Real.log (987 / 25600) ∧
    -Real.log (987 / 25600) ≤ (3255677593 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 2587)) (n := 12)
    (lo := (120772217 / 250000000)) (hi := (483088869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 987) = 1/(987 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3255677593 / 1000000000) (-813919397 / 250000000) (Real.log (987 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (673492393 / 1000000000) ≤ -Real.log (51200 / 100407) ∧
    -Real.log (51200 / 100407) ≤ (336746197 / 500000000) := by
  have h := checkLog_sound (w := (49207 / 151607)) (n := 12)
    (lo := (673492393 / 1000000000)) (hi := (336746197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100407 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100407 / 51200) = 1/(51200 / 100407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (673492393 / 1000000000) (336746197 / 500000000) (Real.log (100407 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100407 / 51200) = -Real.log (51200 / 100407) := by
    rw [show ((100407 / 51200) : ℝ) = ((51200 / 100407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (405762311 / 125000000) ≤ -Real.log (1993 / 51200) ∧
    -Real.log (1993 / 51200) ≤ (3246098493 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 5193)) (n := 12)
    (lo := (59188721 / 125000000)) (hi := (473509769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1993) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1993) = 1/(1993 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3246098493 / 1000000000) (-405762311 / 125000000) (Real.log (1993 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (653829587 / 1000000000) ≤ -Real.log (12800 / 24613) ∧
    -Real.log (12800 / 24613) ≤ (163457397 / 250000000) := by
  have h := checkLog_sound (w := (11813 / 37413)) (n := 12)
    (lo := (653829587 / 1000000000)) (hi := (163457397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24613 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24613 / 12800) = 1/(12800 / 24613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (653829587 / 1000000000) (163457397 / 250000000) (Real.log (24613 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24613 / 12800) = -Real.log (12800 / 24613) := by
    rw [show ((24613 / 12800) : ℝ) = ((12800 / 24613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (320316301 / 125000000) ≤ -Real.log (987 / 12800) ∧
    -Real.log (987 / 12800) ≤ (640632603 / 250000000) := by
  have h := checkLog_sound (w := (613 / 2587)) (n := 12)
    (lo := (120772217 / 250000000)) (hi := (483088869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 987) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 987) = 1/(987 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-640632603 / 250000000) (-320316301 / 125000000) (Real.log (987 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (326721769 / 500000000) ≤ -Real.log (25600 / 49207) ∧
    -Real.log (25600 / 49207) ≤ (653443539 / 1000000000) := by
  have h := checkLog_sound (w := (23607 / 74807)) (n := 12)
    (lo := (326721769 / 500000000)) (hi := (653443539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49207 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49207 / 25600) = 1/(25600 / 49207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (326721769 / 500000000) (653443539 / 1000000000) (Real.log (49207 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49207 / 25600) = -Real.log (25600 / 49207) := by
    rw [show ((49207 / 25600) : ℝ) = ((25600 / 49207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (638237827 / 250000000) ≤ -Real.log (1993 / 25600) ∧
    -Real.log (1993 / 25600) ≤ (159559457 / 62500000) := by
  have h := checkLog_sound (w := (1207 / 5193)) (n := 12)
    (lo := (59188721 / 125000000)) (hi := (473509769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1993) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1993) = 1/(1993 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159559457 / 62500000) (-638237827 / 250000000) (Real.log (1993 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67696241 / 100000000) ≤ -Real.log (1000000 / 1967891) ∧
    -Real.log (1000000 / 1967891) ≤ (676962411 / 1000000000) := by
  have h := checkLog_sound (w := (967891 / 2967891)) (n := 12)
    (lo := (67696241 / 100000000)) (hi := (676962411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967891 / 1000000) = 1/(1000000 / 1967891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67696241 / 100000000) (676962411 / 1000000000) (Real.log (1967891 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1967891 / 1000000) = -Real.log (1000000 / 1967891) := by
    rw [show ((1967891 / 1000000) : ℝ) = ((1000000 / 1967891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107456841 / 31250000) ≤ -Real.log (32109 / 1000000) ∧
    -Real.log (32109 / 1000000) ≤ (3438618917 / 1000000000) := by
  have h := checkLog_sound (w := (30391 / 94609)) (n := 12)
    (lo := (41626887 / 62500000)) (hi := (666030193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32109) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32109) = 1/(32109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3438618917 / 1000000000) (-107456841 / 31250000) (Real.log (32109 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135421953 / 200000000) ≤ -Real.log (1000000 / 1968181) ∧
    -Real.log (1000000 / 1968181) ≤ (338554883 / 500000000) := by
  have h := checkLog_sound (w := (968181 / 2968181)) (n := 12)
    (lo := (135421953 / 200000000)) (hi := (338554883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968181 / 1000000) = 1/(1000000 / 1968181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135421953 / 200000000) (338554883 / 500000000) (Real.log (1968181 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1968181 / 1000000) = -Real.log (1000000 / 1968181) := by
    rw [show ((1968181 / 1000000) : ℝ) = ((1000000 / 1968181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3447691681 / 1000000000) ≤ -Real.log (31819 / 1000000) ∧
    -Real.log (31819 / 1000000) ≤ (1723845843 / 500000000) := by
  have h := checkLog_sound (w := (30681 / 94319)) (n := 12)
    (lo := (675102961 / 1000000000)) (hi := (337551481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31819) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 31819) = 1/(31819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1723845843 / 500000000) (-3447691681 / 1000000000) (Real.log (31819 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338411837 / 500000000) ≤ -Real.log (500000 / 983809) ∧
    -Real.log (500000 / 983809) ≤ (27072947 / 40000000) := by
  have h := checkLog_sound (w := (483809 / 1483809)) (n := 12)
    (lo := (338411837 / 500000000)) (hi := (27072947 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983809 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983809 / 500000) = 1/(500000 / 983809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338411837 / 500000000) (27072947 / 40000000) (Real.log (983809 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (983809 / 500000) = -Real.log (500000 / 983809) := by
    rw [show ((983809 / 500000) : ℝ) = ((500000 / 983809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3430152563 / 1000000000) ≤ -Real.log (16191 / 500000) ∧
    -Real.log (16191 / 500000) ≤ (428769071 / 125000000) := by
  have h := checkLog_sound (w := (15059 / 47441)) (n := 12)
    (lo := (657563843 / 1000000000)) (hi := (164390961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16191) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16191) = 1/(16191 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-428769071 / 125000000) (-3430152563 / 1000000000) (Real.log (16191 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338487049 / 500000000) ≤ -Real.log (500000 / 983957) ∧
    -Real.log (500000 / 983957) ≤ (676974099 / 1000000000) := by
  have h := checkLog_sound (w := (483957 / 1483957)) (n := 12)
    (lo := (338487049 / 500000000)) (hi := (676974099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983957 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983957 / 500000) = 1/(500000 / 983957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338487049 / 500000000) (676974099 / 1000000000) (Real.log (983957 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (983957 / 500000) = -Real.log (500000 / 983957) := by
    rw [show ((983957 / 500000) : ℝ) = ((500000 / 983957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1719667739 / 500000000) ≤ -Real.log (16043 / 500000) ∧
    -Real.log (16043 / 500000) ≤ (3439335483 / 1000000000) := by
  have h := checkLog_sound (w := (15207 / 47293)) (n := 12)
    (lo := (333373379 / 500000000)) (hi := (666746759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16043) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16043) = 1/(16043 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3439335483 / 1000000000) (-1719667739 / 500000000) (Real.log (16043 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2057790661 / 500000000) ≤ -Real.log (250000000000 / 15321958018001) ∧
    -Real.log (250000000000 / 15321958018001) ≤ (257223833 / 62500000) := by
  have h := checkLog_sound (w := (7321958018001 / 23321958018001)) (n := 12)
    (lo := (324922711 / 500000000)) (hi := (649845423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15321958018001 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15321958018001 / 8000000000000) = 1/(250000000000 / 15321958018001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2057790661 / 500000000) (257223833 / 62500000) (Real.log (15321958018001 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15321958018001 / 250000000000) = -Real.log (250000000000 / 15321958018001) := by
    rw [show ((15321958018001 / 250000000000) : ℝ) = ((250000000000 / 15321958018001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2062400723 / 500000000) ≤ -Real.log (500000000000 / 30927763286087) ∧
    -Real.log (500000000000 / 30927763286087) ≤ (1031200363 / 250000000) := by
  have h := checkLog_sound (w := (14927763286087 / 46927763286087)) (n := 12)
    (lo := (329532773 / 500000000)) (hi := (659065547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30927763286087 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30927763286087 / 16000000000000) = 1/(500000000000 / 30927763286087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2062400723 / 500000000) (1031200363 / 250000000) (Real.log (30927763286087 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (30927763286087 / 500000000000) = -Real.log (500000000000 / 30927763286087) := by
    rw [show ((30927763286087 / 500000000000) : ℝ) = ((500000000000 / 30927763286087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4106976237 / 1000000000) ≤ -Real.log (62500000000 / 3797669229819) ∧
    -Real.log (62500000000 / 3797669229819) ≤ (4106976243 / 1000000000) := by
  have h := checkLog_sound (w := (1797669229819 / 5797669229819)) (n := 12)
    (lo := (641240337 / 1000000000)) (hi := (320620169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3797669229819 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3797669229819 / 2000000000000) = 1/(62500000000 / 3797669229819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4106976237 / 1000000000) (4106976243 / 1000000000) (Real.log (3797669229819 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3797669229819 / 62500000000) = -Real.log (62500000000 / 3797669229819) := by
    rw [show ((3797669229819 / 62500000000) : ℝ) = ((62500000000 / 3797669229819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (514538697 / 125000000) ≤ -Real.log (125000000000 / 7666560182011) ∧
    -Real.log (125000000000 / 7666560182011) ≤ (2058154791 / 500000000) := by
  have h := checkLog_sound (w := (3666560182011 / 11666560182011)) (n := 12)
    (lo := (162643419 / 250000000)) (hi := (650573677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7666560182011 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7666560182011 / 4000000000000) = 1/(125000000000 / 7666560182011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (514538697 / 125000000) (2058154791 / 500000000) (Real.log (7666560182011 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7666560182011 / 125000000000) = -Real.log (125000000000 / 7666560182011) := by
    rw [show ((7666560182011 / 125000000000) : ℝ) = ((125000000000 / 7666560182011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0088

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0089Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0089
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

theorem reflection_log_1_neg : (673492393 / 1000000000) ≤ -Real.log (51200 / 100407) ∧
    -Real.log (51200 / 100407) ≤ (336746197 / 500000000) := by
  have h := checkLog_sound (w := (49207 / 151607)) (n := 12)
    (lo := (673492393 / 1000000000)) (hi := (336746197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100407 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100407 / 51200) = 1/(51200 / 100407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (673492393 / 1000000000) (336746197 / 500000000) (Real.log (100407 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100407 / 51200) = -Real.log (51200 / 100407) := by
    rw [show ((100407 / 51200) : ℝ) = ((51200 / 100407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (405762311 / 125000000) ≤ -Real.log (1993 / 51200) ∧
    -Real.log (1993 / 51200) ≤ (3246098493 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 5193)) (n := 12)
    (lo := (59188721 / 125000000)) (hi := (473509769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1993) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1993) = 1/(1993 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3246098493 / 1000000000) (-405762311 / 125000000) (Real.log (1993 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (336651573 / 500000000) ≤ -Real.log (12800 / 25097) ∧
    -Real.log (12800 / 25097) ≤ (673303147 / 1000000000) := by
  have h := checkLog_sound (w := (12297 / 37897)) (n := 12)
    (lo := (336651573 / 500000000)) (hi := (673303147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25097 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25097 / 12800) = 1/(12800 / 25097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (336651573 / 500000000) (673303147 / 1000000000) (Real.log (25097 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25097 / 12800) = -Real.log (12800 / 25097) := by
    rw [show ((25097 / 12800) : ℝ) = ((12800 / 25097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3236610277 / 1000000000) ≤ -Real.log (503 / 12800) ∧
    -Real.log (503 / 12800) ≤ (1618305141 / 500000000) := by
  have h := checkLog_sound (w := (297 / 1303)) (n := 12)
    (lo := (464021557 / 1000000000)) (hi := (232010779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 503) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 503) = 1/(503 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1618305141 / 500000000) (-3236610277 / 1000000000) (Real.log (503 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (326721769 / 500000000) ≤ -Real.log (25600 / 49207) ∧
    -Real.log (25600 / 49207) ≤ (653443539 / 1000000000) := by
  have h := checkLog_sound (w := (23607 / 74807)) (n := 12)
    (lo := (326721769 / 500000000)) (hi := (653443539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49207 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49207 / 25600) = 1/(25600 / 49207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (326721769 / 500000000) (653443539 / 1000000000) (Real.log (49207 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49207 / 25600) = -Real.log (25600 / 49207) := by
    rw [show ((49207 / 25600) : ℝ) = ((25600 / 49207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (638237827 / 250000000) ≤ -Real.log (1993 / 25600) ∧
    -Real.log (1993 / 25600) ≤ (159559457 / 62500000) := by
  have h := checkLog_sound (w := (1207 / 5193)) (n := 12)
    (lo := (59188721 / 125000000)) (hi := (473509769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1993) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1993) = 1/(1993 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159559457 / 62500000) (-638237827 / 250000000) (Real.log (1993 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (653057339 / 1000000000) ≤ -Real.log (6400 / 12297) ∧
    -Real.log (6400 / 12297) ≤ (32652867 / 50000000) := by
  have h := checkLog_sound (w := (5897 / 18697)) (n := 12)
    (lo := (653057339 / 1000000000)) (hi := (32652867 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12297 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12297 / 6400) = 1/(6400 / 12297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (653057339 / 1000000000) (32652867 / 50000000) (Real.log (12297 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12297 / 6400) = -Real.log (6400 / 12297) := by
    rw [show ((12297 / 6400) : ℝ) = ((6400 / 12297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2543463097 / 1000000000) ≤ -Real.log (503 / 6400) ∧
    -Real.log (503 / 6400) ≤ (2543463101 / 1000000000) := by
  have h := checkLog_sound (w := (297 / 1303)) (n := 12)
    (lo := (464021557 / 1000000000)) (hi := (232010779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 503) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 503) = 1/(503 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2543463101 / 1000000000) (-2543463097 / 1000000000) (Real.log (503 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (338407771 / 500000000) ≤ -Real.log (500000 / 983801) ∧
    -Real.log (500000 / 983801) ≤ (676815543 / 1000000000) := by
  have h := checkLog_sound (w := (483801 / 1483801)) (n := 12)
    (lo := (338407771 / 500000000)) (hi := (676815543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983801 / 500000) = 1/(500000 / 983801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (338407771 / 500000000) (676815543 / 1000000000) (Real.log (983801 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (983801 / 500000) = -Real.log (500000 / 983801) := by
    rw [show ((983801 / 500000) : ℝ) = ((500000 / 983801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (428707323 / 125000000) ≤ -Real.log (16199 / 500000) ∧
    -Real.log (16199 / 500000) ≤ (3429658589 / 1000000000) := by
  have h := checkLog_sound (w := (15051 / 47449)) (n := 12)
    (lo := (82133733 / 125000000)) (hi := (131413973 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16199) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16199) = 1/(16199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3429658589 / 1000000000) (-428707323 / 125000000) (Real.log (16199 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (676962919 / 1000000000) ≤ -Real.log (250000 / 491973) ∧
    -Real.log (250000 / 491973) ≤ (16924073 / 25000000) := by
  have h := checkLog_sound (w := (241973 / 741973)) (n := 12)
    (lo := (676962919 / 1000000000)) (hi := (16924073 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491973 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491973 / 250000) = 1/(250000 / 491973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (676962919 / 1000000000) (16924073 / 25000000) (Real.log (491973 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (491973 / 250000) = -Real.log (250000 / 491973) := by
    rw [show ((491973 / 250000) : ℝ) = ((250000 / 491973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (429831257 / 125000000) ≤ -Real.log (8027 / 250000) ∧
    -Real.log (8027 / 250000) ≤ (3438650061 / 1000000000) := by
  have h := checkLog_sound (w := (3799 / 11826)) (n := 12)
    (lo := (83257667 / 125000000)) (hi := (666061337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8027) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8027) = 1/(8027 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3438650061 / 1000000000) (-429831257 / 125000000) (Real.log (8027 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (676674243 / 1000000000) ≤ -Real.log (250000 / 491831) ∧
    -Real.log (250000 / 491831) ≤ (169168561 / 250000000) := by
  have h := checkLog_sound (w := (241831 / 741831)) (n := 12)
    (lo := (676674243 / 1000000000)) (hi := (169168561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491831 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491831 / 250000) = 1/(250000 / 491831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (676674243 / 1000000000) (169168561 / 250000000) (Real.log (491831 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (491831 / 250000) = -Real.log (250000 / 491831) := by
    rw [show ((491831 / 250000) : ℝ) = ((250000 / 491831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3421114413 / 1000000000) ≤ -Real.log (8169 / 250000) ∧
    -Real.log (8169 / 250000) ≤ (1710557209 / 500000000) := by
  have h := checkLog_sound (w := (3728 / 11897)) (n := 12)
    (lo := (648525693 / 1000000000)) (hi := (324262847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8169) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8169) = 1/(8169 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1710557209 / 500000000) (-3421114413 / 1000000000) (Real.log (8169 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338412091 / 500000000) ≤ -Real.log (1000000 / 1967619) ∧
    -Real.log (1000000 / 1967619) ≤ (676824183 / 1000000000) := by
  have h := checkLog_sound (w := (967619 / 2967619)) (n := 12)
    (lo := (338412091 / 500000000)) (hi := (676824183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967619 / 1000000) = 1/(1000000 / 1967619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338412091 / 500000000) (676824183 / 1000000000) (Real.log (1967619 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1967619 / 1000000) = -Real.log (1000000 / 1967619) := by
    rw [show ((1967619 / 1000000) : ℝ) = ((1000000 / 1967619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (686036689 / 200000000) ≤ -Real.log (32381 / 1000000) ∧
    -Real.log (32381 / 1000000) ≤ (68603669 / 20000000) := by
  have h := checkLog_sound (w := (30119 / 94881)) (n := 12)
    (lo := (26303789 / 40000000)) (hi := (328797363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32381) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32381) = 1/(32381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-68603669 / 20000000) (-686036689 / 200000000) (Real.log (32381 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2053237063 / 500000000) ≤ -Real.log (250000000000 / 15183051422927) ∧
    -Real.log (250000000000 / 15183051422927) ≤ (1026618533 / 250000000) := by
  have h := checkLog_sound (w := (7183051422927 / 23183051422927)) (n := 12)
    (lo := (320369113 / 500000000)) (hi := (640738227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15183051422927 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15183051422927 / 8000000000000) = 1/(250000000000 / 15183051422927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2053237063 / 500000000) (1026618533 / 250000000) (Real.log (15183051422927 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15183051422927 / 250000000000) = -Real.log (250000000000 / 15183051422927) := by
    rw [show ((15183051422927 / 250000000000) : ℝ) = ((250000000000 / 15183051422927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2057806487 / 500000000) ≤ -Real.log (250000000000 / 15322443004859) ∧
    -Real.log (250000000000 / 15322443004859) ≤ (205780649 / 50000000) := by
  have h := checkLog_sound (w := (7322443004859 / 23322443004859)) (n := 12)
    (lo := (324938537 / 500000000)) (hi := (25995083 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15322443004859 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15322443004859 / 8000000000000) = 1/(250000000000 / 15322443004859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2057806487 / 500000000) (205780649 / 50000000) (Real.log (15322443004859 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (15322443004859 / 250000000000) = -Real.log (250000000000 / 15322443004859) := by
    rw [show ((15322443004859 / 250000000000) : ℝ) = ((250000000000 / 15322443004859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (256111791 / 62500000) ≤ -Real.log (500000000000 / 30103501040519) ∧
    -Real.log (500000000000 / 30103501040519) ≤ (2048894331 / 500000000) := by
  have h := checkLog_sound (w := (14103501040519 / 46103501040519)) (n := 12)
    (lo := (158013189 / 250000000)) (hi := (632052757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30103501040519 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30103501040519 / 16000000000000) = 1/(500000000000 / 30103501040519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (256111791 / 62500000) (2048894331 / 500000000) (Real.log (30103501040519 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (30103501040519 / 500000000000) = -Real.log (500000000000 / 30103501040519) := by
    rw [show ((30103501040519 / 500000000000) : ℝ) = ((500000000000 / 30103501040519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4107007627 / 1000000000) ≤ -Real.log (500000000000 / 30382307526019) ∧
    -Real.log (500000000000 / 30382307526019) ≤ (4107007633 / 1000000000) := by
  have h := checkLog_sound (w := (14382307526019 / 46382307526019)) (n := 12)
    (lo := (641271727 / 1000000000)) (hi := (40079483 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30382307526019 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30382307526019 / 16000000000000) = 1/(500000000000 / 30382307526019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4107007627 / 1000000000) (4107007633 / 1000000000) (Real.log (30382307526019 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (30382307526019 / 500000000000) = -Real.log (500000000000 / 30382307526019) := by
    rw [show ((30382307526019 / 500000000000) : ℝ) = ((500000000000 / 30382307526019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0089

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0090Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0090
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

theorem reflection_log_1_neg : (336651573 / 500000000) ≤ -Real.log (12800 / 25097) ∧
    -Real.log (12800 / 25097) ≤ (673303147 / 1000000000) := by
  have h := checkLog_sound (w := (12297 / 37897)) (n := 12)
    (lo := (336651573 / 500000000)) (hi := (673303147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25097 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25097 / 12800) = 1/(12800 / 25097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (336651573 / 500000000) (673303147 / 1000000000) (Real.log (25097 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25097 / 12800) = -Real.log (12800 / 25097) := by
    rw [show ((25097 / 12800) : ℝ) = ((12800 / 25097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3236610277 / 1000000000) ≤ -Real.log (503 / 12800) ∧
    -Real.log (503 / 12800) ≤ (1618305141 / 500000000) := by
  have h := checkLog_sound (w := (297 / 1303)) (n := 12)
    (lo := (464021557 / 1000000000)) (hi := (232010779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 503) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 503) = 1/(503 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1618305141 / 500000000) (-3236610277 / 1000000000) (Real.log (503 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (336556931 / 500000000) ≤ -Real.log (51200 / 100369) ∧
    -Real.log (51200 / 100369) ≤ (673113863 / 1000000000) := by
  have h := checkLog_sound (w := (49169 / 151569)) (n := 12)
    (lo := (336556931 / 500000000)) (hi := (673113863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100369 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100369 / 51200) = 1/(51200 / 100369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (336556931 / 500000000) (673113863 / 1000000000) (Real.log (100369 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100369 / 51200) = -Real.log (51200 / 100369) := by
    rw [show ((100369 / 51200) : ℝ) = ((51200 / 100369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3227211247 / 1000000000) ≤ -Real.log (2031 / 51200) ∧
    -Real.log (2031 / 51200) ≤ (806802813 / 250000000) := by
  have h := checkLog_sound (w := (1169 / 5231)) (n := 12)
    (lo := (454622527 / 1000000000)) (hi := (7103477 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2031) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2031) = 1/(2031 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-806802813 / 250000000) (-3227211247 / 1000000000) (Real.log (2031 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (653057339 / 1000000000) ≤ -Real.log (6400 / 12297) ∧
    -Real.log (6400 / 12297) ≤ (32652867 / 50000000) := by
  have h := checkLog_sound (w := (5897 / 18697)) (n := 12)
    (lo := (653057339 / 1000000000)) (hi := (32652867 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12297 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12297 / 6400) = 1/(6400 / 12297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (653057339 / 1000000000) (32652867 / 50000000) (Real.log (12297 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12297 / 6400) = -Real.log (6400 / 12297) := by
    rw [show ((12297 / 6400) : ℝ) = ((6400 / 12297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2543463097 / 1000000000) ≤ -Real.log (503 / 6400) ∧
    -Real.log (503 / 6400) ≤ (2543463101 / 1000000000) := by
  have h := checkLog_sound (w := (297 / 1303)) (n := 12)
    (lo := (464021557 / 1000000000)) (hi := (232010779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 503) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 503) = 1/(503 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2543463101 / 1000000000) (-2543463097 / 1000000000) (Real.log (503 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (40791937 / 62500000) ≤ -Real.log (25600 / 49169) ∧
    -Real.log (25600 / 49169) ≤ (652670993 / 1000000000) := by
  have h := checkLog_sound (w := (23569 / 74769)) (n := 12)
    (lo := (40791937 / 62500000)) (hi := (652670993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49169 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49169 / 25600) = 1/(25600 / 49169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (40791937 / 62500000) (652670993 / 1000000000) (Real.log (49169 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49169 / 25600) = -Real.log (25600 / 49169) := by
    rw [show ((49169 / 25600) : ℝ) = ((25600 / 49169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2534064067 / 1000000000) ≤ -Real.log (2031 / 25600) ∧
    -Real.log (2031 / 25600) ≤ (2534064071 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 5231)) (n := 12)
    (lo := (454622527 / 1000000000)) (hi := (7103477 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2031) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2031) = 1/(2031 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2534064071 / 1000000000) (-2534064067 / 1000000000) (Real.log (2031 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (169167163 / 250000000) ≤ -Real.log (1000000 / 1967313) ∧
    -Real.log (1000000 / 1967313) ≤ (676668653 / 1000000000) := by
  have h := checkLog_sound (w := (967313 / 2967313)) (n := 12)
    (lo := (169167163 / 250000000)) (hi := (676668653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967313 / 1000000) = 1/(1000000 / 1967313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (169167163 / 250000000) (676668653 / 1000000000) (Real.log (1967313 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1967313 / 1000000) = -Real.log (1000000 / 1967313) := by
    rw [show ((1967313 / 1000000) : ℝ) = ((1000000 / 1967313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3420777831 / 1000000000) ≤ -Real.log (32687 / 1000000) ∧
    -Real.log (32687 / 1000000) ≤ (855194459 / 250000000) := by
  have h := checkLog_sound (w := (29813 / 95187)) (n := 12)
    (lo := (648189111 / 1000000000)) (hi := (81023639 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32687) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32687) = 1/(32687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-855194459 / 250000000) (-3420777831 / 1000000000) (Real.log (32687 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13536321 / 20000000) ≤ -Real.log (1000000 / 1967603) ∧
    -Real.log (1000000 / 1967603) ≤ (676816051 / 1000000000) := by
  have h := checkLog_sound (w := (967603 / 2967603)) (n := 12)
    (lo := (13536321 / 20000000)) (hi := (676816051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967603 / 1000000) = 1/(1000000 / 1967603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13536321 / 20000000) (676816051 / 1000000000) (Real.log (1967603 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1967603 / 1000000) = -Real.log (1000000 / 1967603) := by
    rw [show ((1967603 / 1000000) : ℝ) = ((1000000 / 1967603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (68593789 / 20000000) ≤ -Real.log (32397 / 1000000) ∧
    -Real.log (32397 / 1000000) ≤ (685937891 / 200000000) := by
  have h := checkLog_sound (w := (30103 / 94897)) (n := 12)
    (lo := (65710073 / 100000000)) (hi := (657100731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32397) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32397) = 1/(32397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-685937891 / 200000000) (-68593789 / 20000000) (Real.log (32397 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338262141 / 500000000) ≤ -Real.log (1000000 / 1967029) ∧
    -Real.log (1000000 / 1967029) ≤ (676524283 / 1000000000) := by
  have h := checkLog_sound (w := (967029 / 2967029)) (n := 12)
    (lo := (338262141 / 500000000)) (hi := (676524283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967029 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967029 / 1000000) = 1/(1000000 / 1967029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338262141 / 500000000) (676524283 / 1000000000) (Real.log (1967029 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1967029 / 1000000) = -Real.log (1000000 / 1967029) := by
    rw [show ((1967029 / 1000000) : ℝ) = ((1000000 / 1967029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3412126889 / 1000000000) ≤ -Real.log (32971 / 1000000) ∧
    -Real.log (32971 / 1000000) ≤ (1706063447 / 500000000) := by
  have h := checkLog_sound (w := (29529 / 95471)) (n := 12)
    (lo := (639538169 / 1000000000)) (hi := (63953817 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32971) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32971) = 1/(32971 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1706063447 / 500000000) (-3412126889 / 1000000000) (Real.log (32971 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (676674751 / 1000000000) ≤ -Real.log (40000 / 78693) ∧
    -Real.log (40000 / 78693) ≤ (10573043 / 15625000) := by
  have h := checkLog_sound (w := (38693 / 118693)) (n := 12)
    (lo := (676674751 / 1000000000)) (hi := (10573043 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78693 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78693 / 40000) = 1/(40000 / 78693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (676674751 / 1000000000) (10573043 / 15625000) (Real.log (78693 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78693 / 40000) = -Real.log (40000 / 78693) := by
    rw [show ((78693 / 40000) : ℝ) = ((40000 / 78693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3421145017 / 1000000000) ≤ -Real.log (1307 / 40000) ∧
    -Real.log (1307 / 40000) ≤ (1710572511 / 500000000) := by
  have h := checkLog_sound (w := (1193 / 3807)) (n := 12)
    (lo := (648556297 / 1000000000)) (hi := (324278149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1307) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2500 / 1307) = 1/(1307 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1710572511 / 500000000) (-3421145017 / 1000000000) (Real.log (1307 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4097446483 / 1000000000) ≤ -Real.log (500000000000 / 30093202190473) ∧
    -Real.log (500000000000 / 30093202190473) ≤ (4097446489 / 1000000000) := by
  have h := checkLog_sound (w := (14093202190473 / 46093202190473)) (n := 12)
    (lo := (631710583 / 1000000000)) (hi := (78963823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30093202190473 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30093202190473 / 16000000000000) = 1/(500000000000 / 30093202190473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4097446483 / 1000000000) (4097446489 / 1000000000) (Real.log (30093202190473 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (30093202190473 / 500000000000) = -Real.log (500000000000 / 30093202190473) := by
    rw [show ((30093202190473 / 500000000000) : ℝ) = ((500000000000 / 30093202190473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (8213011 / 2000000) ≤ -Real.log (31250000000 / 1897940974473) ∧
    -Real.log (31250000000 / 1897940974473) ≤ (2053252753 / 500000000) := by
  have h := checkLog_sound (w := (897940974473 / 2897940974473)) (n := 12)
    (lo := (400481 / 625000)) (hi := (640769601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1897940974473 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1897940974473 / 1000000000000) = 1/(31250000000 / 1897940974473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (8213011 / 2000000) (2053252753 / 500000000) (Real.log (1897940974473 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1897940974473 / 31250000000) = -Real.log (31250000000 / 1897940974473) := by
    rw [show ((1897940974473 / 31250000000) : ℝ) = ((31250000000 / 1897940974473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4088651171 / 1000000000) ≤ -Real.log (500000000000 / 29829683661399) ∧
    -Real.log (500000000000 / 29829683661399) ≤ (4088651177 / 1000000000) := by
  have h := checkLog_sound (w := (13829683661399 / 45829683661399)) (n := 12)
    (lo := (622915271 / 1000000000)) (hi := (77864409 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29829683661399 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(29829683661399 / 16000000000000) = 1/(500000000000 / 29829683661399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4088651171 / 1000000000) (4088651177 / 1000000000) (Real.log (29829683661399 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (29829683661399 / 500000000000) = -Real.log (500000000000 / 29829683661399) := by
    rw [show ((29829683661399 / 500000000000) : ℝ) = ((500000000000 / 29829683661399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (512227471 / 125000000) ≤ -Real.log (500000000000 / 30104437643459) ∧
    -Real.log (500000000000 / 30104437643459) ≤ (2048909887 / 500000000) := by
  have h := checkLog_sound (w := (14104437643459 / 46104437643459)) (n := 12)
    (lo := (158020967 / 250000000)) (hi := (632083869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30104437643459 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30104437643459 / 16000000000000) = 1/(500000000000 / 30104437643459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (512227471 / 125000000) (2048909887 / 500000000) (Real.log (30104437643459 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (30104437643459 / 500000000000) = -Real.log (500000000000 / 30104437643459) := by
    rw [show ((30104437643459 / 500000000000) : ℝ) = ((500000000000 / 30104437643459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0090

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0091Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0091
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

theorem reflection_log_1_neg : (336556931 / 500000000) ≤ -Real.log (51200 / 100369) ∧
    -Real.log (51200 / 100369) ≤ (673113863 / 1000000000) := by
  have h := checkLog_sound (w := (49169 / 151569)) (n := 12)
    (lo := (336556931 / 500000000)) (hi := (673113863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100369 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100369 / 51200) = 1/(51200 / 100369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (336556931 / 500000000) (673113863 / 1000000000) (Real.log (100369 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100369 / 51200) = -Real.log (51200 / 100369) := by
    rw [show ((100369 / 51200) : ℝ) = ((51200 / 100369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3227211247 / 1000000000) ≤ -Real.log (2031 / 51200) ∧
    -Real.log (2031 / 51200) ≤ (806802813 / 250000000) := by
  have h := checkLog_sound (w := (1169 / 5231)) (n := 12)
    (lo := (454622527 / 1000000000)) (hi := (7103477 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2031) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2031) = 1/(2031 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-806802813 / 250000000) (-3227211247 / 1000000000) (Real.log (2031 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (672924543 / 1000000000) ≤ -Real.log (1024 / 2007) ∧
    -Real.log (1024 / 2007) ≤ (5257223 / 7812500) := by
  have h := checkLog_sound (w := (983 / 3031)) (n := 12)
    (lo := (672924543 / 1000000000)) (hi := (5257223 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2007 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2007 / 1024) = 1/(1024 / 2007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (672924543 / 1000000000) (5257223 / 7812500) (Real.log (2007 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2007 / 1024) = -Real.log (1024 / 2007) := by
    rw [show ((2007 / 1024) : ℝ) = ((1024 / 2007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (402237467 / 125000000) ≤ -Real.log (41 / 1024) ∧
    -Real.log (41 / 1024) ≤ (3217899741 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(64 / 41) = 1/(41 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3217899741 / 1000000000) (-402237467 / 125000000) (Real.log (41 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (40791937 / 62500000) ≤ -Real.log (25600 / 49169) ∧
    -Real.log (25600 / 49169) ≤ (652670993 / 1000000000) := by
  have h := checkLog_sound (w := (23569 / 74769)) (n := 12)
    (lo := (40791937 / 62500000)) (hi := (652670993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49169 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49169 / 25600) = 1/(25600 / 49169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (40791937 / 62500000) (652670993 / 1000000000) (Real.log (49169 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49169 / 25600) = -Real.log (25600 / 49169) := by
    rw [show ((49169 / 25600) : ℝ) = ((25600 / 49169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2534064067 / 1000000000) ≤ -Real.log (2031 / 25600) ∧
    -Real.log (2031 / 25600) ≤ (2534064071 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 5231)) (n := 12)
    (lo := (454622527 / 1000000000)) (hi := (7103477 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2031) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2031) = 1/(2031 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2534064071 / 1000000000) (-2534064067 / 1000000000) (Real.log (2031 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (130456899 / 200000000) ≤ -Real.log (512 / 983) ∧
    -Real.log (512 / 983) ≤ (40767781 / 62500000) := by
  have h := checkLog_sound (w := (471 / 1495)) (n := 12)
    (lo := (130456899 / 200000000)) (hi := (40767781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983 / 512) = 1/(512 / 983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (130456899 / 200000000) (40767781 / 62500000) (Real.log (983 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (983 / 512) = -Real.log (512 / 983) := by
    rw [show ((983 / 512) : ℝ) = ((512 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (631188139 / 250000000) ≤ -Real.log (41 / 512) ∧
    -Real.log (41 / 512) ≤ (31559407 / 12500000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(64 / 41) = 1/(41 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-31559407 / 12500000) (-631188139 / 250000000) (Real.log (41 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (676522249 / 1000000000) ≤ -Real.log (40000 / 78681) ∧
    -Real.log (40000 / 78681) ≤ (2706089 / 4000000) := by
  have h := checkLog_sound (w := (38681 / 118681)) (n := 12)
    (lo := (676522249 / 1000000000)) (hi := (2706089 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78681 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78681 / 40000) = 1/(40000 / 78681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (676522249 / 1000000000) (2706089 / 4000000) (Real.log (78681 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (78681 / 40000) = -Real.log (40000 / 78681) := by
    rw [show ((78681 / 40000) : ℝ) = ((40000 / 78681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1706002789 / 500000000) ≤ -Real.log (1319 / 40000) ∧
    -Real.log (1319 / 40000) ≤ (3412005583 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 3819)) (n := 12)
    (lo := (319708429 / 500000000)) (hi := (639416859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1319) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2500 / 1319) = 1/(1319 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3412005583 / 1000000000) (-1706002789 / 500000000) (Real.log (1319 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16916729 / 25000000) ≤ -Real.log (500000 / 983657) ∧
    -Real.log (500000 / 983657) ≤ (676669161 / 1000000000) := by
  have h := checkLog_sound (w := (483657 / 1483657)) (n := 12)
    (lo := (16916729 / 25000000)) (hi := (676669161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983657 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983657 / 500000) = 1/(500000 / 983657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16916729 / 25000000) (676669161 / 1000000000) (Real.log (983657 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (983657 / 500000) = -Real.log (500000 / 983657) := by
    rw [show ((983657 / 500000) : ℝ) = ((500000 / 983657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (136832337 / 40000000) ≤ -Real.log (16343 / 500000) ∧
    -Real.log (16343 / 500000) ≤ (342080843 / 100000000) := by
  have h := checkLog_sound (w := (14907 / 47593)) (n := 12)
    (lo := (129643941 / 200000000)) (hi := (324109853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16343) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16343) = 1/(16343 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-342080843 / 100000000) (-136832337 / 40000000) (Real.log (16343 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338187149 / 500000000) ≤ -Real.log (500000 / 983367) ∧
    -Real.log (500000 / 983367) ≤ (676374299 / 1000000000) := by
  have h := checkLog_sound (w := (483367 / 1483367)) (n := 12)
    (lo := (338187149 / 500000000)) (hi := (676374299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983367 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983367 / 500000) = 1/(500000 / 983367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338187149 / 500000000) (676374299 / 1000000000) (Real.log (983367 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (983367 / 500000) = -Real.log (500000 / 983367) := by
    rw [show ((983367 / 500000) : ℝ) = ((500000 / 983367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1701609711 / 500000000) ≤ -Real.log (16633 / 500000) ∧
    -Real.log (16633 / 500000) ≤ (3403219427 / 1000000000) := by
  have h := checkLog_sound (w := (14617 / 47883)) (n := 12)
    (lo := (315315351 / 500000000)) (hi := (630630703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16633) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16633) = 1/(16633 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3403219427 / 1000000000) (-1701609711 / 500000000) (Real.log (16633 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67652479 / 100000000) ≤ -Real.log (100000 / 196703) ∧
    -Real.log (100000 / 196703) ≤ (676524791 / 1000000000) := by
  have h := checkLog_sound (w := (96703 / 296703)) (n := 12)
    (lo := (67652479 / 100000000)) (hi := (676524791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196703 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196703 / 100000) = 1/(100000 / 196703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67652479 / 100000000) (676524791 / 1000000000) (Real.log (196703 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (196703 / 100000) = -Real.log (100000 / 196703) := by
    rw [show ((196703 / 100000) : ℝ) = ((100000 / 196703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3412157219 / 1000000000) ≤ -Real.log (3297 / 100000) ∧
    -Real.log (3297 / 100000) ≤ (426519653 / 125000000) := by
  have h := checkLog_sound (w := (2953 / 9547)) (n := 12)
    (lo := (639568499 / 1000000000)) (hi := (1279137 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3297) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3297) = 1/(3297 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-426519653 / 125000000) (-3412157219 / 1000000000) (Real.log (3297 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2044263913 / 500000000) ≤ -Real.log (5000000000 / 298260045489) ∧
    -Real.log (5000000000 / 298260045489) ≤ (511065979 / 125000000) := by
  have h := checkLog_sound (w := (138260045489 / 458260045489)) (n := 12)
    (lo := (311395963 / 500000000)) (hi := (622791927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298260045489 / 160000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(298260045489 / 160000000000) = 1/(5000000000 / 298260045489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2044263913 / 500000000) (511065979 / 125000000) (Real.log (298260045489 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (298260045489 / 5000000000) = -Real.log (5000000000 / 298260045489) := by
    rw [show ((298260045489 / 5000000000) : ℝ) = ((5000000000 / 298260045489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (819495517 / 200000000) ≤ -Real.log (62500000000 / 3761767270391) ∧
    -Real.log (62500000000 / 3761767270391) ≤ (4097477591 / 1000000000) := by
  have h := checkLog_sound (w := (1761767270391 / 5761767270391)) (n := 12)
    (lo := (126348337 / 200000000)) (hi := (315870843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3761767270391 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3761767270391 / 2000000000000) = 1/(62500000000 / 3761767270391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (819495517 / 200000000) (4097477591 / 1000000000) (Real.log (3761767270391 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3761767270391 / 62500000000) = -Real.log (62500000000 / 3761767270391) := by
    rw [show ((3761767270391 / 62500000000) : ℝ) = ((62500000000 / 3761767270391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (101989843 / 25000000) ≤ -Real.log (125000000000 / 7390180664943) ∧
    -Real.log (125000000000 / 7390180664943) ≤ (2039796863 / 500000000) := by
  have h := checkLog_sound (w := (3390180664943 / 11390180664943)) (n := 12)
    (lo := (30692891 / 50000000)) (hi := (613857821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7390180664943 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7390180664943 / 4000000000000) = 1/(125000000000 / 7390180664943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (101989843 / 25000000) (2039796863 / 500000000) (Real.log (7390180664943 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7390180664943 / 125000000000) = -Real.log (125000000000 / 7390180664943) := by
    rw [show ((7390180664943 / 125000000000) : ℝ) = ((125000000000 / 7390180664943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (408868201 / 100000000) ≤ -Real.log (125000000000 / 7457650894753) ∧
    -Real.log (125000000000 / 7457650894753) ≤ (127771313 / 31250000) := by
  have h := checkLog_sound (w := (3457650894753 / 11457650894753)) (n := 12)
    (lo := (62294611 / 100000000)) (hi := (622946111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7457650894753 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7457650894753 / 4000000000000) = 1/(125000000000 / 7457650894753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (408868201 / 100000000) (127771313 / 31250000) (Real.log (7457650894753 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7457650894753 / 125000000000) = -Real.log (125000000000 / 7457650894753) := by
    rw [show ((7457650894753 / 125000000000) : ℝ) = ((125000000000 / 7457650894753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0091

end


