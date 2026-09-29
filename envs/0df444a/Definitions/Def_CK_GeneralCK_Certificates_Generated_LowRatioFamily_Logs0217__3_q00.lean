-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0217__3_q00
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0217__3_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:00:47.637007+00:00
-- url     : https://prove2.me/theorems/e4c6a574-87f3-4089-9615-08e421f1ae1e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0218, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0219) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0217 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0218, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0219) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0217 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13888_neg : (298850323 / 500000000) ≤ -Real.log (22003 / 40000) ∧
    -Real.log (22003 / 40000) ≤ (597700647 / 1000000000) := by
  have h := checkLog_sound (w := (17997 / 62003)) (n := 12)
    (lo := (298850323 / 500000000)) (hi := (597700647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 22003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 22003) = 1/(22003 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13888 : Bounds (-597700647 / 1000000000) (-298850323 / 500000000) (Real.log (22003 / 40000)) := by
  have h := reflection_log_13888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13889_neg : (45237763 / 200000000) ≤ -Real.log (1276107991 / 1600000000) ∧
    -Real.log (1276107991 / 1600000000) ≤ (14136801 / 62500000) := by
  have h := checkLog_sound (w := (323892009 / 2876107991)) (n := 12)
    (lo := (45237763 / 200000000)) (hi := (14136801 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1276107991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1276107991) = 1/(1276107991 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13889 : Bounds (-14136801 / 62500000) (-45237763 / 200000000) (Real.log (1276107991 / 1600000000)) := by
  have h := reflection_log_13889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13890_neg : (13931901 / 62500000) ≤ -Real.log (32007461199 / 40000000000) ∧
    -Real.log (32007461199 / 40000000000) ≤ (222910417 / 1000000000) := by
  have h := checkLog_sound (w := (7992538801 / 72007461199)) (n := 12)
    (lo := (13931901 / 62500000)) (hi := (222910417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 32007461199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 32007461199) = 1/(32007461199 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13890 : Bounds (-222910417 / 1000000000) (-13931901 / 62500000) (Real.log (32007461199 / 40000000000)) := by
  have h := reflection_log_13890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13891_neg : (961902221 / 1000000000) ≤ -Real.log (500000000000 / 1308334614237) ∧
    -Real.log (500000000000 / 1308334614237) ≤ (961902223 / 1000000000) := by
  have h := checkLog_sound (w := (308334614237 / 2308334614237)) (n := 12)
    (lo := (268755041 / 1000000000)) (hi := (134377521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308334614237 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1308334614237 / 1000000000000) = 1/(500000000000 / 1308334614237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13891 : Bounds (961902221 / 1000000000) (961902223 / 1000000000) (Real.log (1308334614237 / 500000000000)) := by
  have h := reflection_log_13891_neg
  have he : Real.log (1308334614237 / 500000000000) = -Real.log (500000000000 / 1308334614237) := by
    rw [show ((1308334614237 / 500000000000) : ℝ) = ((500000000000 / 1308334614237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13892_neg : (242303119 / 250000000) ≤ -Real.log (500000000000 / 1317933918103) ∧
    -Real.log (500000000000 / 1317933918103) ≤ (484606239 / 500000000) := by
  have h := checkLog_sound (w := (317933918103 / 2317933918103)) (n := 12)
    (lo := (17254081 / 62500000)) (hi := (276065297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317933918103 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1317933918103 / 1000000000000) = 1/(500000000000 / 1317933918103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13892 : Bounds (242303119 / 250000000) (484606239 / 500000000) (Real.log (1317933918103 / 500000000000)) := by
  have h := reflection_log_13892_neg
  have he : Real.log (1317933918103 / 500000000000) = -Real.log (500000000000 / 1317933918103) := by
    rw [show ((1317933918103 / 500000000000) : ℝ) = ((500000000000 / 1317933918103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13893_neg : (132283479 / 62500000) ≤ -Real.log (500000000000 / 4151162790697) ∧
    -Real.log (500000000000 / 4151162790697) ≤ (529133917 / 250000000) := by
  have h := checkLog_sound (w := (151162790697 / 8151162790697)) (n := 12)
    (lo := (9273531 / 250000000)) (hi := (296753 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4151162790697 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4151162790697 / 4000000000000) = 1/(500000000000 / 4151162790697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13893 : Bounds (132283479 / 62500000) (529133917 / 250000000) (Real.log (4151162790697 / 500000000000)) := by
  have h := reflection_log_13893_neg
  have he : Real.log (4151162790697 / 500000000000) = -Real.log (500000000000 / 4151162790697) := by
    rw [show ((4151162790697 / 500000000000) : ℝ) = ((500000000000 / 4151162790697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13894_neg : (2132266679 / 1000000000) ≤ -Real.log (125000000000 / 1054245283019) ∧
    -Real.log (125000000000 / 1054245283019) ≤ (2132266683 / 1000000000) := by
  have h := checkLog_sound (w := (54245283019 / 2054245283019)) (n := 12)
    (lo := (52825139 / 1000000000)) (hi := (2641257 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1054245283019 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1054245283019 / 1000000000000) = 1/(125000000000 / 1054245283019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13894 : Bounds (2132266679 / 1000000000) (2132266683 / 1000000000) (Real.log (1054245283019 / 125000000000)) := by
  have h := reflection_log_13894_neg
  have he : Real.log (1054245283019 / 125000000000) = -Real.log (125000000000 / 1054245283019) := by
    rw [show ((1054245283019 / 125000000000) : ℝ) = ((125000000000 / 1054245283019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13895_neg : (582774123 / 1000000000) ≤ -Real.log (1000 / 1791) ∧
    -Real.log (1000 / 1791) ≤ (145693531 / 250000000) := by
  have h := checkLog_sound (w := (791 / 2791)) (n := 12)
    (lo := (582774123 / 1000000000)) (hi := (145693531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1791 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1791 / 1000) = 1/(1000 / 1791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13895 : Bounds (582774123 / 1000000000) (145693531 / 250000000) (Real.log (1791 / 1000)) := by
  have h := reflection_log_13895_neg
  have he : Real.log (1791 / 1000) = -Real.log (1000 / 1791) := by
    rw [show ((1791 / 1000) : ℝ) = ((1000 / 1791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13896_neg : (62616841 / 40000000) ≤ -Real.log (209 / 1000) ∧
    -Real.log (209 / 1000) ≤ (391355257 / 250000000) := by
  have h := checkLog_sound (w := (41 / 459)) (n := 12)
    (lo := (35825333 / 200000000)) (hi := (89563333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 209) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 209) = 1/(209 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13896 : Bounds (-391355257 / 250000000) (-62616841 / 40000000) (Real.log (209 / 1000)) := by
  have h := reflection_log_13896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13897_neg : (790687 / 1000000000) ≤ -Real.log (1000000 / 1000791) ∧
    -Real.log (1000000 / 1000791) ≤ (24709 / 31250000) := by
  have h := checkLog_sound (w := (791 / 2000791)) (n := 12)
    (lo := (790687 / 1000000000)) (hi := (24709 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000791 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000791 / 1000000) = 1/(1000000 / 1000791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13897 : Bounds (790687 / 1000000000) (24709 / 31250000) (Real.log (1000791 / 1000000)) := by
  have h := reflection_log_13897_neg
  have he : Real.log (1000791 / 1000000) = -Real.log (1000000 / 1000791) := by
    rw [show ((1000791 / 1000000) : ℝ) = ((1000000 / 1000791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13898_neg : (791313 / 1000000000) ≤ -Real.log (999209 / 1000000) ∧
    -Real.log (999209 / 1000000) ≤ (395657 / 500000000) := by
  have h := checkLog_sound (w := (791 / 1999209)) (n := 12)
    (lo := (791313 / 1000000000)) (hi := (395657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999209) = 1/(999209 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13898 : Bounds (-395657 / 500000000) (-791313 / 1000000000) (Real.log (999209 / 1000000)) := by
  have h := reflection_log_13898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13899_neg : (371057911 / 1000000000) ≤ -Real.log (1000000 / 1449267) ∧
    -Real.log (1000000 / 1449267) ≤ (46382239 / 125000000) := by
  have h := checkLog_sound (w := (449267 / 2449267)) (n := 12)
    (lo := (371057911 / 1000000000)) (hi := (46382239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1449267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1449267 / 1000000) = 1/(1000000 / 1449267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13899 : Bounds (371057911 / 1000000000) (46382239 / 125000000) (Real.log (1449267 / 1000000)) := by
  have h := reflection_log_13899_neg
  have he : Real.log (1449267 / 1000000) = -Real.log (1000000 / 1449267) := by
    rw [show ((1449267 / 1000000) : ℝ) = ((1000000 / 1449267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13900_neg : (14912629 / 25000000) ≤ -Real.log (550733 / 1000000) ∧
    -Real.log (550733 / 1000000) ≤ (596505161 / 1000000000) := by
  have h := checkLog_sound (w := (449267 / 1550733)) (n := 12)
    (lo := (14912629 / 25000000)) (hi := (596505161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 550733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 550733) = 1/(550733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13900 : Bounds (-596505161 / 1000000000) (-14912629 / 25000000) (Real.log (550733 / 1000000)) := by
  have h := reflection_log_13900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13901_neg : (186538791 / 500000000) ≤ -Real.log (1000000 / 1452197) ∧
    -Real.log (1000000 / 1452197) ≤ (373077583 / 1000000000) := by
  have h := checkLog_sound (w := (452197 / 2452197)) (n := 12)
    (lo := (186538791 / 500000000)) (hi := (373077583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1452197 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1452197 / 1000000) = 1/(1000000 / 1452197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13901 : Bounds (186538791 / 500000000) (373077583 / 1000000000) (Real.log (1452197 / 1000000)) := by
  have h := reflection_log_13901_neg
  have he : Real.log (1452197 / 1000000) = -Real.log (1000000 / 1452197) := by
    rw [show ((1452197 / 1000000) : ℝ) = ((1000000 / 1452197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13902_neg : (120367909 / 200000000) ≤ -Real.log (547803 / 1000000) ∧
    -Real.log (547803 / 1000000) ≤ (300919773 / 500000000) := by
  have h := checkLog_sound (w := (452197 / 1547803)) (n := 12)
    (lo := (120367909 / 200000000)) (hi := (300919773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 547803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 547803) = 1/(547803 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13902 : Bounds (-300919773 / 500000000) (-120367909 / 200000000) (Real.log (547803 / 1000000)) := by
  have h := reflection_log_13902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13903_neg : (228761963 / 1000000000) ≤ -Real.log (795517873191 / 1000000000000) ∧
    -Real.log (795517873191 / 1000000000000) ≤ (57190491 / 250000000) := by
  have h := checkLog_sound (w := (204482126809 / 1795517873191)) (n := 12)
    (lo := (228761963 / 1000000000)) (hi := (57190491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 795517873191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 795517873191) = 1/(795517873191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13903 : Bounds (-57190491 / 250000000) (-228761963 / 1000000000) (Real.log (795517873191 / 1000000000000)) := by
  have h := reflection_log_13903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13904_neg : (225447249 / 1000000000) ≤ -Real.log (798159162711 / 1000000000000) ∧
    -Real.log (798159162711 / 1000000000000) ≤ (901789 / 4000000) := by
  have h := checkLog_sound (w := (201840837289 / 1798159162711)) (n := 12)
    (lo := (225447249 / 1000000000)) (hi := (901789 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 798159162711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 798159162711) = 1/(798159162711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13904 : Bounds (-901789 / 4000000) (-225447249 / 1000000000) (Real.log (798159162711 / 1000000000000)) := by
  have h := reflection_log_13904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13905_neg : (967563071 / 1000000000) ≤ -Real.log (500000000000 / 1315761902773) ∧
    -Real.log (500000000000 / 1315761902773) ≤ (967563073 / 1000000000) := by
  have h := checkLog_sound (w := (315761902773 / 2315761902773)) (n := 12)
    (lo := (274415891 / 1000000000)) (hi := (68603973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1315761902773 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1315761902773 / 1000000000000) = 1/(500000000000 / 1315761902773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13905 : Bounds (967563071 / 1000000000) (967563073 / 1000000000) (Real.log (1315761902773 / 500000000000)) := by
  have h := reflection_log_13905_neg
  have he : Real.log (1315761902773 / 500000000000) = -Real.log (500000000000 / 1315761902773) := by
    rw [show ((1315761902773 / 500000000000) : ℝ) = ((500000000000 / 1315761902773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13906_neg : (974917127 / 1000000000) ≤ -Real.log (500000000000 / 1325473756077) ∧
    -Real.log (500000000000 / 1325473756077) ≤ (974917129 / 1000000000) := by
  have h := checkLog_sound (w := (325473756077 / 2325473756077)) (n := 12)
    (lo := (281769947 / 1000000000)) (hi := (70442487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325473756077 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1325473756077 / 1000000000000) = 1/(500000000000 / 1325473756077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13906 : Bounds (974917127 / 1000000000) (974917129 / 1000000000) (Real.log (1325473756077 / 500000000000)) := by
  have h := reflection_log_13906_neg
  have he : Real.log (1325473756077 / 500000000000) = -Real.log (500000000000 / 1325473756077) := by
    rw [show ((1325473756077 / 500000000000) : ℝ) = ((500000000000 / 1325473756077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13907_neg : (2132266679 / 1000000000) ≤ -Real.log (20000000000 / 168679245283) ∧
    -Real.log (20000000000 / 168679245283) ≤ (2132266683 / 1000000000) := by
  have h := checkLog_sound (w := (8679245283 / 328679245283)) (n := 12)
    (lo := (52825139 / 1000000000)) (hi := (2641257 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168679245283 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(168679245283 / 160000000000) = 1/(20000000000 / 168679245283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13907 : Bounds (2132266679 / 1000000000) (2132266683 / 1000000000) (Real.log (168679245283 / 20000000000)) := by
  have h := reflection_log_13907_neg
  have he : Real.log (168679245283 / 20000000000) = -Real.log (20000000000 / 168679245283) := by
    rw [show ((168679245283 / 20000000000) : ℝ) = ((20000000000 / 168679245283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13908_neg : (537048787 / 250000000) ≤ -Real.log (31250000000 / 267793062201) ∧
    -Real.log (31250000000 / 267793062201) ≤ (134262197 / 62500000) := by
  have h := checkLog_sound (w := (17793062201 / 517793062201)) (n := 12)
    (lo := (8594201 / 125000000)) (hi := (68753609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267793062201 / 250000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(267793062201 / 250000000000) = 1/(31250000000 / 267793062201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13908 : Bounds (537048787 / 250000000) (134262197 / 62500000) (Real.log (267793062201 / 31250000000)) := by
  have h := reflection_log_13908_neg
  have he : Real.log (267793062201 / 31250000000) = -Real.log (31250000000 / 267793062201) := by
    rw [show ((267793062201 / 31250000000) : ℝ) = ((31250000000 / 267793062201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13909_neg : (584447763 / 1000000000) ≤ -Real.log (500 / 897) ∧
    -Real.log (500 / 897) ≤ (146111941 / 250000000) := by
  have h := checkLog_sound (w := (397 / 1397)) (n := 12)
    (lo := (584447763 / 1000000000)) (hi := (146111941 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897 / 500) = 1/(500 / 897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13909 : Bounds (584447763 / 1000000000) (146111941 / 250000000) (Real.log (897 / 500)) := by
  have h := reflection_log_13909_neg
  have he : Real.log (897 / 500) = -Real.log (500 / 897) := by
    rw [show ((897 / 500) : ℝ) = ((500 / 897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13910_neg : (1579879109 / 1000000000) ≤ -Real.log (103 / 500) ∧
    -Real.log (103 / 500) ≤ (197484889 / 125000000) := by
  have h := checkLog_sound (w := (11 / 114)) (n := 12)
    (lo := (193584749 / 1000000000)) (hi := (774339 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 103) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 103) = 1/(103 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13910 : Bounds (-197484889 / 125000000) (-1579879109 / 1000000000) (Real.log (103 / 500)) := by
  have h := reflection_log_13910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13911_neg : (198421 / 250000000) ≤ -Real.log (500000 / 500397) ∧
    -Real.log (500000 / 500397) ≤ (158737 / 200000000) := by
  have h := checkLog_sound (w := (397 / 1000397)) (n := 12)
    (lo := (198421 / 250000000)) (hi := (158737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500397 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500397 / 500000) = 1/(500000 / 500397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13911 : Bounds (198421 / 250000000) (158737 / 200000000) (Real.log (500397 / 500000)) := by
  have h := reflection_log_13911_neg
  have he : Real.log (500397 / 500000) = -Real.log (500000 / 500397) := by
    rw [show ((500397 / 500000) : ℝ) = ((500000 / 500397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13912_neg : (158863 / 200000000) ≤ -Real.log (499603 / 500000) ∧
    -Real.log (499603 / 500000) ≤ (198579 / 250000000) := by
  have h := checkLog_sound (w := (397 / 999603)) (n := 12)
    (lo := (158863 / 200000000)) (hi := (198579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499603) = 1/(499603 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13912 : Bounds (-198579 / 250000000) (-158863 / 200000000) (Real.log (499603 / 500000)) := by
  have h := reflection_log_13912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13913_neg : (93156093 / 250000000) ≤ -Real.log (1000000 / 1451539) ∧
    -Real.log (1000000 / 1451539) ≤ (372624373 / 1000000000) := by
  have h := checkLog_sound (w := (451539 / 2451539)) (n := 12)
    (lo := (93156093 / 250000000)) (hi := (372624373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451539 / 1000000) = 1/(1000000 / 1451539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13913 : Bounds (93156093 / 250000000) (372624373 / 1000000000) (Real.log (1451539 / 1000000)) := by
  have h := reflection_log_13913_neg
  have he : Real.log (1451539 / 1000000) = -Real.log (1000000 / 1451539) := by
    rw [show ((1451539 / 1000000) : ℝ) = ((1000000 / 1451539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13914_neg : (4692493 / 7812500) ≤ -Real.log (548461 / 1000000) ∧
    -Real.log (548461 / 1000000) ≤ (120127821 / 200000000) := by
  have h := checkLog_sound (w := (451539 / 1548461)) (n := 12)
    (lo := (4692493 / 7812500)) (hi := (120127821 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 548461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 548461) = 1/(548461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13914 : Bounds (-120127821 / 200000000) (-4692493 / 7812500) (Real.log (548461 / 1000000)) := by
  have h := reflection_log_13914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13915_neg : (2926941 / 7812500) ≤ -Real.log (12500 / 18181) ∧
    -Real.log (12500 / 18181) ≤ (374648449 / 1000000000) := by
  have h := checkLog_sound (w := (5681 / 30681)) (n := 12)
    (lo := (2926941 / 7812500)) (hi := (374648449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18181 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18181 / 12500) = 1/(12500 / 18181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13915 : Bounds (2926941 / 7812500) (374648449 / 1000000000) (Real.log (18181 / 12500)) := by
  have h := reflection_log_13915_neg
  have he : Real.log (18181 / 12500) = -Real.log (12500 / 18181) := by
    rw [show ((18181 / 12500) : ℝ) = ((12500 / 18181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13916_neg : (60601581 / 100000000) ≤ -Real.log (6819 / 12500) ∧
    -Real.log (6819 / 12500) ≤ (606015811 / 1000000000) := by
  have h := checkLog_sound (w := (5681 / 19319)) (n := 12)
    (lo := (60601581 / 100000000)) (hi := (606015811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 6819) = 1/(6819 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13916 : Bounds (-606015811 / 1000000000) (-60601581 / 100000000) (Real.log (6819 / 12500)) := by
  have h := reflection_log_13916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13917_neg : (115683681 / 500000000) ≤ -Real.log (123976239 / 156250000) ∧
    -Real.log (123976239 / 156250000) ≤ (231367363 / 1000000000) := by
  have h := checkLog_sound (w := (32273761 / 280226239)) (n := 12)
    (lo := (115683681 / 500000000)) (hi := (231367363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 123976239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 123976239) = 1/(123976239 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13917 : Bounds (-231367363 / 1000000000) (-115683681 / 500000000) (Real.log (123976239 / 156250000)) := by
  have h := reflection_log_13917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13918_neg : (228014731 / 1000000000) ≤ -Real.log (796112531479 / 1000000000000) ∧
    -Real.log (796112531479 / 1000000000000) ≤ (57003683 / 250000000) := by
  have h := checkLog_sound (w := (203887468521 / 1796112531479)) (n := 12)
    (lo := (228014731 / 1000000000)) (hi := (57003683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 796112531479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 796112531479) = 1/(796112531479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13918 : Bounds (-57003683 / 250000000) (-228014731 / 1000000000) (Real.log (796112531479 / 1000000000000)) := by
  have h := reflection_log_13918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13919_neg : (973263477 / 1000000000) ≤ -Real.log (500000000000 / 1323283697473) ∧
    -Real.log (500000000000 / 1323283697473) ≤ (973263479 / 1000000000) := by
  have h := checkLog_sound (w := (323283697473 / 2323283697473)) (n := 12)
    (lo := (280116297 / 1000000000)) (hi := (140058149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323283697473 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1323283697473 / 1000000000000) = 1/(500000000000 / 1323283697473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13919 : Bounds (973263477 / 1000000000) (973263479 / 1000000000) (Real.log (1323283697473 / 500000000000)) := by
  have h := reflection_log_13919_neg
  have he : Real.log (1323283697473 / 500000000000) = -Real.log (500000000000 / 1323283697473) := by
    rw [show ((1323283697473 / 500000000000) : ℝ) = ((500000000000 / 1323283697473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13920_neg : (490332129 / 500000000) ≤ -Real.log (500000000000 / 1333113359731) ∧
    -Real.log (500000000000 / 1333113359731) ≤ (49033213 / 50000000) := by
  have h := checkLog_sound (w := (333113359731 / 2333113359731)) (n := 12)
    (lo := (143758539 / 500000000)) (hi := (287517079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333113359731 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1333113359731 / 1000000000000) = 1/(500000000000 / 1333113359731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13920 : Bounds (490332129 / 500000000) (49033213 / 50000000) (Real.log (1333113359731 / 500000000000)) := by
  have h := reflection_log_13920_neg
  have he : Real.log (1333113359731 / 500000000000) = -Real.log (500000000000 / 1333113359731) := by
    rw [show ((1333113359731 / 500000000000) : ℝ) = ((500000000000 / 1333113359731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13921_neg : (537048787 / 250000000) ≤ -Real.log (100000000000 / 856937799043) ∧
    -Real.log (100000000000 / 856937799043) ≤ (134262197 / 62500000) := by
  have h := checkLog_sound (w := (56937799043 / 1656937799043)) (n := 12)
    (lo := (8594201 / 125000000)) (hi := (68753609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856937799043 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(856937799043 / 800000000000) = 1/(100000000000 / 856937799043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13921 : Bounds (537048787 / 250000000) (134262197 / 62500000) (Real.log (856937799043 / 100000000000)) := by
  have h := reflection_log_13921_neg
  have he : Real.log (856937799043 / 100000000000) = -Real.log (100000000000 / 856937799043) := by
    rw [show ((856937799043 / 100000000000) : ℝ) = ((100000000000 / 856937799043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13922_neg : (270540859 / 125000000) ≤ -Real.log (500000000000 / 4354368932039) ∧
    -Real.log (500000000000 / 4354368932039) ≤ (541081719 / 250000000) := by
  have h := checkLog_sound (w := (354368932039 / 8354368932039)) (n := 12)
    (lo := (21221333 / 250000000)) (hi := (84885333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4354368932039 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4354368932039 / 4000000000000) = 1/(500000000000 / 4354368932039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13922 : Bounds (270540859 / 125000000) (541081719 / 250000000) (Real.log (4354368932039 / 500000000000)) := by
  have h := reflection_log_13922_neg
  have he : Real.log (4354368932039 / 500000000000) = -Real.log (500000000000 / 4354368932039) := by
    rw [show ((4354368932039 / 500000000000) : ℝ) = ((500000000000 / 4354368932039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13923_neg : (586118607 / 1000000000) ≤ -Real.log (1000 / 1797) ∧
    -Real.log (1000 / 1797) ≤ (36632413 / 62500000) := by
  have h := checkLog_sound (w := (797 / 2797)) (n := 12)
    (lo := (586118607 / 1000000000)) (hi := (36632413 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1797 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1797 / 1000) = 1/(1000 / 1797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13923 : Bounds (586118607 / 1000000000) (36632413 / 62500000) (Real.log (1797 / 1000)) := by
  have h := reflection_log_13923_neg
  have he : Real.log (1797 / 1000) = -Real.log (1000 / 1797) := by
    rw [show ((1797 / 1000) : ℝ) = ((1000 / 1797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13924_neg : (797274649 / 500000000) ≤ -Real.log (203 / 1000) ∧
    -Real.log (203 / 1000) ≤ (1594549301 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 453)) (n := 12)
    (lo := (104127469 / 500000000)) (hi := (208254939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 203) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 203) = 1/(203 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13924 : Bounds (-1594549301 / 1000000000) (-797274649 / 500000000) (Real.log (203 / 1000)) := by
  have h := reflection_log_13924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13925_neg : (398341 / 500000000) ≤ -Real.log (1000000 / 1000797) ∧
    -Real.log (1000000 / 1000797) ≤ (796683 / 1000000000) := by
  have h := checkLog_sound (w := (797 / 2000797)) (n := 12)
    (lo := (398341 / 500000000)) (hi := (796683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000797 / 1000000) = 1/(1000000 / 1000797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13925 : Bounds (398341 / 500000000) (796683 / 1000000000) (Real.log (1000797 / 1000000)) := by
  have h := reflection_log_13925_neg
  have he : Real.log (1000797 / 1000000) = -Real.log (1000000 / 1000797) := by
    rw [show ((1000797 / 1000000) : ℝ) = ((1000000 / 1000797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13926_neg : (797317 / 1000000000) ≤ -Real.log (999203 / 1000000) ∧
    -Real.log (999203 / 1000000) ≤ (398659 / 500000000) := by
  have h := checkLog_sound (w := (797 / 1999203)) (n := 12)
    (lo := (797317 / 1000000000)) (hi := (398659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999203) = 1/(999203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13926 : Bounds (-398659 / 500000000) (-797317 / 1000000000) (Real.log (999203 / 1000000)) := by
  have h := reflection_log_13926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13927_neg : (14967783 / 40000000) ≤ -Real.log (50000 / 72691) ∧
    -Real.log (50000 / 72691) ≤ (23387161 / 62500000) := by
  have h := checkLog_sound (w := (22691 / 122691)) (n := 12)
    (lo := (14967783 / 40000000)) (hi := (23387161 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72691 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72691 / 50000) = 1/(50000 / 72691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13927 : Bounds (14967783 / 40000000) (23387161 / 62500000) (Real.log (72691 / 50000)) := by
  have h := reflection_log_13927_neg
  have he : Real.log (72691 / 50000) = -Real.log (50000 / 72691) := by
    rw [show ((72691 / 50000) : ℝ) = ((50000 / 72691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13928_neg : (604806687 / 1000000000) ≤ -Real.log (27309 / 50000) ∧
    -Real.log (27309 / 50000) ≤ (18900209 / 31250000) := by
  have h := checkLog_sound (w := (22691 / 77309)) (n := 12)
    (lo := (604806687 / 1000000000)) (hi := (18900209 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 27309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 27309) = 1/(27309 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13928 : Bounds (-18900209 / 31250000) (-604806687 / 1000000000) (Real.log (27309 / 50000)) := by
  have h := reflection_log_13928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13929_neg : (376223029 / 1000000000) ≤ -Real.log (250000 / 364193) ∧
    -Real.log (250000 / 364193) ≤ (37622303 / 100000000) := by
  have h := checkLog_sound (w := (114193 / 614193)) (n := 12)
    (lo := (376223029 / 1000000000)) (hi := (37622303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364193 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364193 / 250000) = 1/(250000 / 364193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13929 : Bounds (376223029 / 1000000000) (37622303 / 100000000) (Real.log (364193 / 250000)) := by
  have h := reflection_log_13929_neg
  have he : Real.log (364193 / 250000) = -Real.log (250000 / 364193) := by
    rw [show ((364193 / 250000) : ℝ) = ((250000 / 364193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13930_neg : (610226157 / 1000000000) ≤ -Real.log (135807 / 250000) ∧
    -Real.log (135807 / 250000) ≤ (305113079 / 500000000) := by
  have h := checkLog_sound (w := (114193 / 385807)) (n := 12)
    (lo := (610226157 / 1000000000)) (hi := (305113079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 135807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 135807) = 1/(135807 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13930 : Bounds (-305113079 / 500000000) (-610226157 / 1000000000) (Real.log (135807 / 250000)) := by
  have h := reflection_log_13930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13931_neg : (29250391 / 125000000) ≤ -Real.log (49459958751 / 62500000000) ∧
    -Real.log (49459958751 / 62500000000) ≤ (234003129 / 1000000000) := by
  have h := checkLog_sound (w := (13040041249 / 111959958751)) (n := 12)
    (lo := (29250391 / 125000000)) (hi := (234003129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 49459958751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 49459958751) = 1/(49459958751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13931 : Bounds (-234003129 / 1000000000) (-29250391 / 125000000) (Real.log (49459958751 / 62500000000)) := by
  have h := reflection_log_13931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13932_neg : (14413257 / 62500000) ≤ -Real.log (1985118519 / 2500000000) ∧
    -Real.log (1985118519 / 2500000000) ≤ (230612113 / 1000000000) := by
  have h := checkLog_sound (w := (514881481 / 4485118519)) (n := 12)
    (lo := (14413257 / 62500000)) (hi := (230612113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1985118519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1985118519) = 1/(1985118519 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13932 : Bounds (-230612113 / 1000000000) (-14413257 / 62500000) (Real.log (1985118519 / 2500000000)) := by
  have h := reflection_log_13932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13933_neg : (979001261 / 1000000000) ≤ -Real.log (20000000000 / 53235929547) ∧
    -Real.log (20000000000 / 53235929547) ≤ (979001263 / 1000000000) := by
  have h := checkLog_sound (w := (13235929547 / 93235929547)) (n := 12)
    (lo := (285854081 / 1000000000)) (hi := (142927041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53235929547 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(53235929547 / 40000000000) = 1/(20000000000 / 53235929547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13933 : Bounds (979001261 / 1000000000) (979001263 / 1000000000) (Real.log (53235929547 / 20000000000)) := by
  have h := reflection_log_13933_neg
  have he : Real.log (53235929547 / 20000000000) = -Real.log (20000000000 / 53235929547) := by
    rw [show ((53235929547 / 20000000000) : ℝ) = ((20000000000 / 53235929547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13934_neg : (493224593 / 500000000) ≤ -Real.log (500000000000 / 1340847673537) ∧
    -Real.log (500000000000 / 1340847673537) ≤ (246612297 / 250000000) := by
  have h := checkLog_sound (w := (340847673537 / 2340847673537)) (n := 12)
    (lo := (146651003 / 500000000)) (hi := (293302007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1340847673537 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1340847673537 / 1000000000000) = 1/(500000000000 / 1340847673537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13934 : Bounds (493224593 / 500000000) (246612297 / 250000000) (Real.log (1340847673537 / 500000000000)) := by
  have h := reflection_log_13934_neg
  have he : Real.log (1340847673537 / 500000000000) = -Real.log (500000000000 / 1340847673537) := by
    rw [show ((1340847673537 / 500000000000) : ℝ) = ((500000000000 / 1340847673537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13935_neg : (270540859 / 125000000) ≤ -Real.log (250000000000 / 2177184466019) ∧
    -Real.log (250000000000 / 2177184466019) ≤ (541081719 / 250000000) := by
  have h := checkLog_sound (w := (177184466019 / 4177184466019)) (n := 12)
    (lo := (21221333 / 250000000)) (hi := (84885333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2177184466019 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2177184466019 / 2000000000000) = 1/(250000000000 / 2177184466019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13935 : Bounds (270540859 / 125000000) (541081719 / 250000000) (Real.log (2177184466019 / 250000000000)) := by
  have h := reflection_log_13935_neg
  have he : Real.log (2177184466019 / 250000000000) = -Real.log (250000000000 / 2177184466019) := by
    rw [show ((2177184466019 / 250000000000) : ℝ) = ((250000000000 / 2177184466019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13936_neg : (1090333953 / 500000000) ≤ -Real.log (100000000000 / 885221674877) ∧
    -Real.log (100000000000 / 885221674877) ≤ (218066791 / 100000000) := by
  have h := checkLog_sound (w := (85221674877 / 1685221674877)) (n := 12)
    (lo := (50613183 / 500000000)) (hi := (101226367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885221674877 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(885221674877 / 800000000000) = 1/(100000000000 / 885221674877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13936 : Bounds (1090333953 / 500000000) (218066791 / 100000000) (Real.log (885221674877 / 100000000000)) := by
  have h := reflection_log_13936_neg
  have he : Real.log (885221674877 / 100000000000) = -Real.log (100000000000 / 885221674877) := by
    rw [show ((885221674877 / 100000000000) : ℝ) = ((100000000000 / 885221674877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13937_neg : (73473333 / 125000000) ≤ -Real.log (5 / 9) ∧
    -Real.log (5 / 9) ≤ (117557333 / 200000000) := by
  have h := checkLog_sound (w := (2 / 7)) (n := 12)
    (lo := (73473333 / 125000000)) (hi := (117557333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9 / 5) = 1/(5 / 9) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13937 : Bounds (73473333 / 125000000) (117557333 / 200000000) (Real.log (9 / 5)) := by
  have h := reflection_log_13937_neg
  have he : Real.log (9 / 5) = -Real.log (5 / 9) := by
    rw [show ((9 / 5) : ℝ) = ((5 / 9) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13938_neg : (1609437911 / 1000000000) ≤ -Real.log (1 / 5) ∧
    -Real.log (1 / 5) ≤ (804718957 / 500000000) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(5 / 4) = 1/(1 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13938 : Bounds (-804718957 / 500000000) (-1609437911 / 1000000000) (Real.log (1 / 5)) := by
  have h := reflection_log_13938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13939_neg : (2499 / 3125000) ≤ -Real.log (1250 / 1251) ∧
    -Real.log (1250 / 1251) ≤ (799681 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 2501)) (n := 12)
    (lo := (2499 / 3125000)) (hi := (799681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251 / 1250) = 1/(1250 / 1251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13939 : Bounds (2499 / 3125000) (799681 / 1000000000) (Real.log (1251 / 1250)) := by
  have h := reflection_log_13939_neg
  have he : Real.log (1251 / 1250) = -Real.log (1250 / 1251) := by
    rw [show ((1251 / 1250) : ℝ) = ((1250 / 1251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13940_neg : (2501 / 3125000) ≤ -Real.log (1249 / 1250) ∧
    -Real.log (1249 / 1250) ≤ (800321 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 2499)) (n := 12)
    (lo := (2501 / 3125000)) (hi := (800321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1249) = 1/(1249 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13940 : Bounds (-800321 / 1000000000) (-2501 / 3125000) (Real.log (1249 / 1250)) := by
  have h := reflection_log_13940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13941_neg : (375769183 / 1000000000) ≤ -Real.log (1000000 / 1456111) ∧
    -Real.log (1000000 / 1456111) ≤ (11742787 / 31250000) := by
  have h := checkLog_sound (w := (456111 / 2456111)) (n := 12)
    (lo := (375769183 / 1000000000)) (hi := (11742787 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1456111 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1456111 / 1000000) = 1/(1000000 / 1456111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13941 : Bounds (375769183 / 1000000000) (11742787 / 31250000) (Real.log (1456111 / 1000000)) := by
  have h := reflection_log_13941_neg
  have he : Real.log (1456111 / 1000000) = -Real.log (1000000 / 1456111) := by
    rw [show ((1456111 / 1000000) : ℝ) = ((1000000 / 1456111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13942_neg : (609010097 / 1000000000) ≤ -Real.log (543889 / 1000000) ∧
    -Real.log (543889 / 1000000) ≤ (304505049 / 500000000) := by
  have h := checkLog_sound (w := (456111 / 1543889)) (n := 12)
    (lo := (609010097 / 1000000000)) (hi := (304505049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 543889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 543889) = 1/(543889 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13942 : Bounds (-304505049 / 500000000) (-609010097 / 1000000000) (Real.log (543889 / 1000000)) := by
  have h := reflection_log_13942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13943_neg : (377801987 / 1000000000) ≤ -Real.log (500000 / 729537) ∧
    -Real.log (500000 / 729537) ≤ (94450497 / 250000000) := by
  have h := checkLog_sound (w := (229537 / 1229537)) (n := 12)
    (lo := (377801987 / 1000000000)) (hi := (94450497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729537 / 500000) = 1/(500000 / 729537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13943 : Bounds (377801987 / 1000000000) (94450497 / 250000000) (Real.log (729537 / 500000)) := by
  have h := reflection_log_13943_neg
  have he : Real.log (729537 / 500000) = -Real.log (500000 / 729537) := by
    rw [show ((729537 / 500000) : ℝ) = ((500000 / 729537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13944_neg : (614472793 / 1000000000) ≤ -Real.log (270463 / 500000) ∧
    -Real.log (270463 / 500000) ≤ (307236397 / 500000000) := by
  have h := checkLog_sound (w := (229537 / 770463)) (n := 12)
    (lo := (614472793 / 1000000000)) (hi := (307236397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 270463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 270463) = 1/(270463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13944 : Bounds (-307236397 / 500000000) (-614472793 / 1000000000) (Real.log (270463 / 500000)) := by
  have h := reflection_log_13944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13945_neg : (47334161 / 200000000) ≤ -Real.log (197312765631 / 250000000000) ∧
    -Real.log (197312765631 / 250000000000) ≤ (118335403 / 500000000) := by
  have h := checkLog_sound (w := (52687234369 / 447312765631)) (n := 12)
    (lo := (47334161 / 200000000)) (hi := (118335403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 197312765631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 197312765631) = 1/(197312765631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13945 : Bounds (-118335403 / 500000000) (-47334161 / 200000000) (Real.log (197312765631 / 250000000000)) := by
  have h := reflection_log_13945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13946_neg : (233240913 / 1000000000) ≤ -Real.log (791962755679 / 1000000000000) ∧
    -Real.log (791962755679 / 1000000000000) ≤ (116620457 / 500000000) := by
  have h := checkLog_sound (w := (208037244321 / 1791962755679)) (n := 12)
    (lo := (233240913 / 1000000000)) (hi := (116620457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 791962755679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 791962755679) = 1/(791962755679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13946 : Bounds (-116620457 / 500000000) (-233240913 / 1000000000) (Real.log (791962755679 / 1000000000000)) := by
  have h := reflection_log_13946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13947_neg : (984779279 / 1000000000) ≤ -Real.log (125000000000 / 334652612941) ∧
    -Real.log (125000000000 / 334652612941) ≤ (984779281 / 1000000000) := by
  have h := checkLog_sound (w := (84652612941 / 584652612941)) (n := 12)
    (lo := (291632099 / 1000000000)) (hi := (2916321 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334652612941 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(334652612941 / 250000000000) = 1/(125000000000 / 334652612941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13947 : Bounds (984779279 / 1000000000) (984779281 / 1000000000) (Real.log (334652612941 / 125000000000)) := by
  have h := reflection_log_13947_neg
  have he : Real.log (334652612941 / 125000000000) = -Real.log (125000000000 / 334652612941) := by
    rw [show ((334652612941 / 125000000000) : ℝ) = ((125000000000 / 334652612941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13948_neg : (49613739 / 50000000) ≤ -Real.log (500000000000 / 1348681705077) ∧
    -Real.log (500000000000 / 1348681705077) ≤ (496137391 / 500000000) := by
  have h := checkLog_sound (w := (348681705077 / 2348681705077)) (n := 12)
    (lo := (747819 / 2500000)) (hi := (299127601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348681705077 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1348681705077 / 1000000000000) = 1/(500000000000 / 1348681705077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13948 : Bounds (49613739 / 50000000) (496137391 / 500000000) (Real.log (1348681705077 / 500000000000)) := by
  have h := reflection_log_13948_neg
  have he : Real.log (1348681705077 / 500000000000) = -Real.log (500000000000 / 1348681705077) := by
    rw [show ((1348681705077 / 500000000000) : ℝ) = ((500000000000 / 1348681705077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13949_neg : (1090333953 / 500000000) ≤ -Real.log (31250000000 / 276631773399) ∧
    -Real.log (31250000000 / 276631773399) ≤ (218066791 / 100000000) := by
  have h := checkLog_sound (w := (26631773399 / 526631773399)) (n := 12)
    (lo := (50613183 / 500000000)) (hi := (101226367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((276631773399 / 250000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(276631773399 / 250000000000) = 1/(31250000000 / 276631773399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13949 : Bounds (1090333953 / 500000000) (218066791 / 100000000) (Real.log (276631773399 / 31250000000)) := by
  have h := reflection_log_13949_neg
  have he : Real.log (276631773399 / 31250000000) = -Real.log (31250000000 / 276631773399) := by
    rw [show ((276631773399 / 31250000000) : ℝ) = ((31250000000 / 276631773399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13950_neg : (87888983 / 40000000) ≤ -Real.log (1 / 9) ∧
    -Real.log (1 / 9) ≤ (2197224579 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 17)) (n := 12)
    (lo := (23556607 / 200000000)) (hi := (29445759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9 / 8) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(9 / 8) = 1/(1 / 9) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13950 : Bounds (87888983 / 40000000) (2197224579 / 1000000000) (Real.log (9 / 1)) := by
  have h := reflection_log_13950_neg
  have he : Real.log (9 / 1) = -Real.log (1 / 9) := by
    rw [show ((9 / 1) : ℝ) = ((1 / 9) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13951_neg : (73681493 / 125000000) ≤ -Real.log (1000 / 1803) ∧
    -Real.log (1000 / 1803) ≤ (117890389 / 200000000) := by
  have h := checkLog_sound (w := (803 / 2803)) (n := 12)
    (lo := (73681493 / 125000000)) (hi := (117890389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1803 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1803 / 1000) = 1/(1000 / 1803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13951 : Bounds (73681493 / 125000000) (117890389 / 200000000) (Real.log (1803 / 1000)) := by
  have h := reflection_log_13951_neg
  have he : Real.log (1803 / 1000) = -Real.log (1000 / 1803) := by
    rw [show ((1803 / 1000) : ℝ) = ((1000 / 1803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


