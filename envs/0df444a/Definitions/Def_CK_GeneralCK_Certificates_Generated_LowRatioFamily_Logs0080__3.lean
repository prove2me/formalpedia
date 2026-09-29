-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0080__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0080__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T04:30:12.516627+00:00
-- url     : https://prove2.me/theorems/8a777341-09d0-4ef7-abfe-1f3e6ecc664b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0080 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0081, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0080 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0081, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0082)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0080 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0081, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0082)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0080 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0081, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0082) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0080 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0081, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0082).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0080 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5120_neg : (377831579 / 1000000000) ≤ -Real.log (250000000000 / 364779294233) ∧
    -Real.log (250000000000 / 364779294233) ≤ (18891579 / 50000000) := by
  have h := checkLog_sound (w := (114779294233 / 614779294233)) (n := 12)
    (lo := (377831579 / 1000000000)) (hi := (18891579 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364779294233 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364779294233 / 250000000000) = 1/(250000000000 / 364779294233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5120 : Bounds (377831579 / 1000000000) (18891579 / 50000000) (Real.log (364779294233 / 250000000000)) := by
  have h := reflection_log_5120_neg
  have he : Real.log (364779294233 / 250000000000) = -Real.log (250000000000 / 364779294233) := by
    rw [show ((364779294233 / 250000000000) : ℝ) = ((250000000000 / 364779294233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5121_neg : (189019403 / 500000000) ≤ -Real.log (50000000000 / 72970978849) ∧
    -Real.log (50000000000 / 72970978849) ≤ (378038807 / 1000000000) := by
  have h := checkLog_sound (w := (22970978849 / 122970978849)) (n := 12)
    (lo := (189019403 / 500000000)) (hi := (378038807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72970978849 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72970978849 / 50000000000) = 1/(50000000000 / 72970978849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5121 : Bounds (189019403 / 500000000) (378038807 / 1000000000) (Real.log (72970978849 / 50000000000)) := by
  have h := reflection_log_5121_neg
  have he : Real.log (72970978849 / 50000000000) = -Real.log (50000000000 / 72970978849) := by
    rw [show ((72970978849 / 50000000000) : ℝ) = ((50000000000 / 72970978849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5122_neg : (85672433 / 500000000) ≤ -Real.log (10000 / 11869) ∧
    -Real.log (10000 / 11869) ≤ (171344867 / 1000000000) := by
  have h := checkLog_sound (w := (1869 / 21869)) (n := 12)
    (lo := (85672433 / 500000000)) (hi := (171344867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11869 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11869 / 10000) = 1/(10000 / 11869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5122 : Bounds (85672433 / 500000000) (171344867 / 1000000000) (Real.log (11869 / 10000)) := by
  have h := reflection_log_5122_neg
  have he : Real.log (11869 / 10000) = -Real.log (10000 / 11869) := by
    rw [show ((11869 / 10000) : ℝ) = ((10000 / 11869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5123_neg : (8276047 / 40000000) ≤ -Real.log (8131 / 10000) ∧
    -Real.log (8131 / 10000) ≤ (25862647 / 125000000) := by
  have h := checkLog_sound (w := (1869 / 18131)) (n := 12)
    (lo := (8276047 / 40000000)) (hi := (25862647 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8131) = 1/(8131 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5123 : Bounds (-25862647 / 125000000) (-8276047 / 40000000) (Real.log (8131 / 10000)) := by
  have h := reflection_log_5123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5124_neg : (93441 / 500000000) ≤ -Real.log (10000000 / 10001869) ∧
    -Real.log (10000000 / 10001869) ≤ (186883 / 1000000000) := by
  have h := checkLog_sound (w := (1869 / 20001869)) (n := 12)
    (lo := (93441 / 500000000)) (hi := (186883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001869 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001869 / 10000000) = 1/(10000000 / 10001869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5124 : Bounds (93441 / 500000000) (186883 / 1000000000) (Real.log (10001869 / 10000000)) := by
  have h := reflection_log_5124_neg
  have he : Real.log (10001869 / 10000000) = -Real.log (10000000 / 10001869) := by
    rw [show ((10001869 / 10000000) : ℝ) = ((10000000 / 10001869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5125_neg : (186917 / 1000000000) ≤ -Real.log (9998131 / 10000000) ∧
    -Real.log (9998131 / 10000000) ≤ (93459 / 500000000) := by
  have h := checkLog_sound (w := (1869 / 19998131)) (n := 12)
    (lo := (186917 / 1000000000)) (hi := (93459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998131) = 1/(9998131 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5125 : Bounds (-93459 / 500000000) (-186917 / 1000000000) (Real.log (9998131 / 10000000)) := by
  have h := reflection_log_5125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5126_neg : (44875103 / 500000000) ≤ -Real.log (1000000 / 1093901) ∧
    -Real.log (1000000 / 1093901) ≤ (89750207 / 1000000000) := by
  have h := checkLog_sound (w := (93901 / 2093901)) (n := 12)
    (lo := (44875103 / 500000000)) (hi := (89750207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093901 / 1000000) = 1/(1000000 / 1093901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5126 : Bounds (44875103 / 500000000) (89750207 / 1000000000) (Real.log (1093901 / 1000000)) := by
  have h := reflection_log_5126_neg
  have he : Real.log (1093901 / 1000000) = -Real.log (1000000 / 1093901) := by
    rw [show ((1093901 / 1000000) : ℝ) = ((1000000 / 1093901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5127_neg : (98606707 / 1000000000) ≤ -Real.log (906099 / 1000000) ∧
    -Real.log (906099 / 1000000) ≤ (24651677 / 250000000) := by
  have h := checkLog_sound (w := (93901 / 1906099)) (n := 12)
    (lo := (98606707 / 1000000000)) (hi := (24651677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906099) = 1/(906099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5127 : Bounds (-24651677 / 250000000) (-98606707 / 1000000000) (Real.log (906099 / 1000000)) := by
  have h := reflection_log_5127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5128_neg : (44983419 / 500000000) ≤ -Real.log (500000 / 547069) ∧
    -Real.log (500000 / 547069) ≤ (89966839 / 1000000000) := by
  have h := checkLog_sound (w := (47069 / 1047069)) (n := 12)
    (lo := (44983419 / 500000000)) (hi := (89966839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547069 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547069 / 500000) = 1/(500000 / 547069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5128 : Bounds (44983419 / 500000000) (89966839 / 1000000000) (Real.log (547069 / 500000)) := by
  have h := reflection_log_5128_neg
  have he : Real.log (547069 / 500000) = -Real.log (500000 / 547069) := by
    rw [show ((547069 / 500000) : ℝ) = ((500000 / 547069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5129_neg : (49434151 / 500000000) ≤ -Real.log (452931 / 500000) ∧
    -Real.log (452931 / 500000) ≤ (98868303 / 1000000000) := by
  have h := checkLog_sound (w := (47069 / 952931)) (n := 12)
    (lo := (49434151 / 500000000)) (hi := (98868303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452931) = 1/(452931 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5129 : Bounds (-98868303 / 1000000000) (-49434151 / 500000000) (Real.log (452931 / 500000)) := by
  have h := reflection_log_5129_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5130_neg : (8901463 / 1000000000) ≤ -Real.log (247784509239 / 250000000000) ∧
    -Real.log (247784509239 / 250000000000) ≤ (1112683 / 125000000) := by
  have h := checkLog_sound (w := (2215490761 / 497784509239)) (n := 12)
    (lo := (8901463 / 1000000000)) (hi := (1112683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247784509239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247784509239) = 1/(247784509239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5130 : Bounds (-1112683 / 125000000) (-8901463 / 1000000000) (Real.log (247784509239 / 250000000000)) := by
  have h := reflection_log_5130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5131_neg : (8856501 / 1000000000) ≤ -Real.log (991182602199 / 1000000000000) ∧
    -Real.log (991182602199 / 1000000000000) ≤ (4428251 / 500000000) := by
  have h := checkLog_sound (w := (8817397801 / 1991182602199)) (n := 12)
    (lo := (8856501 / 1000000000)) (hi := (4428251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991182602199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991182602199) = 1/(991182602199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5131 : Bounds (-4428251 / 500000000) (-8856501 / 1000000000) (Real.log (991182602199 / 1000000000000)) := by
  have h := reflection_log_5131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5132_neg : (188356913 / 1000000000) ≤ -Real.log (250000000000 / 301816081907) ∧
    -Real.log (250000000000 / 301816081907) ≤ (94178457 / 500000000) := by
  have h := checkLog_sound (w := (51816081907 / 551816081907)) (n := 12)
    (lo := (188356913 / 1000000000)) (hi := (94178457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301816081907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301816081907 / 250000000000) = 1/(250000000000 / 301816081907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5132 : Bounds (188356913 / 1000000000) (94178457 / 500000000) (Real.log (301816081907 / 250000000000)) := by
  have h := reflection_log_5132_neg
  have he : Real.log (301816081907 / 250000000000) = -Real.log (250000000000 / 301816081907) := by
    rw [show ((301816081907 / 250000000000) : ℝ) = ((250000000000 / 301816081907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5133_neg : (188835141 / 1000000000) ≤ -Real.log (20000000000 / 24156836251) ∧
    -Real.log (20000000000 / 24156836251) ≤ (94417571 / 500000000) := by
  have h := checkLog_sound (w := (4156836251 / 44156836251)) (n := 12)
    (lo := (188835141 / 1000000000)) (hi := (94417571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24156836251 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24156836251 / 20000000000) = 1/(20000000000 / 24156836251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5133 : Bounds (188835141 / 1000000000) (94417571 / 500000000) (Real.log (24156836251 / 20000000000)) := by
  have h := reflection_log_5133_neg
  have he : Real.log (24156836251 / 20000000000) = -Real.log (20000000000 / 24156836251) := by
    rw [show ((24156836251 / 20000000000) : ℝ) = ((20000000000 / 24156836251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5134_neg : (189019403 / 500000000) ≤ -Real.log (500000000000 / 729709788489) ∧
    -Real.log (500000000000 / 729709788489) ≤ (378038807 / 1000000000) := by
  have h := checkLog_sound (w := (229709788489 / 1229709788489)) (n := 12)
    (lo := (189019403 / 500000000)) (hi := (378038807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729709788489 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729709788489 / 500000000000) = 1/(500000000000 / 729709788489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5134 : Bounds (189019403 / 500000000) (378038807 / 1000000000) (Real.log (729709788489 / 500000000000)) := by
  have h := reflection_log_5134_neg
  have he : Real.log (729709788489 / 500000000000) = -Real.log (500000000000 / 729709788489) := by
    rw [show ((729709788489 / 500000000000) : ℝ) = ((500000000000 / 729709788489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5135_neg : (378246041 / 1000000000) ≤ -Real.log (100000000000 / 145972205141) ∧
    -Real.log (100000000000 / 145972205141) ≤ (189123021 / 500000000) := by
  have h := checkLog_sound (w := (45972205141 / 245972205141)) (n := 12)
    (lo := (378246041 / 1000000000)) (hi := (189123021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145972205141 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145972205141 / 100000000000) = 1/(100000000000 / 145972205141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5135 : Bounds (378246041 / 1000000000) (189123021 / 500000000) (Real.log (145972205141 / 100000000000)) := by
  have h := reflection_log_5135_neg
  have he : Real.log (145972205141 / 100000000000) = -Real.log (100000000000 / 145972205141) := by
    rw [show ((145972205141 / 100000000000) : ℝ) = ((100000000000 / 145972205141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5136_neg : (34285823 / 200000000) ≤ -Real.log (1000 / 1187) ∧
    -Real.log (1000 / 1187) ≤ (42857279 / 250000000) := by
  have h := checkLog_sound (w := (187 / 2187)) (n := 12)
    (lo := (34285823 / 200000000)) (hi := (42857279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187 / 1000) = 1/(1000 / 1187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5136 : Bounds (34285823 / 200000000) (42857279 / 250000000) (Real.log (1187 / 1000)) := by
  have h := reflection_log_5136_neg
  have he : Real.log (1187 / 1000) = -Real.log (1000 / 1187) := by
    rw [show ((1187 / 1000) : ℝ) = ((1000 / 1187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5137_neg : (207024169 / 1000000000) ≤ -Real.log (813 / 1000) ∧
    -Real.log (813 / 1000) ≤ (20702417 / 100000000) := by
  have h := checkLog_sound (w := (187 / 1813)) (n := 12)
    (lo := (207024169 / 1000000000)) (hi := (20702417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 813) = 1/(813 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5137 : Bounds (-20702417 / 100000000) (-207024169 / 1000000000) (Real.log (813 / 1000)) := by
  have h := reflection_log_5137_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5138_neg : (93491 / 500000000) ≤ -Real.log (1000000 / 1000187) ∧
    -Real.log (1000000 / 1000187) ≤ (186983 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 2000187)) (n := 12)
    (lo := (93491 / 500000000)) (hi := (186983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000187 / 1000000) = 1/(1000000 / 1000187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5138 : Bounds (93491 / 500000000) (186983 / 1000000000) (Real.log (1000187 / 1000000)) := by
  have h := reflection_log_5138_neg
  have he : Real.log (1000187 / 1000000) = -Real.log (1000000 / 1000187) := by
    rw [show ((1000187 / 1000000) : ℝ) = ((1000000 / 1000187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5139_neg : (187017 / 1000000000) ≤ -Real.log (999813 / 1000000) ∧
    -Real.log (999813 / 1000000) ≤ (93509 / 500000000) := by
  have h := checkLog_sound (w := (187 / 1999813)) (n := 12)
    (lo := (187017 / 1000000000)) (hi := (93509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999813) = 1/(999813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5139 : Bounds (-93509 / 500000000) (-187017 / 1000000000) (Real.log (999813 / 1000000)) := by
  have h := reflection_log_5139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5140_neg : (89795913 / 1000000000) ≤ -Real.log (1000000 / 1093951) ∧
    -Real.log (1000000 / 1093951) ≤ (44897957 / 500000000) := by
  have h := checkLog_sound (w := (93951 / 2093951)) (n := 12)
    (lo := (89795913 / 1000000000)) (hi := (44897957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093951 / 1000000) = 1/(1000000 / 1093951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5140 : Bounds (89795913 / 1000000000) (44897957 / 500000000) (Real.log (1093951 / 1000000)) := by
  have h := reflection_log_5140_neg
  have he : Real.log (1093951 / 1000000) = -Real.log (1000000 / 1093951) := by
    rw [show ((1093951 / 1000000) : ℝ) = ((1000000 / 1093951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5141_neg : (9866189 / 100000000) ≤ -Real.log (906049 / 1000000) ∧
    -Real.log (906049 / 1000000) ≤ (98661891 / 1000000000) := by
  have h := checkLog_sound (w := (93951 / 1906049)) (n := 12)
    (lo := (9866189 / 100000000)) (hi := (98661891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906049) = 1/(906049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5141 : Bounds (-98661891 / 1000000000) (-9866189 / 100000000) (Real.log (906049 / 1000000)) := by
  have h := reflection_log_5141_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5142_neg : (90013449 / 1000000000) ≤ -Real.log (1000000 / 1094189) ∧
    -Real.log (1000000 / 1094189) ≤ (1800269 / 20000000) := by
  have h := checkLog_sound (w := (94189 / 2094189)) (n := 12)
    (lo := (90013449 / 1000000000)) (hi := (1800269 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094189 / 1000000) = 1/(1000000 / 1094189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5142 : Bounds (90013449 / 1000000000) (1800269 / 20000000) (Real.log (1094189 / 1000000)) := by
  have h := reflection_log_5142_neg
  have he : Real.log (1094189 / 1000000) = -Real.log (1000000 / 1094189) := by
    rw [show ((1094189 / 1000000) : ℝ) = ((1000000 / 1094189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5143_neg : (98924603 / 1000000000) ≤ -Real.log (905811 / 1000000) ∧
    -Real.log (905811 / 1000000) ≤ (24731151 / 250000000) := by
  have h := checkLog_sound (w := (94189 / 1905811)) (n := 12)
    (lo := (98924603 / 1000000000)) (hi := (24731151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905811) = 1/(905811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5143 : Bounds (-24731151 / 250000000) (-98924603 / 1000000000) (Real.log (905811 / 1000000)) := by
  have h := reflection_log_5143_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5144_neg : (4455577 / 500000000) ≤ -Real.log (991128432279 / 1000000000000) ∧
    -Real.log (991128432279 / 1000000000000) ≤ (1782231 / 200000000) := by
  have h := checkLog_sound (w := (8871567721 / 1991128432279)) (n := 12)
    (lo := (4455577 / 500000000)) (hi := (1782231 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991128432279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991128432279) = 1/(991128432279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5144 : Bounds (-1782231 / 200000000) (-4455577 / 500000000) (Real.log (991128432279 / 1000000000000)) := by
  have h := reflection_log_5144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5145_neg : (8865977 / 1000000000) ≤ -Real.log (991173209599 / 1000000000000) ∧
    -Real.log (991173209599 / 1000000000000) ≤ (4432989 / 500000000) := by
  have h := checkLog_sound (w := (8826790401 / 1991173209599)) (n := 12)
    (lo := (8865977 / 1000000000)) (hi := (4432989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991173209599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991173209599) = 1/(991173209599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5145 : Bounds (-4432989 / 500000000) (-8865977 / 1000000000) (Real.log (991173209599 / 1000000000000)) := by
  have h := reflection_log_5145_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5146_neg : (188457803 / 1000000000) ≤ -Real.log (125000000000 / 150923266843) ∧
    -Real.log (125000000000 / 150923266843) ≤ (47114451 / 250000000) := by
  have h := checkLog_sound (w := (25923266843 / 275923266843)) (n := 12)
    (lo := (188457803 / 1000000000)) (hi := (47114451 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150923266843 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150923266843 / 125000000000) = 1/(125000000000 / 150923266843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5146 : Bounds (188457803 / 1000000000) (47114451 / 250000000) (Real.log (150923266843 / 125000000000)) := by
  have h := reflection_log_5146_neg
  have he : Real.log (150923266843 / 125000000000) = -Real.log (125000000000 / 150923266843) := by
    rw [show ((150923266843 / 125000000000) : ℝ) = ((125000000000 / 150923266843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5147_neg : (188938053 / 1000000000) ≤ -Real.log (125000000000 / 150995765121) ∧
    -Real.log (125000000000 / 150995765121) ≤ (94469027 / 500000000) := by
  have h := checkLog_sound (w := (25995765121 / 275995765121)) (n := 12)
    (lo := (188938053 / 1000000000)) (hi := (94469027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150995765121 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150995765121 / 125000000000) = 1/(125000000000 / 150995765121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5147 : Bounds (188938053 / 1000000000) (94469027 / 500000000) (Real.log (150995765121 / 125000000000)) := by
  have h := reflection_log_5147_neg
  have he : Real.log (150995765121 / 125000000000) = -Real.log (125000000000 / 150995765121) := by
    rw [show ((150995765121 / 125000000000) : ℝ) = ((125000000000 / 150995765121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5148_neg : (378246041 / 1000000000) ≤ -Real.log (62500000000 / 91232628213) ∧
    -Real.log (62500000000 / 91232628213) ≤ (189123021 / 500000000) := by
  have h := checkLog_sound (w := (28732628213 / 153732628213)) (n := 12)
    (lo := (378246041 / 1000000000)) (hi := (189123021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91232628213 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91232628213 / 62500000000) = 1/(62500000000 / 91232628213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5148 : Bounds (378246041 / 1000000000) (189123021 / 500000000) (Real.log (91232628213 / 62500000000)) := by
  have h := reflection_log_5148_neg
  have he : Real.log (91232628213 / 62500000000) = -Real.log (62500000000 / 91232628213) := by
    rw [show ((91232628213 / 62500000000) : ℝ) = ((62500000000 / 91232628213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5149_neg : (75690657 / 200000000) ≤ -Real.log (125000000000 / 182503075031) ∧
    -Real.log (125000000000 / 182503075031) ≤ (189226643 / 500000000) := by
  have h := checkLog_sound (w := (57503075031 / 307503075031)) (n := 12)
    (lo := (75690657 / 200000000)) (hi := (189226643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182503075031 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182503075031 / 125000000000) = 1/(125000000000 / 182503075031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5149 : Bounds (75690657 / 200000000) (189226643 / 500000000) (Real.log (182503075031 / 125000000000)) := by
  have h := reflection_log_5149_neg
  have he : Real.log (182503075031 / 125000000000) = -Real.log (125000000000 / 182503075031) := by
    rw [show ((182503075031 / 125000000000) : ℝ) = ((125000000000 / 182503075031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5150_neg : (85756679 / 500000000) ≤ -Real.log (10000 / 11871) ∧
    -Real.log (10000 / 11871) ≤ (171513359 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 21871)) (n := 12)
    (lo := (85756679 / 500000000)) (hi := (171513359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11871 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11871 / 10000) = 1/(10000 / 11871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5150 : Bounds (85756679 / 500000000) (171513359 / 1000000000) (Real.log (11871 / 10000)) := by
  have h := reflection_log_5150_neg
  have he : Real.log (11871 / 10000) = -Real.log (10000 / 11871) := by
    rw [show ((11871 / 10000) : ℝ) = ((10000 / 11871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5151_neg : (103573589 / 500000000) ≤ -Real.log (8129 / 10000) ∧
    -Real.log (8129 / 10000) ≤ (207147179 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 18129)) (n := 12)
    (lo := (103573589 / 500000000)) (hi := (207147179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8129) = 1/(8129 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5151 : Bounds (-207147179 / 1000000000) (-103573589 / 500000000) (Real.log (8129 / 10000)) := by
  have h := reflection_log_5151_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5152_neg : (93541 / 500000000) ≤ -Real.log (10000000 / 10001871) ∧
    -Real.log (10000000 / 10001871) ≤ (187083 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 20001871)) (n := 12)
    (lo := (93541 / 500000000)) (hi := (187083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001871 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001871 / 10000000) = 1/(10000000 / 10001871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5152 : Bounds (93541 / 500000000) (187083 / 1000000000) (Real.log (10001871 / 10000000)) := by
  have h := reflection_log_5152_neg
  have he : Real.log (10001871 / 10000000) = -Real.log (10000000 / 10001871) := by
    rw [show ((10001871 / 10000000) : ℝ) = ((10000000 / 10001871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5153_neg : (187117 / 1000000000) ≤ -Real.log (9998129 / 10000000) ∧
    -Real.log (9998129 / 10000000) ≤ (93559 / 500000000) := by
  have h := checkLog_sound (w := (1871 / 19998129)) (n := 12)
    (lo := (187117 / 1000000000)) (hi := (93559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998129) = 1/(9998129 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5153 : Bounds (-93559 / 500000000) (-187117 / 1000000000) (Real.log (9998129 / 10000000)) := by
  have h := reflection_log_5153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5154_neg : (22460633 / 250000000) ≤ -Real.log (500000 / 547001) ∧
    -Real.log (500000 / 547001) ≤ (89842533 / 1000000000) := by
  have h := checkLog_sound (w := (47001 / 1047001)) (n := 12)
    (lo := (22460633 / 250000000)) (hi := (89842533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547001 / 500000) = 1/(500000 / 547001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5154 : Bounds (22460633 / 250000000) (89842533 / 1000000000) (Real.log (547001 / 500000)) := by
  have h := reflection_log_5154_neg
  have he : Real.log (547001 / 500000) = -Real.log (500000 / 547001) := by
    rw [show ((547001 / 500000) : ℝ) = ((500000 / 547001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5155_neg : (4935909 / 50000000) ≤ -Real.log (452999 / 500000) ∧
    -Real.log (452999 / 500000) ≤ (98718181 / 1000000000) := by
  have h := checkLog_sound (w := (47001 / 952999)) (n := 12)
    (lo := (4935909 / 50000000)) (hi := (98718181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452999) = 1/(452999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5155 : Bounds (-98718181 / 1000000000) (-4935909 / 50000000) (Real.log (452999 / 500000)) := by
  have h := reflection_log_5155_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5156_neg : (45030029 / 500000000) ≤ -Real.log (6250 / 6839) ∧
    -Real.log (6250 / 6839) ≤ (90060059 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 13089)) (n := 12)
    (lo := (45030029 / 500000000)) (hi := (90060059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6839 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6839 / 6250) = 1/(6250 / 6839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5156 : Bounds (45030029 / 500000000) (90060059 / 1000000000) (Real.log (6839 / 6250)) := by
  have h := reflection_log_5156_neg
  have he : Real.log (6839 / 6250) = -Real.log (6250 / 6839) := by
    rw [show ((6839 / 6250) : ℝ) = ((6250 / 6839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5157_neg : (24745227 / 250000000) ≤ -Real.log (5661 / 6250) ∧
    -Real.log (5661 / 6250) ≤ (98980909 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 11911)) (n := 12)
    (lo := (24745227 / 250000000)) (hi := (98980909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5661) = 1/(5661 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5157 : Bounds (-98980909 / 1000000000) (-24745227 / 250000000) (Real.log (5661 / 6250)) := by
  have h := reflection_log_5157_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5158_neg : (178417 / 20000000) ≤ -Real.log (38715579 / 39062500) ∧
    -Real.log (38715579 / 39062500) ≤ (8920851 / 1000000000) := by
  have h := checkLog_sound (w := (346921 / 77778079)) (n := 12)
    (lo := (178417 / 20000000)) (hi := (8920851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38715579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38715579) = 1/(38715579 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5158 : Bounds (-8920851 / 1000000000) (-178417 / 20000000) (Real.log (38715579 / 39062500)) := by
  have h := reflection_log_5158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5159_neg : (69341 / 7812500) ≤ -Real.log (247790905999 / 250000000000) ∧
    -Real.log (247790905999 / 250000000000) ≤ (8875649 / 1000000000) := by
  have h := checkLog_sound (w := (2209094001 / 497790905999)) (n := 12)
    (lo := (69341 / 7812500)) (hi := (8875649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247790905999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247790905999) = 1/(247790905999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5159 : Bounds (-8875649 / 1000000000) (-69341 / 7812500) (Real.log (247790905999 / 250000000000)) := by
  have h := reflection_log_5159_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5160_neg : (23570089 / 125000000) ≤ -Real.log (500000000000 / 603755195927) ∧
    -Real.log (500000000000 / 603755195927) ≤ (188560713 / 1000000000) := by
  have h := checkLog_sound (w := (103755195927 / 1103755195927)) (n := 12)
    (lo := (23570089 / 125000000)) (hi := (188560713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603755195927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603755195927 / 500000000000) = 1/(500000000000 / 603755195927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5160 : Bounds (23570089 / 125000000) (188560713 / 1000000000) (Real.log (603755195927 / 500000000000)) := by
  have h := reflection_log_5160_neg
  have he : Real.log (603755195927 / 500000000000) = -Real.log (500000000000 / 603755195927) := by
    rw [show ((603755195927 / 500000000000) : ℝ) = ((500000000000 / 603755195927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5161_neg : (189040967 / 1000000000) ≤ -Real.log (500000000000 / 604045221693) ∧
    -Real.log (500000000000 / 604045221693) ≤ (23630121 / 125000000) := by
  have h := checkLog_sound (w := (104045221693 / 1104045221693)) (n := 12)
    (lo := (189040967 / 1000000000)) (hi := (23630121 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604045221693 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604045221693 / 500000000000) = 1/(500000000000 / 604045221693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5161 : Bounds (189040967 / 1000000000) (23630121 / 125000000) (Real.log (604045221693 / 500000000000)) := by
  have h := reflection_log_5161_neg
  have he : Real.log (604045221693 / 500000000000) = -Real.log (500000000000 / 604045221693) := by
    rw [show ((604045221693 / 500000000000) : ℝ) = ((500000000000 / 604045221693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5162_neg : (75690657 / 200000000) ≤ -Real.log (500000000000 / 730012300123) ∧
    -Real.log (500000000000 / 730012300123) ≤ (189226643 / 500000000) := by
  have h := checkLog_sound (w := (230012300123 / 1230012300123)) (n := 12)
    (lo := (75690657 / 200000000)) (hi := (189226643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730012300123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730012300123 / 500000000000) = 1/(500000000000 / 730012300123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5162 : Bounds (75690657 / 200000000) (189226643 / 500000000) (Real.log (730012300123 / 500000000000)) := by
  have h := reflection_log_5162_neg
  have he : Real.log (730012300123 / 500000000000) = -Real.log (500000000000 / 730012300123) := by
    rw [show ((730012300123 / 500000000000) : ℝ) = ((500000000000 / 730012300123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5163_neg : (47332567 / 125000000) ≤ -Real.log (500000000000 / 730163611761) ∧
    -Real.log (500000000000 / 730163611761) ≤ (378660537 / 1000000000) := by
  have h := checkLog_sound (w := (230163611761 / 1230163611761)) (n := 12)
    (lo := (47332567 / 125000000)) (hi := (378660537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730163611761 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730163611761 / 500000000000) = 1/(500000000000 / 730163611761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5163 : Bounds (47332567 / 125000000) (378660537 / 1000000000) (Real.log (730163611761 / 500000000000)) := by
  have h := reflection_log_5163_neg
  have he : Real.log (730163611761 / 500000000000) = -Real.log (500000000000 / 730163611761) := by
    rw [show ((730163611761 / 500000000000) : ℝ) = ((500000000000 / 730163611761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5164_neg : (171597593 / 1000000000) ≤ -Real.log (625 / 742) ∧
    -Real.log (625 / 742) ≤ (85798797 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1367)) (n := 12)
    (lo := (171597593 / 1000000000)) (hi := (85798797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742 / 625) = 1/(625 / 742) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5164 : Bounds (171597593 / 1000000000) (85798797 / 500000000) (Real.log (742 / 625)) := by
  have h := reflection_log_5164_neg
  have he : Real.log (742 / 625) = -Real.log (625 / 742) := by
    rw [show ((742 / 625) : ℝ) = ((625 / 742) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5165_neg : (103635101 / 500000000) ≤ -Real.log (508 / 625) ∧
    -Real.log (508 / 625) ≤ (207270203 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1133)) (n := 12)
    (lo := (103635101 / 500000000)) (hi := (207270203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 508) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 508) = 1/(508 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5165 : Bounds (-207270203 / 1000000000) (-103635101 / 500000000) (Real.log (508 / 625)) := by
  have h := reflection_log_5165_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5166_neg : (93591 / 500000000) ≤ -Real.log (625000 / 625117) ∧
    -Real.log (625000 / 625117) ≤ (187183 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1250117)) (n := 12)
    (lo := (93591 / 500000000)) (hi := (187183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625117 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625117 / 625000) = 1/(625000 / 625117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5166 : Bounds (93591 / 500000000) (187183 / 1000000000) (Real.log (625117 / 625000)) := by
  have h := reflection_log_5166_neg
  have he : Real.log (625117 / 625000) = -Real.log (625000 / 625117) := by
    rw [show ((625117 / 625000) : ℝ) = ((625000 / 625117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5167_neg : (187217 / 1000000000) ≤ -Real.log (624883 / 625000) ∧
    -Real.log (624883 / 625000) ≤ (93609 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1249883)) (n := 12)
    (lo := (187217 / 1000000000)) (hi := (93609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624883) = 1/(624883 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5167 : Bounds (-93609 / 500000000) (-187217 / 1000000000) (Real.log (624883 / 625000)) := by
  have h := reflection_log_5167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5168_neg : (22472287 / 250000000) ≤ -Real.log (1000000 / 1094053) ∧
    -Real.log (1000000 / 1094053) ≤ (89889149 / 1000000000) := by
  have h := checkLog_sound (w := (94053 / 2094053)) (n := 12)
    (lo := (22472287 / 250000000)) (hi := (89889149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094053 / 1000000) = 1/(1000000 / 1094053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5168 : Bounds (22472287 / 250000000) (89889149 / 1000000000) (Real.log (1094053 / 1000000)) := by
  have h := reflection_log_5168_neg
  have he : Real.log (1094053 / 1000000) = -Real.log (1000000 / 1094053) := by
    rw [show ((1094053 / 1000000) : ℝ) = ((1000000 / 1094053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5169_neg : (98774473 / 1000000000) ≤ -Real.log (905947 / 1000000) ∧
    -Real.log (905947 / 1000000) ≤ (49387237 / 500000000) := by
  have h := checkLog_sound (w := (94053 / 1905947)) (n := 12)
    (lo := (98774473 / 1000000000)) (hi := (49387237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905947) = 1/(905947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5169 : Bounds (-49387237 / 500000000) (-98774473 / 1000000000) (Real.log (905947 / 1000000)) := by
  have h := reflection_log_5169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5170_neg : (11263333 / 125000000) ≤ -Real.log (1000000 / 1094291) ∧
    -Real.log (1000000 / 1094291) ≤ (18021333 / 200000000) := by
  have h := checkLog_sound (w := (94291 / 2094291)) (n := 12)
    (lo := (11263333 / 125000000)) (hi := (18021333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094291 / 1000000) = 1/(1000000 / 1094291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5170 : Bounds (11263333 / 125000000) (18021333 / 200000000) (Real.log (1094291 / 1000000)) := by
  have h := reflection_log_5170_neg
  have he : Real.log (1094291 / 1000000) = -Real.log (1000000 / 1094291) := by
    rw [show ((1094291 / 1000000) : ℝ) = ((1000000 / 1094291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5171_neg : (3094913 / 31250000) ≤ -Real.log (905709 / 1000000) ∧
    -Real.log (905709 / 1000000) ≤ (99037217 / 1000000000) := by
  have h := checkLog_sound (w := (94291 / 1905709)) (n := 12)
    (lo := (3094913 / 31250000)) (hi := (99037217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905709) = 1/(905709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5171 : Bounds (-99037217 / 1000000000) (-3094913 / 31250000) (Real.log (905709 / 1000000)) := by
  have h := reflection_log_5171_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5172_neg : (8930551 / 1000000000) ≤ -Real.log (991109207319 / 1000000000000) ∧
    -Real.log (991109207319 / 1000000000000) ≤ (1116319 / 125000000) := by
  have h := checkLog_sound (w := (8890792681 / 1991109207319)) (n := 12)
    (lo := (8930551 / 1000000000)) (hi := (1116319 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991109207319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991109207319) = 1/(991109207319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5172 : Bounds (-1116319 / 125000000) (-8930551 / 1000000000) (Real.log (991109207319 / 1000000000000)) := by
  have h := reflection_log_5172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5173_neg : (2221331 / 250000000) ≤ -Real.log (991154033191 / 1000000000000) ∧
    -Real.log (991154033191 / 1000000000000) ≤ (355413 / 40000000) := by
  have h := checkLog_sound (w := (8845966809 / 1991154033191)) (n := 12)
    (lo := (2221331 / 250000000)) (hi := (355413 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991154033191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991154033191) = 1/(991154033191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5173 : Bounds (-355413 / 40000000) (-2221331 / 250000000) (Real.log (991154033191 / 1000000000000)) := by
  have h := reflection_log_5173_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5174_neg : (94331811 / 500000000) ≤ -Real.log (500000000000 / 603817331477) ∧
    -Real.log (500000000000 / 603817331477) ≤ (188663623 / 1000000000) := by
  have h := checkLog_sound (w := (103817331477 / 1103817331477)) (n := 12)
    (lo := (94331811 / 500000000)) (hi := (188663623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603817331477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603817331477 / 500000000000) = 1/(500000000000 / 603817331477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5174 : Bounds (94331811 / 500000000) (188663623 / 1000000000) (Real.log (603817331477 / 500000000000)) := by
  have h := reflection_log_5174_neg
  have he : Real.log (603817331477 / 500000000000) = -Real.log (500000000000 / 603817331477) := by
    rw [show ((603817331477 / 500000000000) : ℝ) = ((500000000000 / 603817331477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5175_neg : (189143881 / 1000000000) ≤ -Real.log (250000000000 / 302053694951) ∧
    -Real.log (250000000000 / 302053694951) ≤ (94571941 / 500000000) := by
  have h := checkLog_sound (w := (52053694951 / 552053694951)) (n := 12)
    (lo := (189143881 / 1000000000)) (hi := (94571941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302053694951 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302053694951 / 250000000000) = 1/(250000000000 / 302053694951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5175 : Bounds (189143881 / 1000000000) (94571941 / 500000000) (Real.log (302053694951 / 250000000000)) := by
  have h := reflection_log_5175_neg
  have he : Real.log (302053694951 / 250000000000) = -Real.log (250000000000 / 302053694951) := by
    rw [show ((302053694951 / 250000000000) : ℝ) = ((250000000000 / 302053694951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5176_neg : (47332567 / 125000000) ≤ -Real.log (6250000000 / 9127045147) ∧
    -Real.log (6250000000 / 9127045147) ≤ (378660537 / 1000000000) := by
  have h := checkLog_sound (w := (2877045147 / 15377045147)) (n := 12)
    (lo := (47332567 / 125000000)) (hi := (378660537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9127045147 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9127045147 / 6250000000) = 1/(6250000000 / 9127045147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5176 : Bounds (47332567 / 125000000) (378660537 / 1000000000) (Real.log (9127045147 / 6250000000)) := by
  have h := reflection_log_5176_neg
  have he : Real.log (9127045147 / 6250000000) = -Real.log (6250000000 / 9127045147) := by
    rw [show ((9127045147 / 6250000000) : ℝ) = ((6250000000 / 9127045147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5177_neg : (75773559 / 200000000) ≤ -Real.log (50000000000 / 73031496063) ∧
    -Real.log (50000000000 / 73031496063) ≤ (94716949 / 250000000) := by
  have h := checkLog_sound (w := (23031496063 / 123031496063)) (n := 12)
    (lo := (75773559 / 200000000)) (hi := (94716949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73031496063 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73031496063 / 50000000000) = 1/(50000000000 / 73031496063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5177 : Bounds (75773559 / 200000000) (94716949 / 250000000) (Real.log (73031496063 / 50000000000)) := by
  have h := reflection_log_5177_neg
  have he : Real.log (73031496063 / 50000000000) = -Real.log (50000000000 / 73031496063) := by
    rw [show ((73031496063 / 50000000000) : ℝ) = ((50000000000 / 73031496063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5178_neg : (171681821 / 1000000000) ≤ -Real.log (10000 / 11873) ∧
    -Real.log (10000 / 11873) ≤ (85840911 / 500000000) := by
  have h := checkLog_sound (w := (1873 / 21873)) (n := 12)
    (lo := (171681821 / 1000000000)) (hi := (85840911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11873 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11873 / 10000) = 1/(10000 / 11873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5178 : Bounds (171681821 / 1000000000) (85840911 / 500000000) (Real.log (11873 / 10000)) := by
  have h := reflection_log_5178_neg
  have he : Real.log (11873 / 10000) = -Real.log (10000 / 11873) := by
    rw [show ((11873 / 10000) : ℝ) = ((10000 / 11873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5179_neg : (207393241 / 1000000000) ≤ -Real.log (8127 / 10000) ∧
    -Real.log (8127 / 10000) ≤ (103696621 / 500000000) := by
  have h := checkLog_sound (w := (1873 / 18127)) (n := 12)
    (lo := (207393241 / 1000000000)) (hi := (103696621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8127) = 1/(8127 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5179 : Bounds (-103696621 / 500000000) (-207393241 / 1000000000) (Real.log (8127 / 10000)) := by
  have h := reflection_log_5179_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5180_neg : (93641 / 500000000) ≤ -Real.log (10000000 / 10001873) ∧
    -Real.log (10000000 / 10001873) ≤ (187283 / 1000000000) := by
  have h := checkLog_sound (w := (1873 / 20001873)) (n := 12)
    (lo := (93641 / 500000000)) (hi := (187283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001873 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001873 / 10000000) = 1/(10000000 / 10001873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5180 : Bounds (93641 / 500000000) (187283 / 1000000000) (Real.log (10001873 / 10000000)) := by
  have h := reflection_log_5180_neg
  have he : Real.log (10001873 / 10000000) = -Real.log (10000000 / 10001873) := by
    rw [show ((10001873 / 10000000) : ℝ) = ((10000000 / 10001873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5181_neg : (187317 / 1000000000) ≤ -Real.log (9998127 / 10000000) ∧
    -Real.log (9998127 / 10000000) ≤ (93659 / 500000000) := by
  have h := checkLog_sound (w := (1873 / 19998127)) (n := 12)
    (lo := (187317 / 1000000000)) (hi := (93659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998127) = 1/(9998127 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5181 : Bounds (-93659 / 500000000) (-187317 / 1000000000) (Real.log (9998127 / 10000000)) := by
  have h := reflection_log_5181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5182_neg : (89935763 / 1000000000) ≤ -Real.log (125000 / 136763) ∧
    -Real.log (125000 / 136763) ≤ (22483941 / 250000000) := by
  have h := checkLog_sound (w := (11763 / 261763)) (n := 12)
    (lo := (89935763 / 1000000000)) (hi := (22483941 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136763 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136763 / 125000) = 1/(125000 / 136763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5182 : Bounds (89935763 / 1000000000) (22483941 / 250000000) (Real.log (136763 / 125000)) := by
  have h := reflection_log_5182_neg
  have he : Real.log (136763 / 125000) = -Real.log (125000 / 136763) := by
    rw [show ((136763 / 125000) : ℝ) = ((125000 / 136763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5183_neg : (98830769 / 1000000000) ≤ -Real.log (113237 / 125000) ∧
    -Real.log (113237 / 125000) ≤ (9883077 / 100000000) := by
  have h := checkLog_sound (w := (11763 / 238237)) (n := 12)
    (lo := (98830769 / 1000000000)) (hi := (9883077 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113237) = 1/(113237 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5183 : Bounds (-9883077 / 100000000) (-98830769 / 1000000000) (Real.log (113237 / 125000)) := by
  have h := reflection_log_5183_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0081 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5184_neg : (90153269 / 1000000000) ≤ -Real.log (500000 / 547171) ∧
    -Real.log (500000 / 547171) ≤ (9015327 / 100000000) := by
  have h := checkLog_sound (w := (47171 / 1047171)) (n := 12)
    (lo := (90153269 / 1000000000)) (hi := (9015327 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547171 / 500000) = 1/(500000 / 547171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5184 : Bounds (90153269 / 1000000000) (9015327 / 100000000) (Real.log (547171 / 500000)) := by
  have h := reflection_log_5184_neg
  have he : Real.log (547171 / 500000) = -Real.log (500000 / 547171) := by
    rw [show ((547171 / 500000) : ℝ) = ((500000 / 547171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5185_neg : (99093527 / 1000000000) ≤ -Real.log (452829 / 500000) ∧
    -Real.log (452829 / 500000) ≤ (12386691 / 125000000) := by
  have h := checkLog_sound (w := (47171 / 952829)) (n := 12)
    (lo := (99093527 / 1000000000)) (hi := (12386691 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452829) = 1/(452829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5185 : Bounds (-12386691 / 125000000) (-99093527 / 1000000000) (Real.log (452829 / 500000)) := by
  have h := reflection_log_5185_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5186_neg : (4470129 / 500000000) ≤ -Real.log (247774896759 / 250000000000) ∧
    -Real.log (247774896759 / 250000000000) ≤ (8940259 / 1000000000) := by
  have h := checkLog_sound (w := (2225103241 / 497774896759)) (n := 12)
    (lo := (4470129 / 500000000)) (hi := (8940259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247774896759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247774896759) = 1/(247774896759 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5186 : Bounds (-8940259 / 1000000000) (-4470129 / 500000000) (Real.log (247774896759 / 250000000000)) := by
  have h := reflection_log_5186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5187_neg : (4447503 / 500000000) ≤ -Real.log (15486631831 / 15625000000) ∧
    -Real.log (15486631831 / 15625000000) ≤ (8895007 / 1000000000) := by
  have h := checkLog_sound (w := (138368169 / 31111631831)) (n := 12)
    (lo := (4447503 / 500000000)) (hi := (8895007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15486631831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15486631831) = 1/(15486631831 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5187 : Bounds (-8895007 / 1000000000) (-4447503 / 500000000) (Real.log (15486631831 / 15625000000)) := by
  have h := reflection_log_5187_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5188_neg : (188766533 / 1000000000) ≤ -Real.log (500000000000 / 603879474023) ∧
    -Real.log (500000000000 / 603879474023) ≤ (94383267 / 500000000) := by
  have h := checkLog_sound (w := (103879474023 / 1103879474023)) (n := 12)
    (lo := (188766533 / 1000000000)) (hi := (94383267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603879474023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603879474023 / 500000000000) = 1/(500000000000 / 603879474023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5188 : Bounds (188766533 / 1000000000) (94383267 / 500000000) (Real.log (603879474023 / 500000000000)) := by
  have h := reflection_log_5188_neg
  have he : Real.log (603879474023 / 500000000000) = -Real.log (500000000000 / 603879474023) := by
    rw [show ((603879474023 / 500000000000) : ℝ) = ((500000000000 / 603879474023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5189_neg : (189246797 / 1000000000) ≤ -Real.log (62500000000 / 75521195639) ∧
    -Real.log (62500000000 / 75521195639) ≤ (94623399 / 500000000) := by
  have h := checkLog_sound (w := (13021195639 / 138021195639)) (n := 12)
    (lo := (189246797 / 1000000000)) (hi := (94623399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75521195639 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75521195639 / 62500000000) = 1/(62500000000 / 75521195639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5189 : Bounds (189246797 / 1000000000) (94623399 / 500000000) (Real.log (75521195639 / 62500000000)) := by
  have h := reflection_log_5189_neg
  have he : Real.log (75521195639 / 62500000000) = -Real.log (62500000000 / 75521195639) := by
    rw [show ((75521195639 / 62500000000) : ℝ) = ((62500000000 / 75521195639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5190_neg : (75773559 / 200000000) ≤ -Real.log (500000000000 / 730314960629) ∧
    -Real.log (500000000000 / 730314960629) ≤ (94716949 / 250000000) := by
  have h := checkLog_sound (w := (230314960629 / 1230314960629)) (n := 12)
    (lo := (75773559 / 200000000)) (hi := (94716949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730314960629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730314960629 / 500000000000) = 1/(500000000000 / 730314960629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5190 : Bounds (75773559 / 200000000) (94716949 / 250000000) (Real.log (730314960629 / 500000000000)) := by
  have h := reflection_log_5190_neg
  have he : Real.log (730314960629 / 500000000000) = -Real.log (500000000000 / 730314960629) := by
    rw [show ((730314960629 / 500000000000) : ℝ) = ((500000000000 / 730314960629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5191_neg : (189537531 / 500000000) ≤ -Real.log (250000000000 / 365233173373) ∧
    -Real.log (250000000000 / 365233173373) ≤ (379075063 / 1000000000) := by
  have h := checkLog_sound (w := (115233173373 / 615233173373)) (n := 12)
    (lo := (189537531 / 500000000)) (hi := (379075063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365233173373 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365233173373 / 250000000000) = 1/(250000000000 / 365233173373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5191 : Bounds (189537531 / 500000000) (379075063 / 1000000000) (Real.log (365233173373 / 250000000000)) := by
  have h := reflection_log_5191_neg
  have he : Real.log (365233173373 / 250000000000) = -Real.log (250000000000 / 365233173373) := by
    rw [show ((365233173373 / 250000000000) : ℝ) = ((250000000000 / 365233173373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5192_neg : (85883021 / 500000000) ≤ -Real.log (5000 / 5937) ∧
    -Real.log (5000 / 5937) ≤ (171766043 / 1000000000) := by
  have h := checkLog_sound (w := (937 / 10937)) (n := 12)
    (lo := (85883021 / 500000000)) (hi := (171766043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5937 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5937 / 5000) = 1/(5000 / 5937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5192 : Bounds (85883021 / 500000000) (171766043 / 1000000000) (Real.log (5937 / 5000)) := by
  have h := reflection_log_5192_neg
  have he : Real.log (5937 / 5000) = -Real.log (5000 / 5937) := by
    rw [show ((5937 / 5000) : ℝ) = ((5000 / 5937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5193_neg : (41503259 / 200000000) ≤ -Real.log (4063 / 5000) ∧
    -Real.log (4063 / 5000) ≤ (25939537 / 125000000) := by
  have h := checkLog_sound (w := (937 / 9063)) (n := 12)
    (lo := (41503259 / 200000000)) (hi := (25939537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4063) = 1/(4063 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5193 : Bounds (-25939537 / 125000000) (-41503259 / 200000000) (Real.log (4063 / 5000)) := by
  have h := reflection_log_5193_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5194_neg : (93691 / 500000000) ≤ -Real.log (5000000 / 5000937) ∧
    -Real.log (5000000 / 5000937) ≤ (187383 / 1000000000) := by
  have h := checkLog_sound (w := (937 / 10000937)) (n := 12)
    (lo := (93691 / 500000000)) (hi := (187383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000937 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000937 / 5000000) = 1/(5000000 / 5000937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5194 : Bounds (93691 / 500000000) (187383 / 1000000000) (Real.log (5000937 / 5000000)) := by
  have h := reflection_log_5194_neg
  have he : Real.log (5000937 / 5000000) = -Real.log (5000000 / 5000937) := by
    rw [show ((5000937 / 5000000) : ℝ) = ((5000000 / 5000937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5195_neg : (187417 / 1000000000) ≤ -Real.log (4999063 / 5000000) ∧
    -Real.log (4999063 / 5000000) ≤ (93709 / 500000000) := by
  have h := checkLog_sound (w := (937 / 9999063)) (n := 12)
    (lo := (187417 / 1000000000)) (hi := (93709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999063) = 1/(4999063 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5195 : Bounds (-93709 / 500000000) (-187417 / 1000000000) (Real.log (4999063 / 5000000)) := by
  have h := reflection_log_5195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5196_neg : (719859 / 8000000) ≤ -Real.log (200000 / 218831) ∧
    -Real.log (200000 / 218831) ≤ (11247797 / 125000000) := by
  have h := checkLog_sound (w := (18831 / 418831)) (n := 12)
    (lo := (719859 / 8000000)) (hi := (11247797 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218831 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218831 / 200000) = 1/(200000 / 218831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5196 : Bounds (719859 / 8000000) (11247797 / 125000000) (Real.log (218831 / 200000)) := by
  have h := reflection_log_5196_neg
  have he : Real.log (218831 / 200000) = -Real.log (200000 / 218831) := by
    rw [show ((218831 / 200000) : ℝ) = ((200000 / 218831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5197_neg : (98887069 / 1000000000) ≤ -Real.log (181169 / 200000) ∧
    -Real.log (181169 / 200000) ≤ (9888707 / 100000000) := by
  have h := checkLog_sound (w := (18831 / 381169)) (n := 12)
    (lo := (98887069 / 1000000000)) (hi := (9888707 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181169) = 1/(181169 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5197 : Bounds (-9888707 / 100000000) (-98887069 / 1000000000) (Real.log (181169 / 200000)) := by
  have h := reflection_log_5197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5198_neg : (90199871 / 1000000000) ≤ -Real.log (1000000 / 1094393) ∧
    -Real.log (1000000 / 1094393) ≤ (1409373 / 15625000) := by
  have h := checkLog_sound (w := (94393 / 2094393)) (n := 12)
    (lo := (90199871 / 1000000000)) (hi := (1409373 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094393 / 1000000) = 1/(1000000 / 1094393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5198 : Bounds (90199871 / 1000000000) (1409373 / 15625000) (Real.log (1094393 / 1000000)) := by
  have h := reflection_log_5198_neg
  have he : Real.log (1094393 / 1000000) = -Real.log (1000000 / 1094393) := by
    rw [show ((1094393 / 1000000) : ℝ) = ((1000000 / 1094393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5199_neg : (99149841 / 1000000000) ≤ -Real.log (905607 / 1000000) ∧
    -Real.log (905607 / 1000000) ≤ (49574921 / 500000000) := by
  have h := checkLog_sound (w := (94393 / 1905607)) (n := 12)
    (lo := (99149841 / 1000000000)) (hi := (49574921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905607) = 1/(905607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5199 : Bounds (-49574921 / 500000000) (-99149841 / 1000000000) (Real.log (905607 / 1000000)) := by
  have h := reflection_log_5199_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5200_neg : (894997 / 100000000) ≤ -Real.log (991089961551 / 1000000000000) ∧
    -Real.log (991089961551 / 1000000000000) ≤ (8949971 / 1000000000) := by
  have h := checkLog_sound (w := (8910038449 / 1991089961551)) (n := 12)
    (lo := (894997 / 100000000)) (hi := (8949971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991089961551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991089961551) = 1/(991089961551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5200 : Bounds (-8949971 / 1000000000) (-894997 / 100000000) (Real.log (991089961551 / 1000000000000)) := by
  have h := reflection_log_5200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5201_neg : (8904693 / 1000000000) ≤ -Real.log (39645393439 / 40000000000) ∧
    -Real.log (39645393439 / 40000000000) ≤ (4452347 / 500000000) := by
  have h := checkLog_sound (w := (354606561 / 79645393439)) (n := 12)
    (lo := (8904693 / 1000000000)) (hi := (4452347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39645393439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39645393439) = 1/(39645393439 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5201 : Bounds (-4452347 / 500000000) (-8904693 / 1000000000) (Real.log (39645393439 / 40000000000)) := by
  have h := reflection_log_5201_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5202_neg : (37773889 / 200000000) ≤ -Real.log (250000000000 / 301970811783) ∧
    -Real.log (250000000000 / 301970811783) ≤ (94434723 / 500000000) := by
  have h := checkLog_sound (w := (51970811783 / 551970811783)) (n := 12)
    (lo := (37773889 / 200000000)) (hi := (94434723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301970811783 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301970811783 / 250000000000) = 1/(250000000000 / 301970811783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5202 : Bounds (37773889 / 200000000) (94434723 / 500000000) (Real.log (301970811783 / 250000000000)) := by
  have h := reflection_log_5202_neg
  have he : Real.log (301970811783 / 250000000000) = -Real.log (250000000000 / 301970811783) := by
    rw [show ((301970811783 / 250000000000) : ℝ) = ((250000000000 / 301970811783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5203_neg : (189349713 / 1000000000) ≤ -Real.log (250000000000 / 302115873663) ∧
    -Real.log (250000000000 / 302115873663) ≤ (94674857 / 500000000) := by
  have h := checkLog_sound (w := (52115873663 / 552115873663)) (n := 12)
    (lo := (189349713 / 1000000000)) (hi := (94674857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302115873663 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302115873663 / 250000000000) = 1/(250000000000 / 302115873663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5203 : Bounds (189349713 / 1000000000) (94674857 / 500000000) (Real.log (302115873663 / 250000000000)) := by
  have h := reflection_log_5203_neg
  have he : Real.log (302115873663 / 250000000000) = -Real.log (250000000000 / 302115873663) := by
    rw [show ((302115873663 / 250000000000) : ℝ) = ((250000000000 / 302115873663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5204_neg : (189537531 / 500000000) ≤ -Real.log (100000000000 / 146093269349) ∧
    -Real.log (100000000000 / 146093269349) ≤ (379075063 / 1000000000) := by
  have h := checkLog_sound (w := (46093269349 / 246093269349)) (n := 12)
    (lo := (189537531 / 500000000)) (hi := (379075063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146093269349 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146093269349 / 100000000000) = 1/(100000000000 / 146093269349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5204 : Bounds (189537531 / 500000000) (379075063 / 1000000000) (Real.log (146093269349 / 100000000000)) := by
  have h := reflection_log_5204_neg
  have he : Real.log (146093269349 / 100000000000) = -Real.log (100000000000 / 146093269349) := by
    rw [show ((146093269349 / 100000000000) : ℝ) = ((100000000000 / 146093269349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5205_neg : (189641169 / 500000000) ≤ -Real.log (500000000000 / 730617770121) ∧
    -Real.log (500000000000 / 730617770121) ≤ (379282339 / 1000000000) := by
  have h := checkLog_sound (w := (230617770121 / 1230617770121)) (n := 12)
    (lo := (189641169 / 500000000)) (hi := (379282339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730617770121 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730617770121 / 500000000000) = 1/(500000000000 / 730617770121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5205 : Bounds (189641169 / 500000000) (379282339 / 1000000000) (Real.log (730617770121 / 500000000000)) := by
  have h := reflection_log_5205_neg
  have he : Real.log (730617770121 / 500000000000) = -Real.log (500000000000 / 730617770121) := by
    rw [show ((730617770121 / 500000000000) : ℝ) = ((500000000000 / 730617770121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5206_neg : (10740641 / 62500000) ≤ -Real.log (16 / 19) ∧
    -Real.log (16 / 19) ≤ (171850257 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 35)) (n := 12)
    (lo := (10740641 / 62500000)) (hi := (171850257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19 / 16) = 1/(16 / 19) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5206 : Bounds (10740641 / 62500000) (171850257 / 1000000000) (Real.log (19 / 16)) := by
  have h := reflection_log_5206_neg
  have he : Real.log (19 / 16) = -Real.log (16 / 19) := by
    rw [show ((19 / 16) : ℝ) = ((16 / 19) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5207_neg : (51909841 / 250000000) ≤ -Real.log (13 / 16) ∧
    -Real.log (13 / 16) ≤ (41527873 / 200000000) := by
  have h := checkLog_sound (w := (3 / 29)) (n := 12)
    (lo := (51909841 / 250000000)) (hi := (41527873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 13) = 1/(13 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5207 : Bounds (-41527873 / 200000000) (-51909841 / 250000000) (Real.log (13 / 16)) := by
  have h := reflection_log_5207_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5208_neg : (93741 / 500000000) ≤ -Real.log (16000 / 16003) ∧
    -Real.log (16000 / 16003) ≤ (187483 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 32003)) (n := 12)
    (lo := (93741 / 500000000)) (hi := (187483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16003 / 16000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16003 / 16000) = 1/(16000 / 16003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5208 : Bounds (93741 / 500000000) (187483 / 1000000000) (Real.log (16003 / 16000)) := by
  have h := reflection_log_5208_neg
  have he : Real.log (16003 / 16000) = -Real.log (16000 / 16003) := by
    rw [show ((16003 / 16000) : ℝ) = ((16000 / 16003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5209_neg : (187517 / 1000000000) ≤ -Real.log (15997 / 16000) ∧
    -Real.log (15997 / 16000) ≤ (93759 / 500000000) := by
  have h := checkLog_sound (w := (3 / 31997)) (n := 12)
    (lo := (187517 / 1000000000)) (hi := (93759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000 / 15997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000 / 15997) = 1/(15997 / 16000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5209 : Bounds (-93759 / 500000000) (-187517 / 1000000000) (Real.log (15997 / 16000)) := by
  have h := reflection_log_5209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5210_neg : (45014493 / 500000000) ≤ -Real.log (500000 / 547103) ∧
    -Real.log (500000 / 547103) ≤ (90028987 / 1000000000) := by
  have h := checkLog_sound (w := (47103 / 1047103)) (n := 12)
    (lo := (45014493 / 500000000)) (hi := (90028987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547103 / 500000) = 1/(500000 / 547103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5210 : Bounds (45014493 / 500000000) (90028987 / 1000000000) (Real.log (547103 / 500000)) := by
  have h := reflection_log_5210_neg
  have he : Real.log (547103 / 500000) = -Real.log (500000 / 547103) := by
    rw [show ((547103 / 500000) : ℝ) = ((500000 / 547103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5211_neg : (98943371 / 1000000000) ≤ -Real.log (452897 / 500000) ∧
    -Real.log (452897 / 500000) ≤ (24735843 / 250000000) := by
  have h := checkLog_sound (w := (47103 / 952897)) (n := 12)
    (lo := (98943371 / 1000000000)) (hi := (24735843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452897) = 1/(452897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5211 : Bounds (-24735843 / 250000000) (-98943371 / 1000000000) (Real.log (452897 / 500000)) := by
  have h := reflection_log_5211_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5212_neg : (90246471 / 1000000000) ≤ -Real.log (250000 / 273611) ∧
    -Real.log (250000 / 273611) ≤ (11280809 / 125000000) := by
  have h := checkLog_sound (w := (23611 / 523611)) (n := 12)
    (lo := (90246471 / 1000000000)) (hi := (11280809 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273611 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273611 / 250000) = 1/(250000 / 273611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5212 : Bounds (90246471 / 1000000000) (11280809 / 125000000) (Real.log (273611 / 250000)) := by
  have h := reflection_log_5212_neg
  have he : Real.log (273611 / 250000) = -Real.log (250000 / 273611) := by
    rw [show ((273611 / 250000) : ℝ) = ((250000 / 273611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5213_neg : (99206159 / 1000000000) ≤ -Real.log (226389 / 250000) ∧
    -Real.log (226389 / 250000) ≤ (1240077 / 12500000) := by
  have h := checkLog_sound (w := (23611 / 476389)) (n := 12)
    (lo := (99206159 / 1000000000)) (hi := (1240077 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226389) = 1/(226389 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5213 : Bounds (-1240077 / 12500000) (-99206159 / 1000000000) (Real.log (226389 / 250000)) := by
  have h := reflection_log_5213_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5214_neg : (8959687 / 1000000000) ≤ -Real.log (61942520679 / 62500000000) ∧
    -Real.log (61942520679 / 62500000000) ≤ (1119961 / 125000000) := by
  have h := checkLog_sound (w := (557479321 / 124442520679)) (n := 12)
    (lo := (8959687 / 1000000000)) (hi := (1119961 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61942520679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61942520679) = 1/(61942520679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5214 : Bounds (-1119961 / 125000000) (-8959687 / 1000000000) (Real.log (61942520679 / 62500000000)) := by
  have h := reflection_log_5214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5215_neg : (1782877 / 200000000) ≤ -Real.log (247781307391 / 250000000000) ∧
    -Real.log (247781307391 / 250000000000) ≤ (4457193 / 500000000) := by
  have h := checkLog_sound (w := (2218692609 / 497781307391)) (n := 12)
    (lo := (1782877 / 200000000)) (hi := (4457193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247781307391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247781307391) = 1/(247781307391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5215 : Bounds (-4457193 / 500000000) (-1782877 / 200000000) (Real.log (247781307391 / 250000000000)) := by
  have h := reflection_log_5215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5216_neg : (188972357 / 1000000000) ≤ -Real.log (125000000000 / 151000945027) ∧
    -Real.log (125000000000 / 151000945027) ≤ (94486179 / 500000000) := by
  have h := checkLog_sound (w := (26000945027 / 276000945027)) (n := 12)
    (lo := (188972357 / 1000000000)) (hi := (94486179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151000945027 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151000945027 / 125000000000) = 1/(125000000000 / 151000945027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5216 : Bounds (188972357 / 1000000000) (94486179 / 500000000) (Real.log (151000945027 / 125000000000)) := by
  have h := reflection_log_5216_neg
  have he : Real.log (151000945027 / 125000000000) = -Real.log (125000000000 / 151000945027) := by
    rw [show ((151000945027 / 125000000000) : ℝ) = ((125000000000 / 151000945027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5217_neg : (189452631 / 1000000000) ≤ -Real.log (500000000000 / 604293936543) ∧
    -Real.log (500000000000 / 604293936543) ≤ (23681579 / 125000000) := by
  have h := checkLog_sound (w := (104293936543 / 1104293936543)) (n := 12)
    (lo := (189452631 / 1000000000)) (hi := (23681579 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604293936543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604293936543 / 500000000000) = 1/(500000000000 / 604293936543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5217 : Bounds (189452631 / 1000000000) (23681579 / 125000000) (Real.log (604293936543 / 500000000000)) := by
  have h := reflection_log_5217_neg
  have he : Real.log (604293936543 / 500000000000) = -Real.log (500000000000 / 604293936543) := by
    rw [show ((604293936543 / 500000000000) : ℝ) = ((500000000000 / 604293936543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5218_neg : (189641169 / 500000000) ≤ -Real.log (12500000000 / 18265444253) ∧
    -Real.log (12500000000 / 18265444253) ≤ (379282339 / 1000000000) := by
  have h := checkLog_sound (w := (5765444253 / 30765444253)) (n := 12)
    (lo := (189641169 / 500000000)) (hi := (379282339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18265444253 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18265444253 / 12500000000) = 1/(12500000000 / 18265444253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5218 : Bounds (189641169 / 500000000) (379282339 / 1000000000) (Real.log (18265444253 / 12500000000)) := by
  have h := reflection_log_5218_neg
  have he : Real.log (18265444253 / 12500000000) = -Real.log (12500000000 / 18265444253) := by
    rw [show ((18265444253 / 12500000000) : ℝ) = ((12500000000 / 18265444253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5219_neg : (379489621 / 1000000000) ≤ -Real.log (50000000000 / 73076923077) ∧
    -Real.log (50000000000 / 73076923077) ≤ (189744811 / 500000000) := by
  have h := checkLog_sound (w := (23076923077 / 123076923077)) (n := 12)
    (lo := (379489621 / 1000000000)) (hi := (189744811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73076923077 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73076923077 / 50000000000) = 1/(50000000000 / 73076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5219 : Bounds (379489621 / 1000000000) (189744811 / 500000000) (Real.log (73076923077 / 50000000000)) := by
  have h := reflection_log_5219_neg
  have he : Real.log (73076923077 / 50000000000) = -Real.log (50000000000 / 73076923077) := by
    rw [show ((73076923077 / 50000000000) : ℝ) = ((50000000000 / 73076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5220_neg : (171934463 / 1000000000) ≤ -Real.log (2500 / 2969) ∧
    -Real.log (2500 / 2969) ≤ (671619 / 3906250) := by
  have h := checkLog_sound (w := (469 / 5469)) (n := 12)
    (lo := (171934463 / 1000000000)) (hi := (671619 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2969 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2969 / 2500) = 1/(2500 / 2969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5220 : Bounds (171934463 / 1000000000) (671619 / 3906250) (Real.log (2969 / 2500)) := by
  have h := reflection_log_5220_neg
  have he : Real.log (2969 / 2500) = -Real.log (2500 / 2969) := by
    rw [show ((2969 / 2500) : ℝ) = ((2500 / 2969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5221_neg : (207762449 / 1000000000) ≤ -Real.log (2031 / 2500) ∧
    -Real.log (2031 / 2500) ≤ (4155249 / 20000000) := by
  have h := checkLog_sound (w := (469 / 4531)) (n := 12)
    (lo := (207762449 / 1000000000)) (hi := (4155249 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2031) = 1/(2031 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5221 : Bounds (-4155249 / 20000000) (-207762449 / 1000000000) (Real.log (2031 / 2500)) := by
  have h := reflection_log_5221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5222_neg : (93791 / 500000000) ≤ -Real.log (2500000 / 2500469) ∧
    -Real.log (2500000 / 2500469) ≤ (187583 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 5000469)) (n := 12)
    (lo := (93791 / 500000000)) (hi := (187583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500469 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500469 / 2500000) = 1/(2500000 / 2500469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5222 : Bounds (93791 / 500000000) (187583 / 1000000000) (Real.log (2500469 / 2500000)) := by
  have h := reflection_log_5222_neg
  have he : Real.log (2500469 / 2500000) = -Real.log (2500000 / 2500469) := by
    rw [show ((2500469 / 2500000) : ℝ) = ((2500000 / 2500469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5223_neg : (187617 / 1000000000) ≤ -Real.log (2499531 / 2500000) ∧
    -Real.log (2499531 / 2500000) ≤ (93809 / 500000000) := by
  have h := checkLog_sound (w := (469 / 4999531)) (n := 12)
    (lo := (187617 / 1000000000)) (hi := (93809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499531) = 1/(2499531 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5223 : Bounds (-93809 / 500000000) (-187617 / 1000000000) (Real.log (2499531 / 2500000)) := by
  have h := reflection_log_5223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5224_neg : (45037797 / 500000000) ≤ -Real.log (1000000 / 1094257) ∧
    -Real.log (1000000 / 1094257) ≤ (18015119 / 200000000) := by
  have h := checkLog_sound (w := (94257 / 2094257)) (n := 12)
    (lo := (45037797 / 500000000)) (hi := (18015119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094257 / 1000000) = 1/(1000000 / 1094257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5224 : Bounds (45037797 / 500000000) (18015119 / 200000000) (Real.log (1094257 / 1000000)) := by
  have h := reflection_log_5224_neg
  have he : Real.log (1094257 / 1000000) = -Real.log (1000000 / 1094257) := by
    rw [show ((1094257 / 1000000) : ℝ) = ((1000000 / 1094257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5225_neg : (98999677 / 1000000000) ≤ -Real.log (905743 / 1000000) ∧
    -Real.log (905743 / 1000000) ≤ (49499839 / 500000000) := by
  have h := checkLog_sound (w := (94257 / 1905743)) (n := 12)
    (lo := (98999677 / 1000000000)) (hi := (49499839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905743) = 1/(905743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5225 : Bounds (-49499839 / 500000000) (-98999677 / 1000000000) (Real.log (905743 / 1000000)) := by
  have h := reflection_log_5225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5226_neg : (90293069 / 1000000000) ≤ -Real.log (200000 / 218899) ∧
    -Real.log (200000 / 218899) ≤ (9029307 / 100000000) := by
  have h := checkLog_sound (w := (18899 / 418899)) (n := 12)
    (lo := (90293069 / 1000000000)) (hi := (9029307 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218899 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218899 / 200000) = 1/(200000 / 218899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5226 : Bounds (90293069 / 1000000000) (9029307 / 100000000) (Real.log (218899 / 200000)) := by
  have h := reflection_log_5226_neg
  have he : Real.log (218899 / 200000) = -Real.log (200000 / 218899) := by
    rw [show ((218899 / 200000) : ℝ) = ((200000 / 218899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5227_neg : (99262479 / 1000000000) ≤ -Real.log (181101 / 200000) ∧
    -Real.log (181101 / 200000) ≤ (1240781 / 12500000) := by
  have h := checkLog_sound (w := (18899 / 381101)) (n := 12)
    (lo := (99262479 / 1000000000)) (hi := (1240781 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181101) = 1/(181101 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5227 : Bounds (-1240781 / 12500000) (-99262479 / 1000000000) (Real.log (181101 / 200000)) := by
  have h := reflection_log_5227_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5228_neg : (896941 / 100000000) ≤ -Real.log (39642827799 / 40000000000) ∧
    -Real.log (39642827799 / 40000000000) ≤ (8969411 / 1000000000) := by
  have h := checkLog_sound (w := (357172201 / 79642827799)) (n := 12)
    (lo := (896941 / 100000000)) (hi := (8969411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39642827799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39642827799) = 1/(39642827799 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5228 : Bounds (-8969411 / 1000000000) (-896941 / 100000000) (Real.log (39642827799 / 40000000000)) := by
  have h := reflection_log_5228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5229_neg : (8924083 / 1000000000) ≤ -Real.log (991115617951 / 1000000000000) ∧
    -Real.log (991115617951 / 1000000000000) ≤ (2231021 / 250000000) := by
  have h := checkLog_sound (w := (8884382049 / 1991115617951)) (n := 12)
    (lo := (8924083 / 1000000000)) (hi := (2231021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991115617951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991115617951) = 1/(991115617951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5229 : Bounds (-2231021 / 250000000) (-8924083 / 1000000000) (Real.log (991115617951 / 1000000000000)) := by
  have h := reflection_log_5229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5230_neg : (189075271 / 1000000000) ≤ -Real.log (10000000000 / 12081318873) ∧
    -Real.log (10000000000 / 12081318873) ≤ (23634409 / 125000000) := by
  have h := checkLog_sound (w := (2081318873 / 22081318873)) (n := 12)
    (lo := (189075271 / 1000000000)) (hi := (23634409 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12081318873 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12081318873 / 10000000000) = 1/(10000000000 / 12081318873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5230 : Bounds (189075271 / 1000000000) (23634409 / 125000000) (Real.log (12081318873 / 10000000000)) := by
  have h := reflection_log_5230_neg
  have he : Real.log (12081318873 / 10000000000) = -Real.log (10000000000 / 12081318873) := by
    rw [show ((12081318873 / 10000000000) : ℝ) = ((10000000000 / 12081318873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5231_neg : (189555549 / 1000000000) ≤ -Real.log (250000000000 / 302178066383) ∧
    -Real.log (250000000000 / 302178066383) ≤ (3791111 / 20000000) := by
  have h := checkLog_sound (w := (52178066383 / 552178066383)) (n := 12)
    (lo := (189555549 / 1000000000)) (hi := (3791111 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302178066383 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302178066383 / 250000000000) = 1/(250000000000 / 302178066383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5231 : Bounds (189555549 / 1000000000) (3791111 / 20000000) (Real.log (302178066383 / 250000000000)) := by
  have h := reflection_log_5231_neg
  have he : Real.log (302178066383 / 250000000000) = -Real.log (250000000000 / 302178066383) := by
    rw [show ((302178066383 / 250000000000) : ℝ) = ((250000000000 / 302178066383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5232_neg : (379489621 / 1000000000) ≤ -Real.log (500000000000 / 730769230769) ∧
    -Real.log (500000000000 / 730769230769) ≤ (189744811 / 500000000) := by
  have h := checkLog_sound (w := (230769230769 / 1230769230769)) (n := 12)
    (lo := (379489621 / 1000000000)) (hi := (189744811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730769230769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730769230769 / 500000000000) = 1/(500000000000 / 730769230769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5232 : Bounds (379489621 / 1000000000) (189744811 / 500000000) (Real.log (730769230769 / 500000000000)) := by
  have h := reflection_log_5232_neg
  have he : Real.log (730769230769 / 500000000000) = -Real.log (500000000000 / 730769230769) := by
    rw [show ((730769230769 / 500000000000) : ℝ) = ((500000000000 / 730769230769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5233_neg : (379696913 / 1000000000) ≤ -Real.log (250000000000 / 365460364353) ∧
    -Real.log (250000000000 / 365460364353) ≤ (189848457 / 500000000) := by
  have h := checkLog_sound (w := (115460364353 / 615460364353)) (n := 12)
    (lo := (379696913 / 1000000000)) (hi := (189848457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365460364353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365460364353 / 250000000000) = 1/(250000000000 / 365460364353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5233 : Bounds (379696913 / 1000000000) (189848457 / 500000000) (Real.log (365460364353 / 250000000000)) := by
  have h := reflection_log_5233_neg
  have he : Real.log (365460364353 / 250000000000) = -Real.log (250000000000 / 365460364353) := by
    rw [show ((365460364353 / 250000000000) : ℝ) = ((250000000000 / 365460364353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5234_neg : (172018663 / 1000000000) ≤ -Real.log (10000 / 11877) ∧
    -Real.log (10000 / 11877) ≤ (21502333 / 125000000) := by
  have h := checkLog_sound (w := (1877 / 21877)) (n := 12)
    (lo := (172018663 / 1000000000)) (hi := (21502333 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11877 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11877 / 10000) = 1/(10000 / 11877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5234 : Bounds (172018663 / 1000000000) (21502333 / 125000000) (Real.log (11877 / 10000)) := by
  have h := reflection_log_5234_neg
  have he : Real.log (11877 / 10000) = -Real.log (10000 / 11877) := by
    rw [show ((11877 / 10000) : ℝ) = ((10000 / 11877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5235_neg : (51971387 / 250000000) ≤ -Real.log (8123 / 10000) ∧
    -Real.log (8123 / 10000) ≤ (207885549 / 1000000000) := by
  have h := checkLog_sound (w := (1877 / 18123)) (n := 12)
    (lo := (51971387 / 250000000)) (hi := (207885549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8123) = 1/(8123 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5235 : Bounds (-207885549 / 1000000000) (-51971387 / 250000000) (Real.log (8123 / 10000)) := by
  have h := reflection_log_5235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5236_neg : (93841 / 500000000) ≤ -Real.log (10000000 / 10001877) ∧
    -Real.log (10000000 / 10001877) ≤ (187683 / 1000000000) := by
  have h := checkLog_sound (w := (1877 / 20001877)) (n := 12)
    (lo := (93841 / 500000000)) (hi := (187683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001877 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001877 / 10000000) = 1/(10000000 / 10001877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5236 : Bounds (93841 / 500000000) (187683 / 1000000000) (Real.log (10001877 / 10000000)) := by
  have h := reflection_log_5236_neg
  have he : Real.log (10001877 / 10000000) = -Real.log (10000000 / 10001877) := by
    rw [show ((10001877 / 10000000) : ℝ) = ((10000000 / 10001877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5237_neg : (187717 / 1000000000) ≤ -Real.log (9998123 / 10000000) ∧
    -Real.log (9998123 / 10000000) ≤ (93859 / 500000000) := by
  have h := checkLog_sound (w := (1877 / 19998123)) (n := 12)
    (lo := (187717 / 1000000000)) (hi := (93859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998123) = 1/(9998123 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5237 : Bounds (-93859 / 500000000) (-187717 / 1000000000) (Real.log (9998123 / 10000000)) := by
  have h := reflection_log_5237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5238_neg : (450611 / 5000000) ≤ -Real.log (250000 / 273577) ∧
    -Real.log (250000 / 273577) ≤ (90122201 / 1000000000) := by
  have h := checkLog_sound (w := (23577 / 523577)) (n := 12)
    (lo := (450611 / 5000000)) (hi := (90122201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273577 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273577 / 250000) = 1/(250000 / 273577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5238 : Bounds (450611 / 5000000) (90122201 / 1000000000) (Real.log (273577 / 250000)) := by
  have h := reflection_log_5238_neg
  have he : Real.log (273577 / 250000) = -Real.log (250000 / 273577) := by
    rw [show ((273577 / 250000) : ℝ) = ((250000 / 273577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5239_neg : (49527993 / 500000000) ≤ -Real.log (226423 / 250000) ∧
    -Real.log (226423 / 250000) ≤ (99055987 / 1000000000) := by
  have h := checkLog_sound (w := (23577 / 476423)) (n := 12)
    (lo := (49527993 / 500000000)) (hi := (99055987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226423) = 1/(226423 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5239 : Bounds (-99055987 / 1000000000) (-49527993 / 500000000) (Real.log (226423 / 250000)) := by
  have h := reflection_log_5239_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5240_neg : (18067933 / 200000000) ≤ -Real.log (500000 / 547273) ∧
    -Real.log (500000 / 547273) ≤ (45169833 / 500000000) := by
  have h := checkLog_sound (w := (47273 / 1047273)) (n := 12)
    (lo := (18067933 / 200000000)) (hi := (45169833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547273 / 500000) = 1/(500000 / 547273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5240 : Bounds (18067933 / 200000000) (45169833 / 500000000) (Real.log (547273 / 500000)) := by
  have h := reflection_log_5240_neg
  have he : Real.log (547273 / 500000) = -Real.log (500000 / 547273) := by
    rw [show ((547273 / 500000) : ℝ) = ((500000 / 547273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5241_neg : (99318803 / 1000000000) ≤ -Real.log (452727 / 500000) ∧
    -Real.log (452727 / 500000) ≤ (24829701 / 250000000) := by
  have h := checkLog_sound (w := (47273 / 952727)) (n := 12)
    (lo := (99318803 / 1000000000)) (hi := (24829701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452727) = 1/(452727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5241 : Bounds (-24829701 / 250000000) (-99318803 / 1000000000) (Real.log (452727 / 500000)) := by
  have h := reflection_log_5241_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5242_neg : (4489569 / 500000000) ≤ -Real.log (247765263471 / 250000000000) ∧
    -Real.log (247765263471 / 250000000000) ≤ (8979139 / 1000000000) := by
  have h := checkLog_sound (w := (2234736529 / 497765263471)) (n := 12)
    (lo := (4489569 / 500000000)) (hi := (8979139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247765263471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247765263471) = 1/(247765263471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5242 : Bounds (-8979139 / 1000000000) (-4489569 / 500000000) (Real.log (247765263471 / 250000000000)) := by
  have h := reflection_log_5242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5243_neg : (4466893 / 500000000) ≤ -Real.log (61944125071 / 62500000000) ∧
    -Real.log (61944125071 / 62500000000) ≤ (8933787 / 1000000000) := by
  have h := checkLog_sound (w := (555874929 / 124444125071)) (n := 12)
    (lo := (4466893 / 500000000)) (hi := (8933787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61944125071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61944125071) = 1/(61944125071 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5243 : Bounds (-8933787 / 1000000000) (-4466893 / 500000000) (Real.log (61944125071 / 62500000000)) := by
  have h := reflection_log_5243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5244_neg : (94589093 / 500000000) ≤ -Real.log (500000000000 / 604128114193) ∧
    -Real.log (500000000000 / 604128114193) ≤ (189178187 / 1000000000) := by
  have h := checkLog_sound (w := (104128114193 / 1104128114193)) (n := 12)
    (lo := (94589093 / 500000000)) (hi := (189178187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604128114193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604128114193 / 500000000000) = 1/(500000000000 / 604128114193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5244 : Bounds (94589093 / 500000000) (189178187 / 1000000000) (Real.log (604128114193 / 500000000000)) := by
  have h := reflection_log_5244_neg
  have he : Real.log (604128114193 / 500000000000) = -Real.log (500000000000 / 604128114193) := by
    rw [show ((604128114193 / 500000000000) : ℝ) = ((500000000000 / 604128114193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5245_neg : (189658469 / 1000000000) ≤ -Real.log (100000000000 / 120883667199) ∧
    -Real.log (100000000000 / 120883667199) ≤ (18965847 / 100000000) := by
  have h := checkLog_sound (w := (20883667199 / 220883667199)) (n := 12)
    (lo := (189658469 / 1000000000)) (hi := (18965847 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120883667199 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120883667199 / 100000000000) = 1/(100000000000 / 120883667199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5245 : Bounds (189658469 / 1000000000) (18965847 / 100000000) (Real.log (120883667199 / 100000000000)) := by
  have h := reflection_log_5245_neg
  have he : Real.log (120883667199 / 100000000000) = -Real.log (100000000000 / 120883667199) := by
    rw [show ((120883667199 / 100000000000) : ℝ) = ((100000000000 / 120883667199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5246_neg : (379696913 / 1000000000) ≤ -Real.log (100000000000 / 146184145741) ∧
    -Real.log (100000000000 / 146184145741) ≤ (189848457 / 500000000) := by
  have h := checkLog_sound (w := (46184145741 / 246184145741)) (n := 12)
    (lo := (379696913 / 1000000000)) (hi := (189848457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146184145741 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146184145741 / 100000000000) = 1/(100000000000 / 146184145741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5246 : Bounds (379696913 / 1000000000) (189848457 / 500000000) (Real.log (146184145741 / 100000000000)) := by
  have h := reflection_log_5246_neg
  have he : Real.log (146184145741 / 100000000000) = -Real.log (100000000000 / 146184145741) := by
    rw [show ((146184145741 / 100000000000) : ℝ) = ((100000000000 / 146184145741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5247_neg : (94976053 / 250000000) ≤ -Real.log (250000000000 / 365536131971) ∧
    -Real.log (250000000000 / 365536131971) ≤ (379904213 / 1000000000) := by
  have h := checkLog_sound (w := (115536131971 / 615536131971)) (n := 12)
    (lo := (94976053 / 250000000)) (hi := (379904213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365536131971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365536131971 / 250000000000) = 1/(250000000000 / 365536131971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5247 : Bounds (94976053 / 250000000) (379904213 / 1000000000) (Real.log (365536131971 / 250000000000)) := by
  have h := reflection_log_5247_neg
  have he : Real.log (365536131971 / 250000000000) = -Real.log (250000000000 / 365536131971) := by
    rw [show ((365536131971 / 250000000000) : ℝ) = ((250000000000 / 365536131971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0082 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5248_neg : (21512857 / 125000000) ≤ -Real.log (5000 / 5939) ∧
    -Real.log (5000 / 5939) ≤ (172102857 / 1000000000) := by
  have h := checkLog_sound (w := (939 / 10939)) (n := 12)
    (lo := (21512857 / 125000000)) (hi := (172102857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5939 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5939 / 5000) = 1/(5000 / 5939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5248 : Bounds (21512857 / 125000000) (172102857 / 1000000000) (Real.log (5939 / 5000)) := by
  have h := reflection_log_5248_neg
  have he : Real.log (5939 / 5000) = -Real.log (5000 / 5939) := by
    rw [show ((5939 / 5000) : ℝ) = ((5000 / 5939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5249_neg : (208008663 / 1000000000) ≤ -Real.log (4061 / 5000) ∧
    -Real.log (4061 / 5000) ≤ (26001083 / 125000000) := by
  have h := checkLog_sound (w := (939 / 9061)) (n := 12)
    (lo := (208008663 / 1000000000)) (hi := (26001083 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4061) = 1/(4061 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5249 : Bounds (-26001083 / 125000000) (-208008663 / 1000000000) (Real.log (4061 / 5000)) := by
  have h := reflection_log_5249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5250_neg : (93891 / 500000000) ≤ -Real.log (5000000 / 5000939) ∧
    -Real.log (5000000 / 5000939) ≤ (187783 / 1000000000) := by
  have h := checkLog_sound (w := (939 / 10000939)) (n := 12)
    (lo := (93891 / 500000000)) (hi := (187783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000939 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000939 / 5000000) = 1/(5000000 / 5000939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5250 : Bounds (93891 / 500000000) (187783 / 1000000000) (Real.log (5000939 / 5000000)) := by
  have h := reflection_log_5250_neg
  have he : Real.log (5000939 / 5000000) = -Real.log (5000000 / 5000939) := by
    rw [show ((5000939 / 5000000) : ℝ) = ((5000000 / 5000939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5251_neg : (187817 / 1000000000) ≤ -Real.log (4999061 / 5000000) ∧
    -Real.log (4999061 / 5000000) ≤ (93909 / 500000000) := by
  have h := checkLog_sound (w := (939 / 9999061)) (n := 12)
    (lo := (187817 / 1000000000)) (hi := (93909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999061) = 1/(4999061 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5251 : Bounds (-93909 / 500000000) (-187817 / 1000000000) (Real.log (4999061 / 5000000)) := by
  have h := reflection_log_5251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5252_neg : (90168803 / 1000000000) ≤ -Real.log (1000000 / 1094359) ∧
    -Real.log (1000000 / 1094359) ≤ (22542201 / 250000000) := by
  have h := checkLog_sound (w := (94359 / 2094359)) (n := 12)
    (lo := (90168803 / 1000000000)) (hi := (22542201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094359 / 1000000) = 1/(1000000 / 1094359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5252 : Bounds (90168803 / 1000000000) (22542201 / 250000000) (Real.log (1094359 / 1000000)) := by
  have h := reflection_log_5252_neg
  have he : Real.log (1094359 / 1000000) = -Real.log (1000000 / 1094359) := by
    rw [show ((1094359 / 1000000) : ℝ) = ((1000000 / 1094359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5253_neg : (49556149 / 500000000) ≤ -Real.log (905641 / 1000000) ∧
    -Real.log (905641 / 1000000) ≤ (99112299 / 1000000000) := by
  have h := checkLog_sound (w := (94359 / 1905641)) (n := 12)
    (lo := (49556149 / 500000000)) (hi := (99112299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905641) = 1/(905641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5253 : Bounds (-99112299 / 1000000000) (-49556149 / 500000000) (Real.log (905641 / 1000000)) := by
  have h := reflection_log_5253_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5254_neg : (45193129 / 500000000) ≤ -Real.log (1000000 / 1094597) ∧
    -Real.log (1000000 / 1094597) ≤ (90386259 / 1000000000) := by
  have h := checkLog_sound (w := (94597 / 2094597)) (n := 12)
    (lo := (45193129 / 500000000)) (hi := (90386259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094597 / 1000000) = 1/(1000000 / 1094597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5254 : Bounds (45193129 / 500000000) (90386259 / 1000000000) (Real.log (1094597 / 1000000)) := by
  have h := reflection_log_5254_neg
  have he : Real.log (1094597 / 1000000) = -Real.log (1000000 / 1094597) := by
    rw [show ((1094597 / 1000000) : ℝ) = ((1000000 / 1094597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5255_neg : (9937513 / 100000000) ≤ -Real.log (905403 / 1000000) ∧
    -Real.log (905403 / 1000000) ≤ (99375131 / 1000000000) := by
  have h := checkLog_sound (w := (94597 / 1905403)) (n := 12)
    (lo := (9937513 / 100000000)) (hi := (99375131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905403) = 1/(905403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5255 : Bounds (-99375131 / 1000000000) (-9937513 / 100000000) (Real.log (905403 / 1000000)) := by
  have h := reflection_log_5255_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5256_neg : (8988871 / 1000000000) ≤ -Real.log (991051407591 / 1000000000000) ∧
    -Real.log (991051407591 / 1000000000000) ≤ (1123609 / 125000000) := by
  have h := checkLog_sound (w := (8948592409 / 1991051407591)) (n := 12)
    (lo := (8988871 / 1000000000)) (hi := (1123609 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991051407591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991051407591) = 1/(991051407591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5256 : Bounds (-1123609 / 125000000) (-8988871 / 1000000000) (Real.log (991051407591 / 1000000000000)) := by
  have h := reflection_log_5256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5257_neg : (4471747 / 500000000) ≤ -Real.log (991096379119 / 1000000000000) ∧
    -Real.log (991096379119 / 1000000000000) ≤ (1788699 / 200000000) := by
  have h := checkLog_sound (w := (8903620881 / 1991096379119)) (n := 12)
    (lo := (4471747 / 500000000)) (hi := (1788699 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991096379119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991096379119) = 1/(991096379119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5257 : Bounds (-1788699 / 200000000) (-4471747 / 500000000) (Real.log (991096379119 / 1000000000000)) := by
  have h := reflection_log_5257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5258_neg : (94640551 / 500000000) ≤ -Real.log (250000000000 / 302095145869) ∧
    -Real.log (250000000000 / 302095145869) ≤ (189281103 / 1000000000) := by
  have h := checkLog_sound (w := (52095145869 / 552095145869)) (n := 12)
    (lo := (94640551 / 500000000)) (hi := (189281103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302095145869 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302095145869 / 250000000000) = 1/(250000000000 / 302095145869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5258 : Bounds (94640551 / 500000000) (189281103 / 1000000000) (Real.log (302095145869 / 250000000000)) := by
  have h := reflection_log_5258_neg
  have he : Real.log (302095145869 / 250000000000) = -Real.log (250000000000 / 302095145869) := by
    rw [show ((302095145869 / 250000000000) : ℝ) = ((250000000000 / 302095145869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5259_neg : (189761389 / 1000000000) ≤ -Real.log (62500000000 / 75560068279) ∧
    -Real.log (62500000000 / 75560068279) ≤ (18976139 / 100000000) := by
  have h := checkLog_sound (w := (13060068279 / 138060068279)) (n := 12)
    (lo := (189761389 / 1000000000)) (hi := (18976139 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75560068279 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75560068279 / 62500000000) = 1/(62500000000 / 75560068279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5259 : Bounds (189761389 / 1000000000) (18976139 / 100000000) (Real.log (75560068279 / 62500000000)) := by
  have h := reflection_log_5259_neg
  have he : Real.log (75560068279 / 62500000000) = -Real.log (62500000000 / 75560068279) := by
    rw [show ((75560068279 / 62500000000) : ℝ) = ((62500000000 / 75560068279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5260_neg : (94976053 / 250000000) ≤ -Real.log (500000000000 / 731072263941) ∧
    -Real.log (500000000000 / 731072263941) ≤ (379904213 / 1000000000) := by
  have h := checkLog_sound (w := (231072263941 / 1231072263941)) (n := 12)
    (lo := (94976053 / 250000000)) (hi := (379904213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731072263941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731072263941 / 500000000000) = 1/(500000000000 / 731072263941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5260 : Bounds (94976053 / 250000000) (379904213 / 1000000000) (Real.log (731072263941 / 500000000000)) := by
  have h := reflection_log_5260_neg
  have he : Real.log (731072263941 / 500000000000) = -Real.log (500000000000 / 731072263941) := by
    rw [show ((731072263941 / 500000000000) : ℝ) = ((500000000000 / 731072263941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5261_neg : (2375697 / 6250000) ≤ -Real.log (250000000000 / 365611918247) ∧
    -Real.log (250000000000 / 365611918247) ≤ (380111521 / 1000000000) := by
  have h := checkLog_sound (w := (115611918247 / 615611918247)) (n := 12)
    (lo := (2375697 / 6250000)) (hi := (380111521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365611918247 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365611918247 / 250000000000) = 1/(250000000000 / 365611918247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5261 : Bounds (2375697 / 6250000) (380111521 / 1000000000) (Real.log (365611918247 / 250000000000)) := by
  have h := reflection_log_5261_neg
  have he : Real.log (365611918247 / 250000000000) = -Real.log (250000000000 / 365611918247) := by
    rw [show ((365611918247 / 250000000000) : ℝ) = ((250000000000 / 365611918247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5262_neg : (86093521 / 500000000) ≤ -Real.log (10000 / 11879) ∧
    -Real.log (10000 / 11879) ≤ (172187043 / 1000000000) := by
  have h := checkLog_sound (w := (1879 / 21879)) (n := 12)
    (lo := (86093521 / 500000000)) (hi := (172187043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11879 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11879 / 10000) = 1/(10000 / 11879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5262 : Bounds (86093521 / 500000000) (172187043 / 1000000000) (Real.log (11879 / 10000)) := by
  have h := reflection_log_5262_neg
  have he : Real.log (11879 / 10000) = -Real.log (10000 / 11879) := by
    rw [show ((11879 / 10000) : ℝ) = ((10000 / 11879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5263_neg : (208131793 / 1000000000) ≤ -Real.log (8121 / 10000) ∧
    -Real.log (8121 / 10000) ≤ (104065897 / 500000000) := by
  have h := checkLog_sound (w := (1879 / 18121)) (n := 12)
    (lo := (208131793 / 1000000000)) (hi := (104065897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8121) = 1/(8121 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5263 : Bounds (-104065897 / 500000000) (-208131793 / 1000000000) (Real.log (8121 / 10000)) := by
  have h := reflection_log_5263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5264_neg : (93941 / 500000000) ≤ -Real.log (10000000 / 10001879) ∧
    -Real.log (10000000 / 10001879) ≤ (187883 / 1000000000) := by
  have h := checkLog_sound (w := (1879 / 20001879)) (n := 12)
    (lo := (93941 / 500000000)) (hi := (187883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001879 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001879 / 10000000) = 1/(10000000 / 10001879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5264 : Bounds (93941 / 500000000) (187883 / 1000000000) (Real.log (10001879 / 10000000)) := by
  have h := reflection_log_5264_neg
  have he : Real.log (10001879 / 10000000) = -Real.log (10000000 / 10001879) := by
    rw [show ((10001879 / 10000000) : ℝ) = ((10000000 / 10001879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5265_neg : (187917 / 1000000000) ≤ -Real.log (9998121 / 10000000) ∧
    -Real.log (9998121 / 10000000) ≤ (93959 / 500000000) := by
  have h := checkLog_sound (w := (1879 / 19998121)) (n := 12)
    (lo := (187917 / 1000000000)) (hi := (93959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998121) = 1/(9998121 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5265 : Bounds (-93959 / 500000000) (-187917 / 1000000000) (Real.log (9998121 / 10000000)) := by
  have h := reflection_log_5265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5266_neg : (18043081 / 200000000) ≤ -Real.log (100000 / 109441) ∧
    -Real.log (100000 / 109441) ≤ (45107703 / 500000000) := by
  have h := checkLog_sound (w := (9441 / 209441)) (n := 12)
    (lo := (18043081 / 200000000)) (hi := (45107703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109441 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109441 / 100000) = 1/(100000 / 109441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5266 : Bounds (18043081 / 200000000) (45107703 / 500000000) (Real.log (109441 / 100000)) := by
  have h := reflection_log_5266_neg
  have he : Real.log (109441 / 100000) = -Real.log (100000 / 109441) := by
    rw [show ((109441 / 100000) : ℝ) = ((100000 / 109441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5267_neg : (99168613 / 1000000000) ≤ -Real.log (90559 / 100000) ∧
    -Real.log (90559 / 100000) ≤ (49584307 / 500000000) := by
  have h := checkLog_sound (w := (9441 / 190559)) (n := 12)
    (lo := (99168613 / 1000000000)) (hi := (49584307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90559) = 1/(90559 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5267 : Bounds (-49584307 / 500000000) (-99168613 / 1000000000) (Real.log (90559 / 100000)) := by
  have h := reflection_log_5267_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5268_neg : (1808657 / 20000000) ≤ -Real.log (125000 / 136831) ∧
    -Real.log (125000 / 136831) ≤ (90432851 / 1000000000) := by
  have h := checkLog_sound (w := (11831 / 261831)) (n := 12)
    (lo := (1808657 / 20000000)) (hi := (90432851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136831 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136831 / 125000) = 1/(125000 / 136831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5268 : Bounds (1808657 / 20000000) (90432851 / 1000000000) (Real.log (136831 / 125000)) := by
  have h := reflection_log_5268_neg
  have he : Real.log (136831 / 125000) = -Real.log (125000 / 136831) := by
    rw [show ((136831 / 125000) : ℝ) = ((125000 / 136831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5269_neg : (4971573 / 50000000) ≤ -Real.log (113169 / 125000) ∧
    -Real.log (113169 / 125000) ≤ (99431461 / 1000000000) := by
  have h := checkLog_sound (w := (11831 / 238169)) (n := 12)
    (lo := (4971573 / 50000000)) (hi := (99431461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113169) = 1/(113169 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5269 : Bounds (-99431461 / 1000000000) (-4971573 / 50000000) (Real.log (113169 / 125000)) := by
  have h := reflection_log_5269_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5270_neg : (899861 / 100000000) ≤ -Real.log (15485027439 / 15625000000) ∧
    -Real.log (15485027439 / 15625000000) ≤ (8998611 / 1000000000) := by
  have h := checkLog_sound (w := (139972561 / 31110027439)) (n := 12)
    (lo := (899861 / 100000000)) (hi := (8998611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15485027439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15485027439) = 1/(15485027439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5270 : Bounds (-8998611 / 1000000000) (-899861 / 100000000) (Real.log (15485027439 / 15625000000)) := by
  have h := reflection_log_5270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5271_neg : (1119151 / 125000000) ≤ -Real.log (9910867519 / 10000000000) ∧
    -Real.log (9910867519 / 10000000000) ≤ (8953209 / 1000000000) := by
  have h := checkLog_sound (w := (89132481 / 19910867519)) (n := 12)
    (lo := (1119151 / 125000000)) (hi := (8953209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9910867519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9910867519) = 1/(9910867519 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5271 : Bounds (-8953209 / 1000000000) (-1119151 / 125000000) (Real.log (9910867519 / 10000000000)) := by
  have h := reflection_log_5271_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5272_neg : (189384019 / 1000000000) ≤ -Real.log (250000000000 / 302126238143) ∧
    -Real.log (250000000000 / 302126238143) ≤ (9469201 / 50000000) := by
  have h := checkLog_sound (w := (52126238143 / 552126238143)) (n := 12)
    (lo := (189384019 / 1000000000)) (hi := (9469201 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302126238143 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302126238143 / 250000000000) = 1/(250000000000 / 302126238143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5272 : Bounds (189384019 / 1000000000) (9469201 / 50000000) (Real.log (302126238143 / 250000000000)) := by
  have h := reflection_log_5272_neg
  have he : Real.log (302126238143 / 250000000000) = -Real.log (250000000000 / 302126238143) := by
    rw [show ((302126238143 / 250000000000) : ℝ) = ((250000000000 / 302126238143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5273_neg : (189864311 / 1000000000) ≤ -Real.log (250000000000 / 302271381739) ∧
    -Real.log (250000000000 / 302271381739) ≤ (23733039 / 125000000) := by
  have h := checkLog_sound (w := (52271381739 / 552271381739)) (n := 12)
    (lo := (189864311 / 1000000000)) (hi := (23733039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302271381739 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302271381739 / 250000000000) = 1/(250000000000 / 302271381739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5273 : Bounds (189864311 / 1000000000) (23733039 / 125000000) (Real.log (302271381739 / 250000000000)) := by
  have h := reflection_log_5273_neg
  have he : Real.log (302271381739 / 250000000000) = -Real.log (250000000000 / 302271381739) := by
    rw [show ((302271381739 / 250000000000) : ℝ) = ((250000000000 / 302271381739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5274_neg : (2375697 / 6250000) ≤ -Real.log (500000000000 / 731223836493) ∧
    -Real.log (500000000000 / 731223836493) ≤ (380111521 / 1000000000) := by
  have h := checkLog_sound (w := (231223836493 / 1231223836493)) (n := 12)
    (lo := (2375697 / 6250000)) (hi := (380111521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731223836493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731223836493 / 500000000000) = 1/(500000000000 / 731223836493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5274 : Bounds (2375697 / 6250000) (380111521 / 1000000000) (Real.log (731223836493 / 500000000000)) := by
  have h := reflection_log_5274_neg
  have he : Real.log (731223836493 / 500000000000) = -Real.log (500000000000 / 731223836493) := by
    rw [show ((731223836493 / 500000000000) : ℝ) = ((500000000000 / 731223836493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5275_neg : (95079709 / 250000000) ≤ -Real.log (250000000000 / 365687723187) ∧
    -Real.log (250000000000 / 365687723187) ≤ (380318837 / 1000000000) := by
  have h := checkLog_sound (w := (115687723187 / 615687723187)) (n := 12)
    (lo := (95079709 / 250000000)) (hi := (380318837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365687723187 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365687723187 / 250000000000) = 1/(250000000000 / 365687723187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5275 : Bounds (95079709 / 250000000) (380318837 / 1000000000) (Real.log (365687723187 / 250000000000)) := by
  have h := reflection_log_5275_neg
  have he : Real.log (365687723187 / 250000000000) = -Real.log (250000000000 / 365687723187) := by
    rw [show ((365687723187 / 250000000000) : ℝ) = ((250000000000 / 365687723187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5276_neg : (8613561 / 50000000) ≤ -Real.log (250 / 297) ∧
    -Real.log (250 / 297) ≤ (172271221 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 547)) (n := 12)
    (lo := (8613561 / 50000000)) (hi := (172271221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297 / 250) = 1/(250 / 297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5276 : Bounds (8613561 / 50000000) (172271221 / 1000000000) (Real.log (297 / 250)) := by
  have h := reflection_log_5276_neg
  have he : Real.log (297 / 250) = -Real.log (250 / 297) := by
    rw [show ((297 / 250) : ℝ) = ((250 / 297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5277_neg : (104127469 / 500000000) ≤ -Real.log (203 / 250) ∧
    -Real.log (203 / 250) ≤ (208254939 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 453)) (n := 12)
    (lo := (104127469 / 500000000)) (hi := (208254939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 203) = 1/(203 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5277 : Bounds (-208254939 / 1000000000) (-104127469 / 500000000) (Real.log (203 / 250)) := by
  have h := reflection_log_5277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5278_neg : (93991 / 500000000) ≤ -Real.log (250000 / 250047) ∧
    -Real.log (250000 / 250047) ≤ (187983 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 500047)) (n := 12)
    (lo := (93991 / 500000000)) (hi := (187983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250047 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250047 / 250000) = 1/(250000 / 250047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5278 : Bounds (93991 / 500000000) (187983 / 1000000000) (Real.log (250047 / 250000)) := by
  have h := reflection_log_5278_neg
  have he : Real.log (250047 / 250000) = -Real.log (250000 / 250047) := by
    rw [show ((250047 / 250000) : ℝ) = ((250000 / 250047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5279_neg : (188017 / 1000000000) ≤ -Real.log (249953 / 250000) ∧
    -Real.log (249953 / 250000) ≤ (94009 / 500000000) := by
  have h := checkLog_sound (w := (47 / 499953)) (n := 12)
    (lo := (188017 / 1000000000)) (hi := (94009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249953) = 1/(249953 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5279 : Bounds (-94009 / 500000000) (-188017 / 1000000000) (Real.log (249953 / 250000)) := by
  have h := reflection_log_5279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5280_neg : (22565501 / 250000000) ≤ -Real.log (1000000 / 1094461) ∧
    -Real.log (1000000 / 1094461) ≤ (18052401 / 200000000) := by
  have h := checkLog_sound (w := (94461 / 2094461)) (n := 12)
    (lo := (22565501 / 250000000)) (hi := (18052401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094461 / 1000000) = 1/(1000000 / 1094461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5280 : Bounds (22565501 / 250000000) (18052401 / 200000000) (Real.log (1094461 / 1000000)) := by
  have h := reflection_log_5280_neg
  have he : Real.log (1094461 / 1000000) = -Real.log (1000000 / 1094461) := by
    rw [show ((1094461 / 1000000) : ℝ) = ((1000000 / 1094461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5281_neg : (24806233 / 250000000) ≤ -Real.log (905539 / 1000000) ∧
    -Real.log (905539 / 1000000) ≤ (99224933 / 1000000000) := by
  have h := checkLog_sound (w := (94461 / 1905539)) (n := 12)
    (lo := (24806233 / 250000000)) (hi := (99224933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905539) = 1/(905539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5281 : Bounds (-99224933 / 1000000000) (-24806233 / 250000000) (Real.log (905539 / 1000000)) := by
  have h := reflection_log_5281_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5282_neg : (90479439 / 1000000000) ≤ -Real.log (1000000 / 1094699) ∧
    -Real.log (1000000 / 1094699) ≤ (1130993 / 12500000) := by
  have h := checkLog_sound (w := (94699 / 2094699)) (n := 12)
    (lo := (90479439 / 1000000000)) (hi := (1130993 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094699 / 1000000) = 1/(1000000 / 1094699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5282 : Bounds (90479439 / 1000000000) (1130993 / 12500000) (Real.log (1094699 / 1000000)) := by
  have h := reflection_log_5282_neg
  have he : Real.log (1094699 / 1000000) = -Real.log (1000000 / 1094699) := by
    rw [show ((1094699 / 1000000) : ℝ) = ((1000000 / 1094699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5283_neg : (99487793 / 1000000000) ≤ -Real.log (905301 / 1000000) ∧
    -Real.log (905301 / 1000000) ≤ (49743897 / 500000000) := by
  have h := checkLog_sound (w := (94699 / 1905301)) (n := 12)
    (lo := (99487793 / 1000000000)) (hi := (49743897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905301) = 1/(905301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5283 : Bounds (-49743897 / 500000000) (-99487793 / 1000000000) (Real.log (905301 / 1000000)) := by
  have h := reflection_log_5283_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5284_neg : (4504177 / 500000000) ≤ -Real.log (991032099399 / 1000000000000) ∧
    -Real.log (991032099399 / 1000000000000) ≤ (1801671 / 200000000) := by
  have h := checkLog_sound (w := (8967900601 / 1991032099399)) (n := 12)
    (lo := (4504177 / 500000000)) (hi := (1801671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991032099399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991032099399) = 1/(991032099399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5284 : Bounds (-1801671 / 200000000) (-4504177 / 500000000) (Real.log (991032099399 / 1000000000000)) := by
  have h := reflection_log_5284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5285_neg : (8962927 / 1000000000) ≤ -Real.log (991077119479 / 1000000000000) ∧
    -Real.log (991077119479 / 1000000000000) ≤ (560183 / 62500000) := by
  have h := checkLog_sound (w := (8922880521 / 1991077119479)) (n := 12)
    (lo := (8962927 / 1000000000)) (hi := (560183 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991077119479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991077119479) = 1/(991077119479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5285 : Bounds (-560183 / 62500000) (-8962927 / 1000000000) (Real.log (991077119479 / 1000000000000)) := by
  have h := reflection_log_5285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5286_neg : (189486937 / 1000000000) ≤ -Real.log (250000000000 / 302157333919) ∧
    -Real.log (250000000000 / 302157333919) ≤ (94743469 / 500000000) := by
  have h := checkLog_sound (w := (52157333919 / 552157333919)) (n := 12)
    (lo := (189486937 / 1000000000)) (hi := (94743469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302157333919 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302157333919 / 250000000000) = 1/(250000000000 / 302157333919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5286 : Bounds (189486937 / 1000000000) (94743469 / 500000000) (Real.log (302157333919 / 250000000000)) := by
  have h := reflection_log_5286_neg
  have he : Real.log (302157333919 / 250000000000) = -Real.log (250000000000 / 302157333919) := by
    rw [show ((302157333919 / 250000000000) : ℝ) = ((250000000000 / 302157333919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5287_neg : (189967233 / 1000000000) ≤ -Real.log (250000000000 / 302302493867) ∧
    -Real.log (250000000000 / 302302493867) ≤ (94983617 / 500000000) := by
  have h := checkLog_sound (w := (52302493867 / 552302493867)) (n := 12)
    (lo := (189967233 / 1000000000)) (hi := (94983617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302302493867 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302302493867 / 250000000000) = 1/(250000000000 / 302302493867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5287 : Bounds (189967233 / 1000000000) (94983617 / 500000000) (Real.log (302302493867 / 250000000000)) := by
  have h := reflection_log_5287_neg
  have he : Real.log (302302493867 / 250000000000) = -Real.log (250000000000 / 302302493867) := by
    rw [show ((302302493867 / 250000000000) : ℝ) = ((250000000000 / 302302493867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5288_neg : (95079709 / 250000000) ≤ -Real.log (500000000000 / 731375446373) ∧
    -Real.log (500000000000 / 731375446373) ≤ (380318837 / 1000000000) := by
  have h := checkLog_sound (w := (231375446373 / 1231375446373)) (n := 12)
    (lo := (95079709 / 250000000)) (hi := (380318837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731375446373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731375446373 / 500000000000) = 1/(500000000000 / 731375446373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5288 : Bounds (95079709 / 250000000) (380318837 / 1000000000) (Real.log (731375446373 / 500000000000)) := by
  have h := reflection_log_5288_neg
  have he : Real.log (731375446373 / 500000000000) = -Real.log (500000000000 / 731375446373) := by
    rw [show ((731375446373 / 500000000000) : ℝ) = ((500000000000 / 731375446373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5289_neg : (380526159 / 1000000000) ≤ -Real.log (500000000000 / 731527093597) ∧
    -Real.log (500000000000 / 731527093597) ≤ (4756577 / 12500000) := by
  have h := checkLog_sound (w := (231527093597 / 1231527093597)) (n := 12)
    (lo := (380526159 / 1000000000)) (hi := (4756577 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731527093597 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731527093597 / 500000000000) = 1/(500000000000 / 731527093597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5289 : Bounds (380526159 / 1000000000) (4756577 / 12500000) (Real.log (731527093597 / 500000000000)) := by
  have h := reflection_log_5289_neg
  have he : Real.log (731527093597 / 500000000000) = -Real.log (500000000000 / 731527093597) := by
    rw [show ((731527093597 / 500000000000) : ℝ) = ((500000000000 / 731527093597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5290_neg : (2693053 / 15625000) ≤ -Real.log (10000 / 11881) ∧
    -Real.log (10000 / 11881) ≤ (172355393 / 1000000000) := by
  have h := checkLog_sound (w := (1881 / 21881)) (n := 12)
    (lo := (2693053 / 15625000)) (hi := (172355393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11881 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11881 / 10000) = 1/(10000 / 11881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5290 : Bounds (2693053 / 15625000) (172355393 / 1000000000) (Real.log (11881 / 10000)) := by
  have h := reflection_log_5290_neg
  have he : Real.log (11881 / 10000) = -Real.log (10000 / 11881) := by
    rw [show ((11881 / 10000) : ℝ) = ((10000 / 11881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5291_neg : (208378099 / 1000000000) ≤ -Real.log (8119 / 10000) ∧
    -Real.log (8119 / 10000) ≤ (2083781 / 10000000) := by
  have h := checkLog_sound (w := (1881 / 18119)) (n := 12)
    (lo := (208378099 / 1000000000)) (hi := (2083781 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8119) = 1/(8119 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5291 : Bounds (-2083781 / 10000000) (-208378099 / 1000000000) (Real.log (8119 / 10000)) := by
  have h := reflection_log_5291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5292_neg : (94041 / 500000000) ≤ -Real.log (10000000 / 10001881) ∧
    -Real.log (10000000 / 10001881) ≤ (188083 / 1000000000) := by
  have h := checkLog_sound (w := (1881 / 20001881)) (n := 12)
    (lo := (94041 / 500000000)) (hi := (188083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001881 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001881 / 10000000) = 1/(10000000 / 10001881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5292 : Bounds (94041 / 500000000) (188083 / 1000000000) (Real.log (10001881 / 10000000)) := by
  have h := reflection_log_5292_neg
  have he : Real.log (10001881 / 10000000) = -Real.log (10000000 / 10001881) := by
    rw [show ((10001881 / 10000000) : ℝ) = ((10000000 / 10001881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5293_neg : (188117 / 1000000000) ≤ -Real.log (9998119 / 10000000) ∧
    -Real.log (9998119 / 10000000) ≤ (94059 / 500000000) := by
  have h := checkLog_sound (w := (1881 / 19998119)) (n := 12)
    (lo := (188117 / 1000000000)) (hi := (94059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998119) = 1/(9998119 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5293 : Bounds (-94059 / 500000000) (-188117 / 1000000000) (Real.log (9998119 / 10000000)) := by
  have h := reflection_log_5293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5294_neg : (90308601 / 1000000000) ≤ -Real.log (62500 / 68407) ∧
    -Real.log (62500 / 68407) ≤ (45154301 / 500000000) := by
  have h := checkLog_sound (w := (5907 / 130907)) (n := 12)
    (lo := (90308601 / 1000000000)) (hi := (45154301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68407 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68407 / 62500) = 1/(62500 / 68407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5294 : Bounds (90308601 / 1000000000) (45154301 / 500000000) (Real.log (68407 / 62500)) := by
  have h := reflection_log_5294_neg
  have he : Real.log (68407 / 62500) = -Real.log (62500 / 68407) := by
    rw [show ((68407 / 62500) : ℝ) = ((62500 / 68407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5295_neg : (49640627 / 500000000) ≤ -Real.log (56593 / 62500) ∧
    -Real.log (56593 / 62500) ≤ (19856251 / 200000000) := by
  have h := checkLog_sound (w := (5907 / 119093)) (n := 12)
    (lo := (49640627 / 500000000)) (hi := (19856251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56593) = 1/(56593 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5295 : Bounds (-19856251 / 200000000) (-49640627 / 500000000) (Real.log (56593 / 62500)) := by
  have h := reflection_log_5295_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5296_neg : (45263013 / 500000000) ≤ -Real.log (4000 / 4379) ∧
    -Real.log (4000 / 4379) ≤ (90526027 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 8379)) (n := 12)
    (lo := (45263013 / 500000000)) (hi := (90526027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4379 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4379 / 4000) = 1/(4000 / 4379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5296 : Bounds (45263013 / 500000000) (90526027 / 1000000000) (Real.log (4379 / 4000)) := by
  have h := reflection_log_5296_neg
  have he : Real.log (4379 / 4000) = -Real.log (4000 / 4379) := by
    rw [show ((4379 / 4000) : ℝ) = ((4000 / 4379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5297_neg : (9954413 / 100000000) ≤ -Real.log (3621 / 4000) ∧
    -Real.log (3621 / 4000) ≤ (99544131 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 7621)) (n := 12)
    (lo := (9954413 / 100000000)) (hi := (99544131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3621) = 1/(3621 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5297 : Bounds (-99544131 / 1000000000) (-9954413 / 100000000) (Real.log (3621 / 4000)) := by
  have h := reflection_log_5297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5298_neg : (9018103 / 1000000000) ≤ -Real.log (15856359 / 16000000) ∧
    -Real.log (15856359 / 16000000) ≤ (1127263 / 125000000) := by
  have h := checkLog_sound (w := (143641 / 31856359)) (n := 12)
    (lo := (9018103 / 1000000000)) (hi := (1127263 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15856359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15856359) = 1/(15856359 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5298 : Bounds (-1127263 / 125000000) (-9018103 / 1000000000) (Real.log (15856359 / 16000000)) := by
  have h := reflection_log_5298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5299_neg : (2243163 / 250000000) ≤ -Real.log (3871357351 / 3906250000) ∧
    -Real.log (3871357351 / 3906250000) ≤ (8972653 / 1000000000) := by
  have h := checkLog_sound (w := (34892649 / 7777607351)) (n := 12)
    (lo := (2243163 / 250000000)) (hi := (8972653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3871357351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3871357351) = 1/(3871357351 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5299 : Bounds (-8972653 / 1000000000) (-2243163 / 250000000) (Real.log (3871357351 / 3906250000)) := by
  have h := reflection_log_5299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5300_neg : (37917971 / 200000000) ≤ -Real.log (125000000000 / 151094216599) ∧
    -Real.log (125000000000 / 151094216599) ≤ (5924683 / 31250000) := by
  have h := checkLog_sound (w := (26094216599 / 276094216599)) (n := 12)
    (lo := (37917971 / 200000000)) (hi := (5924683 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151094216599 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151094216599 / 125000000000) = 1/(125000000000 / 151094216599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5300 : Bounds (37917971 / 200000000) (5924683 / 31250000) (Real.log (151094216599 / 125000000000)) := by
  have h := reflection_log_5300_neg
  have he : Real.log (151094216599 / 125000000000) = -Real.log (125000000000 / 151094216599) := by
    rw [show ((151094216599 / 125000000000) : ℝ) = ((125000000000 / 151094216599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5301_neg : (190070157 / 1000000000) ≤ -Real.log (500000000000 / 604667219001) ∧
    -Real.log (500000000000 / 604667219001) ≤ (95035079 / 500000000) := by
  have h := checkLog_sound (w := (104667219001 / 1104667219001)) (n := 12)
    (lo := (190070157 / 1000000000)) (hi := (95035079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604667219001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604667219001 / 500000000000) = 1/(500000000000 / 604667219001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5301 : Bounds (190070157 / 1000000000) (95035079 / 500000000) (Real.log (604667219001 / 500000000000)) := by
  have h := reflection_log_5301_neg
  have he : Real.log (604667219001 / 500000000000) = -Real.log (500000000000 / 604667219001) := by
    rw [show ((604667219001 / 500000000000) : ℝ) = ((500000000000 / 604667219001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5302_neg : (380526159 / 1000000000) ≤ -Real.log (125000000000 / 182881773399) ∧
    -Real.log (125000000000 / 182881773399) ≤ (4756577 / 12500000) := by
  have h := checkLog_sound (w := (57881773399 / 307881773399)) (n := 12)
    (lo := (380526159 / 1000000000)) (hi := (4756577 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182881773399 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182881773399 / 125000000000) = 1/(125000000000 / 182881773399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5302 : Bounds (380526159 / 1000000000) (4756577 / 12500000) (Real.log (182881773399 / 125000000000)) := by
  have h := reflection_log_5302_neg
  have he : Real.log (182881773399 / 125000000000) = -Real.log (125000000000 / 182881773399) := by
    rw [show ((182881773399 / 125000000000) : ℝ) = ((125000000000 / 182881773399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5303_neg : (380733491 / 1000000000) ≤ -Real.log (20000000000 / 29267151127) ∧
    -Real.log (20000000000 / 29267151127) ≤ (95183373 / 250000000) := by
  have h := checkLog_sound (w := (9267151127 / 49267151127)) (n := 12)
    (lo := (380733491 / 1000000000)) (hi := (95183373 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29267151127 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29267151127 / 20000000000) = 1/(20000000000 / 29267151127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5303 : Bounds (380733491 / 1000000000) (95183373 / 250000000) (Real.log (29267151127 / 20000000000)) := by
  have h := reflection_log_5303_neg
  have he : Real.log (29267151127 / 20000000000) = -Real.log (20000000000 / 29267151127) := by
    rw [show ((29267151127 / 20000000000) : ℝ) = ((20000000000 / 29267151127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5304_neg : (43109889 / 250000000) ≤ -Real.log (5000 / 5941) ∧
    -Real.log (5000 / 5941) ≤ (172439557 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 10941)) (n := 12)
    (lo := (43109889 / 250000000)) (hi := (172439557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5941 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5941 / 5000) = 1/(5000 / 5941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5304 : Bounds (43109889 / 250000000) (172439557 / 1000000000) (Real.log (5941 / 5000)) := by
  have h := reflection_log_5304_neg
  have he : Real.log (5941 / 5000) = -Real.log (5000 / 5941) := by
    rw [show ((5941 / 5000) : ℝ) = ((5000 / 5941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5305_neg : (104250637 / 500000000) ≤ -Real.log (4059 / 5000) ∧
    -Real.log (4059 / 5000) ≤ (8340051 / 40000000) := by
  have h := checkLog_sound (w := (941 / 9059)) (n := 12)
    (lo := (104250637 / 500000000)) (hi := (8340051 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4059) = 1/(4059 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5305 : Bounds (-8340051 / 40000000) (-104250637 / 500000000) (Real.log (4059 / 5000)) := by
  have h := reflection_log_5305_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5306_neg : (94091 / 500000000) ≤ -Real.log (5000000 / 5000941) ∧
    -Real.log (5000000 / 5000941) ≤ (188183 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 10000941)) (n := 12)
    (lo := (94091 / 500000000)) (hi := (188183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000941 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000941 / 5000000) = 1/(5000000 / 5000941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5306 : Bounds (94091 / 500000000) (188183 / 1000000000) (Real.log (5000941 / 5000000)) := by
  have h := reflection_log_5306_neg
  have he : Real.log (5000941 / 5000000) = -Real.log (5000000 / 5000941) := by
    rw [show ((5000941 / 5000000) : ℝ) = ((5000000 / 5000941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5307_neg : (188217 / 1000000000) ≤ -Real.log (4999059 / 5000000) ∧
    -Real.log (4999059 / 5000000) ≤ (94109 / 500000000) := by
  have h := checkLog_sound (w := (941 / 9999059)) (n := 12)
    (lo := (188217 / 1000000000)) (hi := (94109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999059) = 1/(4999059 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5307 : Bounds (-94109 / 500000000) (-188217 / 1000000000) (Real.log (4999059 / 5000000)) := by
  have h := reflection_log_5307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5308_neg : (90354283 / 1000000000) ≤ -Real.log (500000 / 547281) ∧
    -Real.log (500000 / 547281) ≤ (22588571 / 250000000) := by
  have h := checkLog_sound (w := (47281 / 1047281)) (n := 12)
    (lo := (90354283 / 1000000000)) (hi := (22588571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547281 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547281 / 500000) = 1/(500000 / 547281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5308 : Bounds (90354283 / 1000000000) (22588571 / 250000000) (Real.log (547281 / 500000)) := by
  have h := reflection_log_5308_neg
  have he : Real.log (547281 / 500000) = -Real.log (500000 / 547281) := by
    rw [show ((547281 / 500000) : ℝ) = ((500000 / 547281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5309_neg : (49668237 / 500000000) ≤ -Real.log (452719 / 500000) ∧
    -Real.log (452719 / 500000) ≤ (3973459 / 40000000) := by
  have h := checkLog_sound (w := (47281 / 952719)) (n := 12)
    (lo := (49668237 / 500000000)) (hi := (3973459 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452719) = 1/(452719 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5309 : Bounds (-3973459 / 40000000) (-49668237 / 500000000) (Real.log (452719 / 500000)) := by
  have h := reflection_log_5309_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5310_neg : (90572611 / 1000000000) ≤ -Real.log (1000000 / 1094801) ∧
    -Real.log (1000000 / 1094801) ≤ (22643153 / 250000000) := by
  have h := checkLog_sound (w := (94801 / 2094801)) (n := 12)
    (lo := (90572611 / 1000000000)) (hi := (22643153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094801 / 1000000) = 1/(1000000 / 1094801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5310 : Bounds (90572611 / 1000000000) (22643153 / 250000000) (Real.log (1094801 / 1000000)) := by
  have h := reflection_log_5310_neg
  have he : Real.log (1094801 / 1000000) = -Real.log (1000000 / 1094801) := by
    rw [show ((1094801 / 1000000) : ℝ) = ((1000000 / 1094801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5311_neg : (99600469 / 1000000000) ≤ -Real.log (905199 / 1000000) ∧
    -Real.log (905199 / 1000000) ≤ (9960047 / 100000000) := by
  have h := checkLog_sound (w := (94801 / 1905199)) (n := 12)
    (lo := (99600469 / 1000000000)) (hi := (9960047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905199) = 1/(905199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5311 : Bounds (-9960047 / 100000000) (-99600469 / 1000000000) (Real.log (905199 / 1000000)) := by
  have h := reflection_log_5311_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


