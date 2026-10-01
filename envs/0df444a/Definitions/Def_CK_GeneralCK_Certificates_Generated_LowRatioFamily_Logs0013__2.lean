-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0013__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0013__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:15:44.505931+00:00
-- url     : https://prove2.me/theorems/473e415b-50d0-44e6-b40f-d4d84eadce02
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0013 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0014)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0013 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0014)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0013 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0014)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0013 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0014) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0013 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0014).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0013 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_832_neg : (40889273 / 500000000) ≤ -Real.log (230369 / 250000) ∧
    -Real.log (230369 / 250000) ≤ (81778547 / 1000000000) := by
  have h := checkLog_sound (w := (19631 / 480369)) (n := 12)
    (lo := (40889273 / 500000000)) (hi := (81778547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230369) = 1/(230369 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_832 : Bounds (-81778547 / 1000000000) (-40889273 / 500000000) (Real.log (230369 / 250000)) := by
  have h := reflection_log_832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_833_neg : (3092553 / 500000000) ≤ -Real.log (62114623839 / 62500000000) ∧
    -Real.log (62114623839 / 62500000000) ≤ (6185107 / 1000000000) := by
  have h := checkLog_sound (w := (385376161 / 124614623839)) (n := 12)
    (lo := (3092553 / 500000000)) (hi := (6185107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62114623839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62114623839) = 1/(62114623839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_833 : Bounds (-6185107 / 1000000000) (-3092553 / 500000000) (Real.log (62114623839 / 62500000000)) := by
  have h := reflection_log_833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_834_neg : (6152439 / 1000000000) ≤ -Real.log (993866447511 / 1000000000000) ∧
    -Real.log (993866447511 / 1000000000000) ≤ (153811 / 25000000) := by
  have h := checkLog_sound (w := (6133552489 / 1993866447511)) (n := 12)
    (lo := (6152439 / 1000000000)) (hi := (153811 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993866447511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993866447511) = 1/(993866447511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_834 : Bounds (-153811 / 25000000) (-6152439 / 1000000000) (Real.log (993866447511 / 1000000000000)) := by
  have h := reflection_log_834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_835_neg : (4904857 / 31250000) ≤ -Real.log (500000000000 / 584971731061) ∧
    -Real.log (500000000000 / 584971731061) ≤ (6278217 / 40000000) := by
  have h := checkLog_sound (w := (84971731061 / 1084971731061)) (n := 12)
    (lo := (4904857 / 31250000)) (hi := (6278217 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584971731061 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584971731061 / 500000000000) = 1/(500000000000 / 584971731061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_835 : Bounds (4904857 / 31250000) (6278217 / 40000000) (Real.log (584971731061 / 500000000000)) := by
  have h := reflection_log_835_neg
  have he : Real.log (584971731061 / 500000000000) = -Real.log (500000000000 / 584971731061) := by
    rw [show ((584971731061 / 500000000000) : ℝ) = ((500000000000 / 584971731061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_836_neg : (78685993 / 500000000) ≤ -Real.log (250000000000 / 292607729339) ∧
    -Real.log (250000000000 / 292607729339) ≤ (157371987 / 1000000000) := by
  have h := checkLog_sound (w := (42607729339 / 542607729339)) (n := 12)
    (lo := (78685993 / 500000000)) (hi := (157371987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292607729339 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292607729339 / 250000000000) = 1/(250000000000 / 292607729339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_836 : Bounds (78685993 / 500000000) (157371987 / 1000000000) (Real.log (292607729339 / 250000000000)) := by
  have h := reflection_log_836_neg
  have he : Real.log (292607729339 / 250000000000) = -Real.log (250000000000 / 292607729339) := by
    rw [show ((292607729339 / 250000000000) : ℝ) = ((250000000000 / 292607729339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_837_neg : (157386773 / 500000000) ≤ -Real.log (500000000000 / 684974523047) ∧
    -Real.log (500000000000 / 684974523047) ≤ (314773547 / 1000000000) := by
  have h := checkLog_sound (w := (184974523047 / 1184974523047)) (n := 12)
    (lo := (157386773 / 500000000)) (hi := (314773547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684974523047 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684974523047 / 500000000000) = 1/(500000000000 / 684974523047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_837 : Bounds (157386773 / 500000000) (314773547 / 1000000000) (Real.log (684974523047 / 500000000000)) := by
  have h := reflection_log_837_neg
  have he : Real.log (684974523047 / 500000000000) = -Real.log (500000000000 / 684974523047) := by
    rw [show ((684974523047 / 500000000000) : ℝ) = ((500000000000 / 684974523047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_838_neg : (19686159 / 62500000) ≤ -Real.log (500000000000 / 685114956151) ∧
    -Real.log (500000000000 / 685114956151) ≤ (62995709 / 200000000) := by
  have h := checkLog_sound (w := (185114956151 / 1185114956151)) (n := 12)
    (lo := (19686159 / 62500000)) (hi := (62995709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685114956151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685114956151 / 500000000000) = 1/(500000000000 / 685114956151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_838 : Bounds (19686159 / 62500000) (62995709 / 200000000) (Real.log (685114956151 / 500000000000)) := by
  have h := reflection_log_838_neg
  have he : Real.log (685114956151 / 500000000000) = -Real.log (500000000000 / 685114956151) := by
    rw [show ((685114956151 / 500000000000) : ℝ) = ((500000000000 / 685114956151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_839_neg : (36306313 / 250000000) ≤ -Real.log (10000 / 11563) ∧
    -Real.log (10000 / 11563) ≤ (145225253 / 1000000000) := by
  have h := checkLog_sound (w := (1563 / 21563)) (n := 12)
    (lo := (36306313 / 250000000)) (hi := (145225253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11563 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11563 / 10000) = 1/(10000 / 11563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_839 : Bounds (36306313 / 250000000) (145225253 / 1000000000) (Real.log (11563 / 10000)) := by
  have h := reflection_log_839_neg
  have he : Real.log (11563 / 10000) = -Real.log (10000 / 11563) := by
    rw [show ((11563 / 10000) : ℝ) = ((10000 / 11563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_840_neg : (169958297 / 1000000000) ≤ -Real.log (8437 / 10000) ∧
    -Real.log (8437 / 10000) ≤ (84979149 / 500000000) := by
  have h := checkLog_sound (w := (1563 / 18437)) (n := 12)
    (lo := (169958297 / 1000000000)) (hi := (84979149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8437) = 1/(8437 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_840 : Bounds (-84979149 / 500000000) (-169958297 / 1000000000) (Real.log (8437 / 10000)) := by
  have h := reflection_log_840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_841_neg : (156287 / 1000000000) ≤ -Real.log (10000000 / 10001563) ∧
    -Real.log (10000000 / 10001563) ≤ (1221 / 7812500) := by
  have h := checkLog_sound (w := (1563 / 20001563)) (n := 12)
    (lo := (156287 / 1000000000)) (hi := (1221 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001563 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001563 / 10000000) = 1/(10000000 / 10001563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_841 : Bounds (156287 / 1000000000) (1221 / 7812500) (Real.log (10001563 / 10000000)) := by
  have h := reflection_log_841_neg
  have he : Real.log (10001563 / 10000000) = -Real.log (10000000 / 10001563) := by
    rw [show ((10001563 / 10000000) : ℝ) = ((10000000 / 10001563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_842_neg : (19539 / 125000000) ≤ -Real.log (9998437 / 10000000) ∧
    -Real.log (9998437 / 10000000) ≤ (156313 / 1000000000) := by
  have h := checkLog_sound (w := (1563 / 19998437)) (n := 12)
    (lo := (19539 / 125000000)) (hi := (156313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998437) = 1/(9998437 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_842 : Bounds (-156313 / 1000000000) (-19539 / 125000000) (Real.log (9998437 / 10000000)) := by
  have h := reflection_log_842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_843_neg : (75448787 / 1000000000) ≤ -Real.log (31250 / 33699) ∧
    -Real.log (31250 / 33699) ≤ (18862197 / 250000000) := by
  have h := checkLog_sound (w := (2449 / 64949)) (n := 12)
    (lo := (75448787 / 1000000000)) (hi := (18862197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33699 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33699 / 31250) = 1/(31250 / 33699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_843 : Bounds (75448787 / 1000000000) (18862197 / 250000000) (Real.log (33699 / 31250)) := by
  have h := reflection_log_843_neg
  have he : Real.log (33699 / 31250) = -Real.log (31250 / 33699) := by
    rw [show ((33699 / 31250) : ℝ) = ((31250 / 33699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_844_neg : (81609267 / 1000000000) ≤ -Real.log (28801 / 31250) ∧
    -Real.log (28801 / 31250) ≤ (20402317 / 250000000) := by
  have h := checkLog_sound (w := (2449 / 60051)) (n := 12)
    (lo := (81609267 / 1000000000)) (hi := (20402317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28801) = 1/(28801 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_844 : Bounds (-20402317 / 250000000) (-81609267 / 1000000000) (Real.log (28801 / 31250)) := by
  have h := reflection_log_844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_845_neg : (3025629 / 40000000) ≤ -Real.log (40000 / 43143) ∧
    -Real.log (40000 / 43143) ≤ (37820363 / 500000000) := by
  have h := checkLog_sound (w := (3143 / 83143)) (n := 12)
    (lo := (3025629 / 40000000)) (hi := (37820363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43143 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43143 / 40000) = 1/(40000 / 43143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_845 : Bounds (3025629 / 40000000) (37820363 / 500000000) (Real.log (43143 / 40000)) := by
  have h := reflection_log_845_neg
  have he : Real.log (43143 / 40000) = -Real.log (40000 / 43143) := by
    rw [show ((43143 / 40000) : ℝ) = ((40000 / 43143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_846_neg : (40916947 / 500000000) ≤ -Real.log (36857 / 40000) ∧
    -Real.log (36857 / 40000) ≤ (16366779 / 200000000) := by
  have h := checkLog_sound (w := (3143 / 76857)) (n := 12)
    (lo := (40916947 / 500000000)) (hi := (16366779 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36857) = 1/(36857 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_846 : Bounds (-16366779 / 200000000) (-40916947 / 500000000) (Real.log (36857 / 40000)) := by
  have h := reflection_log_846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_847_neg : (387073 / 62500000) ≤ -Real.log (1590121551 / 1600000000) ∧
    -Real.log (1590121551 / 1600000000) ≤ (6193169 / 1000000000) := by
  have h := checkLog_sound (w := (9878449 / 3190121551)) (n := 12)
    (lo := (387073 / 62500000)) (hi := (6193169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1590121551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1590121551) = 1/(1590121551 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_847 : Bounds (-6193169 / 1000000000) (-387073 / 62500000) (Real.log (1590121551 / 1600000000)) := by
  have h := reflection_log_847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_848_neg : (38503 / 6250000) ≤ -Real.log (970564899 / 976562500) ∧
    -Real.log (970564899 / 976562500) ≤ (6160481 / 1000000000) := by
  have h := checkLog_sound (w := (5997601 / 1947127399)) (n := 12)
    (lo := (38503 / 6250000)) (hi := (6160481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 970564899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 970564899) = 1/(970564899 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_848 : Bounds (-6160481 / 1000000000) (-38503 / 6250000) (Real.log (970564899 / 976562500)) := by
  have h := reflection_log_848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_849_neg : (78529027 / 500000000) ≤ -Real.log (50000000000 / 58503176973) ∧
    -Real.log (50000000000 / 58503176973) ≤ (31411611 / 200000000) := by
  have h := checkLog_sound (w := (8503176973 / 108503176973)) (n := 12)
    (lo := (78529027 / 500000000)) (hi := (31411611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58503176973 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58503176973 / 50000000000) = 1/(50000000000 / 58503176973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_849 : Bounds (78529027 / 500000000) (31411611 / 200000000) (Real.log (58503176973 / 50000000000)) := by
  have h := reflection_log_849_neg
  have he : Real.log (58503176973 / 50000000000) = -Real.log (50000000000 / 58503176973) := by
    rw [show ((58503176973 / 50000000000) : ℝ) = ((50000000000 / 58503176973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_850_neg : (157474619 / 1000000000) ≤ -Real.log (125000000000 / 146318881081) ∧
    -Real.log (125000000000 / 146318881081) ≤ (7873731 / 50000000) := by
  have h := checkLog_sound (w := (21318881081 / 271318881081)) (n := 12)
    (lo := (157474619 / 1000000000)) (hi := (7873731 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146318881081 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146318881081 / 125000000000) = 1/(125000000000 / 146318881081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_850 : Bounds (157474619 / 1000000000) (7873731 / 50000000) (Real.log (146318881081 / 125000000000)) := by
  have h := reflection_log_850_neg
  have he : Real.log (146318881081 / 125000000000) = -Real.log (125000000000 / 146318881081) := by
    rw [show ((146318881081 / 125000000000) : ℝ) = ((125000000000 / 146318881081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_851_neg : (19686159 / 62500000) ≤ -Real.log (10000000000 / 13702299123) ∧
    -Real.log (10000000000 / 13702299123) ≤ (62995709 / 200000000) := by
  have h := checkLog_sound (w := (3702299123 / 23702299123)) (n := 12)
    (lo := (19686159 / 62500000)) (hi := (62995709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13702299123 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13702299123 / 10000000000) = 1/(10000000000 / 13702299123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_851 : Bounds (19686159 / 62500000) (62995709 / 200000000) (Real.log (13702299123 / 10000000000)) := by
  have h := reflection_log_851_neg
  have he : Real.log (13702299123 / 10000000000) = -Real.log (10000000000 / 13702299123) := by
    rw [show ((13702299123 / 10000000000) : ℝ) = ((10000000000 / 13702299123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_852_neg : (315183549 / 1000000000) ≤ -Real.log (31250000000 / 42828463909) ∧
    -Real.log (31250000000 / 42828463909) ≤ (6303671 / 20000000) := by
  have h := checkLog_sound (w := (11578463909 / 74078463909)) (n := 12)
    (lo := (315183549 / 1000000000)) (hi := (6303671 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42828463909 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42828463909 / 31250000000) = 1/(31250000000 / 42828463909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_852 : Bounds (315183549 / 1000000000) (6303671 / 20000000) (Real.log (42828463909 / 31250000000)) := by
  have h := reflection_log_852_neg
  have he : Real.log (42828463909 / 31250000000) = -Real.log (31250000000 / 42828463909) := by
    rw [show ((42828463909 / 31250000000) : ℝ) = ((31250000000 / 42828463909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_853_neg : (145311731 / 1000000000) ≤ -Real.log (2500 / 2891) ∧
    -Real.log (2500 / 2891) ≤ (36327933 / 250000000) := by
  have h := checkLog_sound (w := (391 / 5391)) (n := 12)
    (lo := (145311731 / 1000000000)) (hi := (36327933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2891 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2891 / 2500) = 1/(2500 / 2891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_853 : Bounds (145311731 / 1000000000) (36327933 / 250000000) (Real.log (2891 / 2500)) := by
  have h := reflection_log_853_neg
  have he : Real.log (2891 / 2500) = -Real.log (2500 / 2891) := by
    rw [show ((2891 / 2500) : ℝ) = ((2500 / 2891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_854_neg : (17007683 / 100000000) ≤ -Real.log (2109 / 2500) ∧
    -Real.log (2109 / 2500) ≤ (170076831 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 4609)) (n := 12)
    (lo := (17007683 / 100000000)) (hi := (170076831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2109) = 1/(2109 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_854 : Bounds (-170076831 / 1000000000) (-17007683 / 100000000) (Real.log (2109 / 2500)) := by
  have h := reflection_log_854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_855_neg : (156387 / 1000000000) ≤ -Real.log (2500000 / 2500391) ∧
    -Real.log (2500000 / 2500391) ≤ (39097 / 250000000) := by
  have h := checkLog_sound (w := (391 / 5000391)) (n := 12)
    (lo := (156387 / 1000000000)) (hi := (39097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500391 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500391 / 2500000) = 1/(2500000 / 2500391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_855 : Bounds (156387 / 1000000000) (39097 / 250000000) (Real.log (2500391 / 2500000)) := by
  have h := reflection_log_855_neg
  have he : Real.log (2500391 / 2500000) = -Real.log (2500000 / 2500391) := by
    rw [show ((2500391 / 2500000) : ℝ) = ((2500000 / 2500391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_856_neg : (39103 / 250000000) ≤ -Real.log (2499609 / 2500000) ∧
    -Real.log (2499609 / 2500000) ≤ (156413 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 4999609)) (n := 12)
    (lo := (39103 / 250000000)) (hi := (156413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499609) = 1/(2499609 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_856 : Bounds (-156413 / 1000000000) (-39103 / 250000000) (Real.log (2499609 / 2500000)) := by
  have h := reflection_log_856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_857_neg : (4718447 / 62500000) ≤ -Real.log (500000 / 539209) ∧
    -Real.log (500000 / 539209) ≤ (75495153 / 1000000000) := by
  have h := checkLog_sound (w := (39209 / 1039209)) (n := 12)
    (lo := (4718447 / 62500000)) (hi := (75495153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539209 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539209 / 500000) = 1/(500000 / 539209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_857 : Bounds (4718447 / 62500000) (75495153 / 1000000000) (Real.log (539209 / 500000)) := by
  have h := reflection_log_857_neg
  have he : Real.log (539209 / 500000) = -Real.log (500000 / 539209) := by
    rw [show ((539209 / 500000) : ℝ) = ((500000 / 539209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_858_neg : (510397 / 6250000) ≤ -Real.log (460791 / 500000) ∧
    -Real.log (460791 / 500000) ≤ (81663521 / 1000000000) := by
  have h := checkLog_sound (w := (39209 / 960791)) (n := 12)
    (lo := (510397 / 6250000)) (hi := (81663521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460791) = 1/(460791 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_858 : Bounds (-81663521 / 1000000000) (-510397 / 6250000) (Real.log (460791 / 500000)) := by
  have h := reflection_log_858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_859_neg : (9461001 / 125000000) ≤ -Real.log (500000 / 539313) ∧
    -Real.log (500000 / 539313) ≤ (75688009 / 1000000000) := by
  have h := checkLog_sound (w := (39313 / 1039313)) (n := 12)
    (lo := (9461001 / 125000000)) (hi := (75688009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539313 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539313 / 500000) = 1/(500000 / 539313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_859 : Bounds (9461001 / 125000000) (75688009 / 1000000000) (Real.log (539313 / 500000)) := by
  have h := reflection_log_859_neg
  have he : Real.log (539313 / 500000) = -Real.log (500000 / 539313) := by
    rw [show ((539313 / 500000) : ℝ) = ((500000 / 539313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_860_neg : (20472311 / 250000000) ≤ -Real.log (460687 / 500000) ∧
    -Real.log (460687 / 500000) ≤ (16377849 / 200000000) := by
  have h := checkLog_sound (w := (39313 / 960687)) (n := 12)
    (lo := (20472311 / 250000000)) (hi := (16377849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460687) = 1/(460687 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_860 : Bounds (-16377849 / 200000000) (-20472311 / 250000000) (Real.log (460687 / 500000)) := by
  have h := reflection_log_860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_861_neg : (1240247 / 200000000) ≤ -Real.log (248454488031 / 250000000000) ∧
    -Real.log (248454488031 / 250000000000) ≤ (1550309 / 250000000) := by
  have h := checkLog_sound (w := (1545511969 / 498454488031)) (n := 12)
    (lo := (1240247 / 200000000)) (hi := (1550309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248454488031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248454488031) = 1/(248454488031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_861 : Bounds (-1550309 / 250000000) (-1240247 / 200000000) (Real.log (248454488031 / 250000000000)) := by
  have h := reflection_log_861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_862_neg : (385523 / 62500000) ≤ -Real.log (248462654319 / 250000000000) ∧
    -Real.log (248462654319 / 250000000000) ≤ (6168369 / 1000000000) := by
  have h := checkLog_sound (w := (1537345681 / 498462654319)) (n := 12)
    (lo := (385523 / 62500000)) (hi := (6168369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248462654319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248462654319) = 1/(248462654319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_862 : Bounds (-6168369 / 1000000000) (-385523 / 62500000) (Real.log (248462654319 / 250000000000)) := by
  have h := reflection_log_862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_863_neg : (9822417 / 62500000) ≤ -Real.log (25000000000 / 29254531881) ∧
    -Real.log (25000000000 / 29254531881) ≤ (157158673 / 1000000000) := by
  have h := checkLog_sound (w := (4254531881 / 54254531881)) (n := 12)
    (lo := (9822417 / 62500000)) (hi := (157158673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29254531881 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29254531881 / 25000000000) = 1/(25000000000 / 29254531881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_863 : Bounds (9822417 / 62500000) (157158673 / 1000000000) (Real.log (29254531881 / 25000000000)) := by
  have h := reflection_log_863_neg
  have he : Real.log (29254531881 / 25000000000) = -Real.log (25000000000 / 29254531881) := by
    rw [show ((29254531881 / 25000000000) : ℝ) = ((25000000000 / 29254531881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_864_neg : (157577253 / 1000000000) ≤ -Real.log (25000000000 / 29266779831) ∧
    -Real.log (25000000000 / 29266779831) ≤ (78788627 / 500000000) := by
  have h := checkLog_sound (w := (4266779831 / 54266779831)) (n := 12)
    (lo := (157577253 / 1000000000)) (hi := (78788627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29266779831 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29266779831 / 25000000000) = 1/(25000000000 / 29266779831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_864 : Bounds (157577253 / 1000000000) (78788627 / 500000000) (Real.log (29266779831 / 25000000000)) := by
  have h := reflection_log_864_neg
  have he : Real.log (29266779831 / 25000000000) = -Real.log (25000000000 / 29266779831) := by
    rw [show ((29266779831 / 25000000000) : ℝ) = ((25000000000 / 29266779831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_865_neg : (315183549 / 1000000000) ≤ -Real.log (500000000000 / 685255422543) ∧
    -Real.log (500000000000 / 685255422543) ≤ (6303671 / 20000000) := by
  have h := checkLog_sound (w := (185255422543 / 1185255422543)) (n := 12)
    (lo := (315183549 / 1000000000)) (hi := (6303671 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685255422543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685255422543 / 500000000000) = 1/(500000000000 / 685255422543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_865 : Bounds (315183549 / 1000000000) (6303671 / 20000000) (Real.log (685255422543 / 500000000000)) := by
  have h := reflection_log_865_neg
  have he : Real.log (685255422543 / 500000000000) = -Real.log (500000000000 / 685255422543) := by
    rw [show ((685255422543 / 500000000000) : ℝ) = ((500000000000 / 685255422543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_866_neg : (315388561 / 1000000000) ≤ -Real.log (500000000000 / 685395922239) ∧
    -Real.log (500000000000 / 685395922239) ≤ (157694281 / 500000000) := by
  have h := checkLog_sound (w := (185395922239 / 1185395922239)) (n := 12)
    (lo := (315388561 / 1000000000)) (hi := (157694281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685395922239 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685395922239 / 500000000000) = 1/(500000000000 / 685395922239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_866 : Bounds (315388561 / 1000000000) (157694281 / 500000000) (Real.log (685395922239 / 500000000000)) := by
  have h := reflection_log_866_neg
  have he : Real.log (685395922239 / 500000000000) = -Real.log (500000000000 / 685395922239) := by
    rw [show ((685395922239 / 500000000000) : ℝ) = ((500000000000 / 685395922239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_867_neg : (72699101 / 500000000) ≤ -Real.log (2000 / 2313) ∧
    -Real.log (2000 / 2313) ≤ (145398203 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 4313)) (n := 12)
    (lo := (72699101 / 500000000)) (hi := (145398203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2313 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2313 / 2000) = 1/(2000 / 2313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_867 : Bounds (72699101 / 500000000) (145398203 / 1000000000) (Real.log (2313 / 2000)) := by
  have h := reflection_log_867_neg
  have he : Real.log (2313 / 2000) = -Real.log (2000 / 2313) := by
    rw [show ((2313 / 2000) : ℝ) = ((2000 / 2313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_868_neg : (10637211 / 62500000) ≤ -Real.log (1687 / 2000) ∧
    -Real.log (1687 / 2000) ≤ (170195377 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 3687)) (n := 12)
    (lo := (10637211 / 62500000)) (hi := (170195377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1687) = 1/(1687 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_868 : Bounds (-170195377 / 1000000000) (-10637211 / 62500000) (Real.log (1687 / 2000)) := by
  have h := reflection_log_868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_869_neg : (156487 / 1000000000) ≤ -Real.log (2000000 / 2000313) ∧
    -Real.log (2000000 / 2000313) ≤ (19561 / 125000000) := by
  have h := checkLog_sound (w := (313 / 4000313)) (n := 12)
    (lo := (156487 / 1000000000)) (hi := (19561 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000313 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000313 / 2000000) = 1/(2000000 / 2000313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_869 : Bounds (156487 / 1000000000) (19561 / 125000000) (Real.log (2000313 / 2000000)) := by
  have h := reflection_log_869_neg
  have he : Real.log (2000313 / 2000000) = -Real.log (2000000 / 2000313) := by
    rw [show ((2000313 / 2000000) : ℝ) = ((2000000 / 2000313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_870_neg : (4891 / 31250000) ≤ -Real.log (1999687 / 2000000) ∧
    -Real.log (1999687 / 2000000) ≤ (156513 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 3999687)) (n := 12)
    (lo := (4891 / 31250000)) (hi := (156513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999687) = 1/(1999687 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_870 : Bounds (-156513 / 1000000000) (-4891 / 31250000) (Real.log (1999687 / 2000000)) := by
  have h := reflection_log_870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_871_neg : (37771221 / 500000000) ≤ -Real.log (1000000 / 1078469) ∧
    -Real.log (1000000 / 1078469) ≤ (75542443 / 1000000000) := by
  have h := checkLog_sound (w := (78469 / 2078469)) (n := 12)
    (lo := (37771221 / 500000000)) (hi := (75542443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078469 / 1000000) = 1/(1000000 / 1078469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_871 : Bounds (37771221 / 500000000) (75542443 / 1000000000) (Real.log (1078469 / 1000000)) := by
  have h := reflection_log_871_neg
  have he : Real.log (1078469 / 1000000) = -Real.log (1000000 / 1078469) := by
    rw [show ((1078469 / 1000000) : ℝ) = ((1000000 / 1078469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_872_neg : (81718861 / 1000000000) ≤ -Real.log (921531 / 1000000) ∧
    -Real.log (921531 / 1000000) ≤ (40859431 / 500000000) := by
  have h := checkLog_sound (w := (78469 / 1921531)) (n := 12)
    (lo := (81718861 / 1000000000)) (hi := (40859431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921531) = 1/(921531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_872 : Bounds (-40859431 / 500000000) (-81718861 / 1000000000) (Real.log (921531 / 1000000)) := by
  have h := reflection_log_872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_873_neg : (7573529 / 100000000) ≤ -Real.log (1000000 / 1078677) ∧
    -Real.log (1000000 / 1078677) ≤ (75735291 / 1000000000) := by
  have h := checkLog_sound (w := (78677 / 2078677)) (n := 12)
    (lo := (7573529 / 100000000)) (hi := (75735291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078677 / 1000000) = 1/(1000000 / 1078677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_873 : Bounds (7573529 / 100000000) (75735291 / 1000000000) (Real.log (1078677 / 1000000)) := by
  have h := reflection_log_873_neg
  have he : Real.log (1078677 / 1000000) = -Real.log (1000000 / 1078677) := by
    rw [show ((1078677 / 1000000) : ℝ) = ((1000000 / 1078677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_874_neg : (40972299 / 500000000) ≤ -Real.log (921323 / 1000000) ∧
    -Real.log (921323 / 1000000) ≤ (81944599 / 1000000000) := by
  have h := checkLog_sound (w := (78677 / 1921323)) (n := 12)
    (lo := (40972299 / 500000000)) (hi := (81944599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921323) = 1/(921323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_874 : Bounds (-81944599 / 1000000000) (-40972299 / 500000000) (Real.log (921323 / 1000000)) := by
  have h := reflection_log_874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_875_neg : (1552327 / 250000000) ≤ -Real.log (993809929671 / 1000000000000) ∧
    -Real.log (993809929671 / 1000000000000) ≤ (6209309 / 1000000000) := by
  have h := checkLog_sound (w := (6190070329 / 1993809929671)) (n := 12)
    (lo := (1552327 / 250000000)) (hi := (6209309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993809929671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993809929671) = 1/(993809929671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_875 : Bounds (-6209309 / 1000000000) (-1552327 / 250000000) (Real.log (993809929671 / 1000000000000)) := by
  have h := reflection_log_875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_876_neg : (3088209 / 500000000) ≤ -Real.log (993842616039 / 1000000000000) ∧
    -Real.log (993842616039 / 1000000000000) ≤ (6176419 / 1000000000) := by
  have h := checkLog_sound (w := (6157383961 / 1993842616039)) (n := 12)
    (lo := (3088209 / 500000000)) (hi := (6176419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993842616039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993842616039) = 1/(993842616039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_876 : Bounds (-6176419 / 1000000000) (-3088209 / 500000000) (Real.log (993842616039 / 1000000000000)) := by
  have h := reflection_log_876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_877_neg : (19657663 / 125000000) ≤ -Real.log (10000000000 / 11703013789) ∧
    -Real.log (10000000000 / 11703013789) ≤ (31452261 / 200000000) := by
  have h := checkLog_sound (w := (1703013789 / 21703013789)) (n := 12)
    (lo := (19657663 / 125000000)) (hi := (31452261 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11703013789 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11703013789 / 10000000000) = 1/(10000000000 / 11703013789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_877 : Bounds (19657663 / 125000000) (31452261 / 200000000) (Real.log (11703013789 / 10000000000)) := by
  have h := reflection_log_877_neg
  have he : Real.log (11703013789 / 10000000000) = -Real.log (10000000000 / 11703013789) := by
    rw [show ((11703013789 / 10000000000) : ℝ) = ((10000000000 / 11703013789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_878_neg : (9854993 / 62500000) ≤ -Real.log (500000000000 / 585395675567) ∧
    -Real.log (500000000000 / 585395675567) ≤ (157679889 / 1000000000) := by
  have h := checkLog_sound (w := (85395675567 / 1085395675567)) (n := 12)
    (lo := (9854993 / 62500000)) (hi := (157679889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585395675567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585395675567 / 500000000000) = 1/(500000000000 / 585395675567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_878 : Bounds (9854993 / 62500000) (157679889 / 1000000000) (Real.log (585395675567 / 500000000000)) := by
  have h := reflection_log_878_neg
  have he : Real.log (585395675567 / 500000000000) = -Real.log (500000000000 / 585395675567) := by
    rw [show ((585395675567 / 500000000000) : ℝ) = ((500000000000 / 585395675567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_879_neg : (315388561 / 1000000000) ≤ -Real.log (250000000000 / 342697961119) ∧
    -Real.log (250000000000 / 342697961119) ≤ (157694281 / 500000000) := by
  have h := checkLog_sound (w := (92697961119 / 592697961119)) (n := 12)
    (lo := (315388561 / 1000000000)) (hi := (157694281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342697961119 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342697961119 / 250000000000) = 1/(250000000000 / 342697961119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_879 : Bounds (315388561 / 1000000000) (157694281 / 500000000) (Real.log (342697961119 / 250000000000)) := by
  have h := reflection_log_879_neg
  have he : Real.log (342697961119 / 250000000000) = -Real.log (250000000000 / 342697961119) := by
    rw [show ((342697961119 / 250000000000) : ℝ) = ((250000000000 / 342697961119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_880_neg : (315593579 / 1000000000) ≤ -Real.log (250000000000 / 342768227623) ∧
    -Real.log (250000000000 / 342768227623) ≤ (15779679 / 50000000) := by
  have h := checkLog_sound (w := (92768227623 / 592768227623)) (n := 12)
    (lo := (315593579 / 1000000000)) (hi := (15779679 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342768227623 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342768227623 / 250000000000) = 1/(250000000000 / 342768227623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_880 : Bounds (315593579 / 1000000000) (15779679 / 50000000) (Real.log (342768227623 / 250000000000)) := by
  have h := reflection_log_880_neg
  have he : Real.log (342768227623 / 250000000000) = -Real.log (250000000000 / 342768227623) := by
    rw [show ((342768227623 / 250000000000) : ℝ) = ((250000000000 / 342768227623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_881_neg : (72742333 / 500000000) ≤ -Real.log (5000 / 5783) ∧
    -Real.log (5000 / 5783) ≤ (145484667 / 1000000000) := by
  have h := checkLog_sound (w := (783 / 10783)) (n := 12)
    (lo := (72742333 / 500000000)) (hi := (145484667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5783 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5783 / 5000) = 1/(5000 / 5783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_881 : Bounds (72742333 / 500000000) (145484667 / 1000000000) (Real.log (5783 / 5000)) := by
  have h := reflection_log_881_neg
  have he : Real.log (5783 / 5000) = -Real.log (5000 / 5783) := by
    rw [show ((5783 / 5000) : ℝ) = ((5000 / 5783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_882_neg : (170313937 / 1000000000) ≤ -Real.log (4217 / 5000) ∧
    -Real.log (4217 / 5000) ≤ (85156969 / 500000000) := by
  have h := checkLog_sound (w := (783 / 9217)) (n := 12)
    (lo := (170313937 / 1000000000)) (hi := (85156969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4217) = 1/(4217 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_882 : Bounds (-85156969 / 500000000) (-170313937 / 1000000000) (Real.log (4217 / 5000)) := by
  have h := reflection_log_882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_883_neg : (156587 / 1000000000) ≤ -Real.log (5000000 / 5000783) ∧
    -Real.log (5000000 / 5000783) ≤ (39147 / 250000000) := by
  have h := checkLog_sound (w := (783 / 10000783)) (n := 12)
    (lo := (156587 / 1000000000)) (hi := (39147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000783 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000783 / 5000000) = 1/(5000000 / 5000783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_883 : Bounds (156587 / 1000000000) (39147 / 250000000) (Real.log (5000783 / 5000000)) := by
  have h := reflection_log_883_neg
  have he : Real.log (5000783 / 5000000) = -Real.log (5000000 / 5000783) := by
    rw [show ((5000783 / 5000000) : ℝ) = ((5000000 / 5000783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_884_neg : (39153 / 250000000) ≤ -Real.log (4999217 / 5000000) ∧
    -Real.log (4999217 / 5000000) ≤ (156613 / 1000000000) := by
  have h := checkLog_sound (w := (783 / 9999217)) (n := 12)
    (lo := (39153 / 250000000)) (hi := (156613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999217) = 1/(4999217 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_884 : Bounds (-156613 / 1000000000) (-39153 / 250000000) (Real.log (4999217 / 5000000)) := by
  have h := reflection_log_884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_885_neg : (7558973 / 100000000) ≤ -Real.log (25000 / 26963) ∧
    -Real.log (25000 / 26963) ≤ (75589731 / 1000000000) := by
  have h := checkLog_sound (w := (1963 / 51963)) (n := 12)
    (lo := (7558973 / 100000000)) (hi := (75589731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26963 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26963 / 25000) = 1/(25000 / 26963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_885 : Bounds (7558973 / 100000000) (75589731 / 1000000000) (Real.log (26963 / 25000)) := by
  have h := reflection_log_885_neg
  have he : Real.log (26963 / 25000) = -Real.log (25000 / 26963) := by
    rw [show ((26963 / 25000) : ℝ) = ((25000 / 26963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_886_neg : (16354841 / 200000000) ≤ -Real.log (23037 / 25000) ∧
    -Real.log (23037 / 25000) ≤ (40887103 / 500000000) := by
  have h := checkLog_sound (w := (1963 / 48037)) (n := 12)
    (lo := (16354841 / 200000000)) (hi := (40887103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 23037) = 1/(23037 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_886 : Bounds (-40887103 / 500000000) (-16354841 / 200000000) (Real.log (23037 / 25000)) := by
  have h := reflection_log_886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_887_neg : (37890821 / 500000000) ≤ -Real.log (1000000 / 1078727) ∧
    -Real.log (1000000 / 1078727) ≤ (75781643 / 1000000000) := by
  have h := checkLog_sound (w := (78727 / 2078727)) (n := 12)
    (lo := (37890821 / 500000000)) (hi := (75781643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078727 / 1000000) = 1/(1000000 / 1078727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_887 : Bounds (37890821 / 500000000) (75781643 / 1000000000) (Real.log (1078727 / 1000000)) := by
  have h := reflection_log_887_neg
  have he : Real.log (1078727 / 1000000) = -Real.log (1000000 / 1078727) := by
    rw [show ((1078727 / 1000000) : ℝ) = ((1000000 / 1078727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_888_neg : (81998869 / 1000000000) ≤ -Real.log (921273 / 1000000) ∧
    -Real.log (921273 / 1000000) ≤ (8199887 / 100000000) := by
  have h := checkLog_sound (w := (78727 / 1921273)) (n := 12)
    (lo := (81998869 / 1000000000)) (hi := (8199887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921273) = 1/(921273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_888 : Bounds (-8199887 / 100000000) (-81998869 / 1000000000) (Real.log (921273 / 1000000)) := by
  have h := reflection_log_888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_889_neg : (6217227 / 1000000000) ≤ -Real.log (993802059471 / 1000000000000) ∧
    -Real.log (993802059471 / 1000000000000) ≤ (1554307 / 250000000) := by
  have h := checkLog_sound (w := (6197940529 / 1993802059471)) (n := 12)
    (lo := (6217227 / 1000000000)) (hi := (1554307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993802059471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993802059471) = 1/(993802059471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_889 : Bounds (-1554307 / 250000000) (-6217227 / 1000000000) (Real.log (993802059471 / 1000000000000)) := by
  have h := reflection_log_889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_890_neg : (3092237 / 500000000) ≤ -Real.log (621146631 / 625000000) ∧
    -Real.log (621146631 / 625000000) ≤ (247379 / 40000000) := by
  have h := checkLog_sound (w := (3853369 / 1246146631)) (n := 12)
    (lo := (3092237 / 500000000)) (hi := (247379 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 621146631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 621146631) = 1/(621146631 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_890 : Bounds (-247379 / 40000000) (-3092237 / 500000000) (Real.log (621146631 / 625000000)) := by
  have h := reflection_log_890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_891_neg : (4917623 / 31250000) ≤ -Real.log (500000000000 / 585210747927) ∧
    -Real.log (500000000000 / 585210747927) ≤ (157363937 / 1000000000) := by
  have h := checkLog_sound (w := (85210747927 / 1085210747927)) (n := 12)
    (lo := (4917623 / 31250000)) (hi := (157363937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585210747927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585210747927 / 500000000000) = 1/(500000000000 / 585210747927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_891 : Bounds (4917623 / 31250000) (157363937 / 1000000000) (Real.log (585210747927 / 500000000000)) := by
  have h := reflection_log_891_neg
  have he : Real.log (585210747927 / 500000000000) = -Real.log (500000000000 / 585210747927) := by
    rw [show ((585210747927 / 500000000000) : ℝ) = ((500000000000 / 585210747927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_892_neg : (157780511 / 1000000000) ≤ -Real.log (500000000000 / 585454582953) ∧
    -Real.log (500000000000 / 585454582953) ≤ (4930641 / 31250000) := by
  have h := checkLog_sound (w := (85454582953 / 1085454582953)) (n := 12)
    (lo := (157780511 / 1000000000)) (hi := (4930641 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585454582953 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585454582953 / 500000000000) = 1/(500000000000 / 585454582953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_892 : Bounds (157780511 / 1000000000) (4930641 / 31250000) (Real.log (585454582953 / 500000000000)) := by
  have h := reflection_log_892_neg
  have he : Real.log (585454582953 / 500000000000) = -Real.log (500000000000 / 585454582953) := by
    rw [show ((585454582953 / 500000000000) : ℝ) = ((500000000000 / 585454582953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_893_neg : (315593579 / 1000000000) ≤ -Real.log (100000000000 / 137107291049) ∧
    -Real.log (100000000000 / 137107291049) ≤ (15779679 / 50000000) := by
  have h := checkLog_sound (w := (37107291049 / 237107291049)) (n := 12)
    (lo := (315593579 / 1000000000)) (hi := (15779679 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137107291049 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137107291049 / 100000000000) = 1/(100000000000 / 137107291049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_893 : Bounds (315593579 / 1000000000) (15779679 / 50000000) (Real.log (137107291049 / 100000000000)) := by
  have h := reflection_log_893_neg
  have he : Real.log (137107291049 / 100000000000) = -Real.log (100000000000 / 137107291049) := by
    rw [show ((137107291049 / 100000000000) : ℝ) = ((100000000000 / 137107291049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_894_neg : (78949651 / 250000000) ≤ -Real.log (25000000000 / 34283851079) ∧
    -Real.log (25000000000 / 34283851079) ≤ (63159721 / 200000000) := by
  have h := checkLog_sound (w := (9283851079 / 59283851079)) (n := 12)
    (lo := (78949651 / 250000000)) (hi := (63159721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34283851079 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34283851079 / 25000000000) = 1/(25000000000 / 34283851079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_894 : Bounds (78949651 / 250000000) (63159721 / 200000000) (Real.log (34283851079 / 25000000000)) := by
  have h := reflection_log_894_neg
  have he : Real.log (34283851079 / 25000000000) = -Real.log (25000000000 / 34283851079) := by
    rw [show ((34283851079 / 25000000000) : ℝ) = ((25000000000 / 34283851079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_895_neg : (145571123 / 1000000000) ≤ -Real.log (10000 / 11567) ∧
    -Real.log (10000 / 11567) ≤ (36392781 / 250000000) := by
  have h := checkLog_sound (w := (1567 / 21567)) (n := 12)
    (lo := (145571123 / 1000000000)) (hi := (36392781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11567 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11567 / 10000) = 1/(10000 / 11567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_895 : Bounds (145571123 / 1000000000) (36392781 / 250000000) (Real.log (11567 / 10000)) := by
  have h := reflection_log_895_neg
  have he : Real.log (11567 / 10000) = -Real.log (10000 / 11567) := by
    rw [show ((11567 / 10000) : ℝ) = ((10000 / 11567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0014 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_896_neg : (332876 / 1953125) ≤ -Real.log (8433 / 10000) ∧
    -Real.log (8433 / 10000) ≤ (170432513 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 18433)) (n := 12)
    (lo := (332876 / 1953125)) (hi := (170432513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8433) = 1/(8433 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_896 : Bounds (-170432513 / 1000000000) (-332876 / 1953125) (Real.log (8433 / 10000)) := by
  have h := reflection_log_896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_897_neg : (156687 / 1000000000) ≤ -Real.log (10000000 / 10001567) ∧
    -Real.log (10000000 / 10001567) ≤ (9793 / 62500000) := by
  have h := checkLog_sound (w := (1567 / 20001567)) (n := 12)
    (lo := (156687 / 1000000000)) (hi := (9793 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001567 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001567 / 10000000) = 1/(10000000 / 10001567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_897 : Bounds (156687 / 1000000000) (9793 / 62500000) (Real.log (10001567 / 10000000)) := by
  have h := reflection_log_897_neg
  have he : Real.log (10001567 / 10000000) = -Real.log (10000000 / 10001567) := by
    rw [show ((10001567 / 10000000) : ℝ) = ((10000000 / 10001567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_898_neg : (19589 / 125000000) ≤ -Real.log (9998433 / 10000000) ∧
    -Real.log (9998433 / 10000000) ≤ (156713 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 19998433)) (n := 12)
    (lo := (19589 / 125000000)) (hi := (156713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998433) = 1/(9998433 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_898 : Bounds (-156713 / 1000000000) (-19589 / 125000000) (Real.log (9998433 / 10000000)) := by
  have h := reflection_log_898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_899_neg : (75636089 / 1000000000) ≤ -Real.log (100000 / 107857) ∧
    -Real.log (100000 / 107857) ≤ (7563609 / 100000000) := by
  have h := checkLog_sound (w := (7857 / 207857)) (n := 12)
    (lo := (75636089 / 1000000000)) (hi := (7563609 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107857 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107857 / 100000) = 1/(100000 / 107857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_899 : Bounds (75636089 / 1000000000) (7563609 / 100000000) (Real.log (107857 / 100000)) := by
  have h := reflection_log_899_neg
  have he : Real.log (107857 / 100000) = -Real.log (100000 / 107857) := by
    rw [show ((107857 / 100000) : ℝ) = ((100000 / 107857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_900_neg : (81828467 / 1000000000) ≤ -Real.log (92143 / 100000) ∧
    -Real.log (92143 / 100000) ≤ (20457117 / 250000000) := by
  have h := checkLog_sound (w := (7857 / 192143)) (n := 12)
    (lo := (81828467 / 1000000000)) (hi := (20457117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92143) = 1/(92143 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_900 : Bounds (-20457117 / 250000000) (-81828467 / 1000000000) (Real.log (92143 / 100000)) := by
  have h := reflection_log_900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_901_neg : (75828919 / 1000000000) ≤ -Real.log (500000 / 539389) ∧
    -Real.log (500000 / 539389) ≤ (1895723 / 25000000) := by
  have h := checkLog_sound (w := (39389 / 1039389)) (n := 12)
    (lo := (75828919 / 1000000000)) (hi := (1895723 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539389 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539389 / 500000) = 1/(500000 / 539389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_901 : Bounds (75828919 / 1000000000) (1895723 / 25000000) (Real.log (539389 / 500000)) := by
  have h := reflection_log_901_neg
  have he : Real.log (539389 / 500000) = -Real.log (500000 / 539389) := by
    rw [show ((539389 / 500000) : ℝ) = ((500000 / 539389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_902_neg : (82054229 / 1000000000) ≤ -Real.log (460611 / 500000) ∧
    -Real.log (460611 / 500000) ≤ (8205423 / 100000000) := by
  have h := checkLog_sound (w := (39389 / 960611)) (n := 12)
    (lo := (82054229 / 1000000000)) (hi := (8205423 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460611) = 1/(460611 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_902 : Bounds (-8205423 / 100000000) (-82054229 / 1000000000) (Real.log (460611 / 500000)) := by
  have h := reflection_log_902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_903_neg : (622531 / 100000000) ≤ -Real.log (248448506679 / 250000000000) ∧
    -Real.log (248448506679 / 250000000000) ≤ (6225311 / 1000000000) := by
  have h := checkLog_sound (w := (1551493321 / 498448506679)) (n := 12)
    (lo := (622531 / 100000000)) (hi := (6225311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248448506679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248448506679) = 1/(248448506679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_903 : Bounds (-6225311 / 1000000000) (-622531 / 100000000) (Real.log (248448506679 / 250000000000)) := by
  have h := reflection_log_903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_904_neg : (3096189 / 500000000) ≤ -Real.log (9938267551 / 10000000000) ∧
    -Real.log (9938267551 / 10000000000) ≤ (6192379 / 1000000000) := by
  have h := checkLog_sound (w := (61732449 / 19938267551)) (n := 12)
    (lo := (3096189 / 500000000)) (hi := (6192379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9938267551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9938267551) = 1/(9938267551 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_904 : Bounds (-6192379 / 1000000000) (-3096189 / 500000000) (Real.log (9938267551 / 10000000000)) := by
  have h := reflection_log_904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_905_neg : (157464557 / 1000000000) ≤ -Real.log (12500000000 / 14631740881) ∧
    -Real.log (12500000000 / 14631740881) ≤ (78732279 / 500000000) := by
  have h := checkLog_sound (w := (2131740881 / 27131740881)) (n := 12)
    (lo := (157464557 / 1000000000)) (hi := (78732279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14631740881 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14631740881 / 12500000000) = 1/(12500000000 / 14631740881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_905 : Bounds (157464557 / 1000000000) (78732279 / 500000000) (Real.log (14631740881 / 12500000000)) := by
  have h := reflection_log_905_neg
  have he : Real.log (14631740881 / 12500000000) = -Real.log (12500000000 / 14631740881) := by
    rw [show ((14631740881 / 12500000000) : ℝ) = ((12500000000 / 14631740881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_906_neg : (39470787 / 250000000) ≤ -Real.log (500000000000 / 585514675073) ∧
    -Real.log (500000000000 / 585514675073) ≤ (157883149 / 1000000000) := by
  have h := checkLog_sound (w := (85514675073 / 1085514675073)) (n := 12)
    (lo := (39470787 / 250000000)) (hi := (157883149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585514675073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585514675073 / 500000000000) = 1/(500000000000 / 585514675073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_906 : Bounds (39470787 / 250000000) (157883149 / 1000000000) (Real.log (585514675073 / 500000000000)) := by
  have h := reflection_log_906_neg
  have he : Real.log (585514675073 / 500000000000) = -Real.log (500000000000 / 585514675073) := by
    rw [show ((585514675073 / 500000000000) : ℝ) = ((500000000000 / 585514675073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_907_neg : (78949651 / 250000000) ≤ -Real.log (500000000000 / 685677021579) ∧
    -Real.log (500000000000 / 685677021579) ≤ (63159721 / 200000000) := by
  have h := checkLog_sound (w := (185677021579 / 1185677021579)) (n := 12)
    (lo := (78949651 / 250000000)) (hi := (63159721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685677021579 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685677021579 / 500000000000) = 1/(500000000000 / 685677021579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_907 : Bounds (78949651 / 250000000) (63159721 / 200000000) (Real.log (685677021579 / 500000000000)) := by
  have h := reflection_log_907_neg
  have he : Real.log (685677021579 / 500000000000) = -Real.log (500000000000 / 685677021579) := by
    rw [show ((685677021579 / 500000000000) : ℝ) = ((500000000000 / 685677021579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_908_neg : (63200727 / 200000000) ≤ -Real.log (400000000 / 548654097) ∧
    -Real.log (400000000 / 548654097) ≤ (79000909 / 250000000) := by
  have h := checkLog_sound (w := (148654097 / 948654097)) (n := 12)
    (lo := (63200727 / 200000000)) (hi := (79000909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548654097 / 400000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548654097 / 400000000) = 1/(400000000 / 548654097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_908 : Bounds (63200727 / 200000000) (79000909 / 250000000) (Real.log (548654097 / 400000000)) := by
  have h := reflection_log_908_neg
  have he : Real.log (548654097 / 400000000) = -Real.log (400000000 / 548654097) := by
    rw [show ((548654097 / 400000000) : ℝ) = ((400000000 / 548654097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_909_neg : (36414393 / 250000000) ≤ -Real.log (625 / 723) ∧
    -Real.log (625 / 723) ≤ (145657573 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 674)) (n := 12)
    (lo := (36414393 / 250000000)) (hi := (145657573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723 / 625) = 1/(625 / 723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_909 : Bounds (36414393 / 250000000) (145657573 / 1000000000) (Real.log (723 / 625)) := by
  have h := reflection_log_909_neg
  have he : Real.log (723 / 625) = -Real.log (625 / 723) := by
    rw [show ((723 / 625) : ℝ) = ((625 / 723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_910_neg : (170551101 / 1000000000) ≤ -Real.log (527 / 625) ∧
    -Real.log (527 / 625) ≤ (85275551 / 500000000) := by
  have h := checkLog_sound (w := (49 / 576)) (n := 12)
    (lo := (170551101 / 1000000000)) (hi := (85275551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 527) = 1/(527 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_910 : Bounds (-85275551 / 500000000) (-170551101 / 1000000000) (Real.log (527 / 625)) := by
  have h := reflection_log_910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_911_neg : (156787 / 1000000000) ≤ -Real.log (312500 / 312549) ∧
    -Real.log (312500 / 312549) ≤ (39197 / 250000000) := by
  have h := checkLog_sound (w := (49 / 625049)) (n := 12)
    (lo := (156787 / 1000000000)) (hi := (39197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312549 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312549 / 312500) = 1/(312500 / 312549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_911 : Bounds (156787 / 1000000000) (39197 / 250000000) (Real.log (312549 / 312500)) := by
  have h := reflection_log_911_neg
  have he : Real.log (312549 / 312500) = -Real.log (312500 / 312549) := by
    rw [show ((312549 / 312500) : ℝ) = ((312500 / 312549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_912_neg : (39203 / 250000000) ≤ -Real.log (312451 / 312500) ∧
    -Real.log (312451 / 312500) ≤ (156813 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 624951)) (n := 12)
    (lo := (39203 / 250000000)) (hi := (156813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312451) = 1/(312451 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_912 : Bounds (-156813 / 1000000000) (-39203 / 250000000) (Real.log (312451 / 312500)) := by
  have h := reflection_log_912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_913_neg : (75683373 / 1000000000) ≤ -Real.log (1000000 / 1078621) ∧
    -Real.log (1000000 / 1078621) ≤ (37841687 / 500000000) := by
  have h := checkLog_sound (w := (78621 / 2078621)) (n := 12)
    (lo := (75683373 / 1000000000)) (hi := (37841687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078621 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078621 / 1000000) = 1/(1000000 / 1078621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_913 : Bounds (75683373 / 1000000000) (37841687 / 500000000) (Real.log (1078621 / 1000000)) := by
  have h := reflection_log_913_neg
  have he : Real.log (1078621 / 1000000) = -Real.log (1000000 / 1078621) := by
    rw [show ((1078621 / 1000000) : ℝ) = ((1000000 / 1078621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_914_neg : (40941909 / 500000000) ≤ -Real.log (921379 / 1000000) ∧
    -Real.log (921379 / 1000000) ≤ (81883819 / 1000000000) := by
  have h := checkLog_sound (w := (78621 / 1921379)) (n := 12)
    (lo := (40941909 / 500000000)) (hi := (81883819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921379) = 1/(921379 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_914 : Bounds (-81883819 / 1000000000) (-40941909 / 500000000) (Real.log (921379 / 1000000)) := by
  have h := reflection_log_914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_915_neg : (75876193 / 1000000000) ≤ -Real.log (1000000 / 1078829) ∧
    -Real.log (1000000 / 1078829) ≤ (37938097 / 500000000) := by
  have h := checkLog_sound (w := (78829 / 2078829)) (n := 12)
    (lo := (75876193 / 1000000000)) (hi := (37938097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078829 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078829 / 1000000) = 1/(1000000 / 1078829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_915 : Bounds (75876193 / 1000000000) (37938097 / 500000000) (Real.log (1078829 / 1000000)) := by
  have h := reflection_log_915_neg
  have he : Real.log (1078829 / 1000000) = -Real.log (1000000 / 1078829) := by
    rw [show ((1078829 / 1000000) : ℝ) = ((1000000 / 1078829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_916_neg : (10263699 / 125000000) ≤ -Real.log (921171 / 1000000) ∧
    -Real.log (921171 / 1000000) ≤ (82109593 / 1000000000) := by
  have h := checkLog_sound (w := (78829 / 1921171)) (n := 12)
    (lo := (10263699 / 125000000)) (hi := (82109593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921171) = 1/(921171 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_916 : Bounds (-82109593 / 1000000000) (-10263699 / 125000000) (Real.log (921171 / 1000000)) := by
  have h := reflection_log_916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_917_neg : (3116699 / 500000000) ≤ -Real.log (993785988759 / 1000000000000) ∧
    -Real.log (993785988759 / 1000000000000) ≤ (6233399 / 1000000000) := by
  have h := checkLog_sound (w := (6214011241 / 1993785988759)) (n := 12)
    (lo := (3116699 / 500000000)) (hi := (6233399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993785988759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993785988759) = 1/(993785988759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_917 : Bounds (-6233399 / 1000000000) (-3116699 / 500000000) (Real.log (993785988759 / 1000000000000)) := by
  have h := reflection_log_917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_918_neg : (1550111 / 250000000) ≤ -Real.log (993818738359 / 1000000000000) ∧
    -Real.log (993818738359 / 1000000000000) ≤ (1240089 / 200000000) := by
  have h := checkLog_sound (w := (6181261641 / 1993818738359)) (n := 12)
    (lo := (1550111 / 250000000)) (hi := (1240089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993818738359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993818738359) = 1/(993818738359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_918 : Bounds (-1240089 / 200000000) (-1550111 / 250000000) (Real.log (993818738359 / 1000000000000)) := by
  have h := reflection_log_918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_919_neg : (157567191 / 1000000000) ≤ -Real.log (100000000000 / 117065941377) ∧
    -Real.log (100000000000 / 117065941377) ≤ (19695899 / 125000000) := by
  have h := checkLog_sound (w := (17065941377 / 217065941377)) (n := 12)
    (lo := (157567191 / 1000000000)) (hi := (19695899 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117065941377 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117065941377 / 100000000000) = 1/(100000000000 / 117065941377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_919 : Bounds (157567191 / 1000000000) (19695899 / 125000000) (Real.log (117065941377 / 100000000000)) := by
  have h := reflection_log_919_neg
  have he : Real.log (117065941377 / 100000000000) = -Real.log (100000000000 / 117065941377) := by
    rw [show ((117065941377 / 100000000000) : ℝ) = ((100000000000 / 117065941377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_920_neg : (31597157 / 200000000) ≤ -Real.log (62500000000 / 73196846731) ∧
    -Real.log (62500000000 / 73196846731) ≤ (78992893 / 500000000) := by
  have h := checkLog_sound (w := (10696846731 / 135696846731)) (n := 12)
    (lo := (31597157 / 200000000)) (hi := (78992893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73196846731 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73196846731 / 62500000000) = 1/(62500000000 / 73196846731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_920 : Bounds (31597157 / 200000000) (78992893 / 500000000) (Real.log (73196846731 / 62500000000)) := by
  have h := reflection_log_920_neg
  have he : Real.log (73196846731 / 62500000000) = -Real.log (62500000000 / 73196846731) := by
    rw [show ((73196846731 / 62500000000) : ℝ) = ((62500000000 / 73196846731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_921_neg : (63200727 / 200000000) ≤ -Real.log (500000000000 / 685817621249) ∧
    -Real.log (500000000000 / 685817621249) ≤ (79000909 / 250000000) := by
  have h := checkLog_sound (w := (185817621249 / 1185817621249)) (n := 12)
    (lo := (63200727 / 200000000)) (hi := (79000909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685817621249 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685817621249 / 500000000000) = 1/(500000000000 / 685817621249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_921 : Bounds (63200727 / 200000000) (79000909 / 250000000) (Real.log (685817621249 / 500000000000)) := by
  have h := reflection_log_921_neg
  have he : Real.log (685817621249 / 500000000000) = -Real.log (500000000000 / 685817621249) := by
    rw [show ((685817621249 / 500000000000) : ℝ) = ((500000000000 / 685817621249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_922_neg : (316208673 / 1000000000) ≤ -Real.log (50000000000 / 68595825427) ∧
    -Real.log (50000000000 / 68595825427) ≤ (158104337 / 500000000) := by
  have h := checkLog_sound (w := (18595825427 / 118595825427)) (n := 12)
    (lo := (316208673 / 1000000000)) (hi := (158104337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68595825427 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68595825427 / 50000000000) = 1/(50000000000 / 68595825427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_922 : Bounds (316208673 / 1000000000) (158104337 / 500000000) (Real.log (68595825427 / 50000000000)) := by
  have h := reflection_log_922_neg
  have he : Real.log (68595825427 / 50000000000) = -Real.log (50000000000 / 68595825427) := by
    rw [show ((68595825427 / 50000000000) : ℝ) = ((50000000000 / 68595825427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_923_neg : (72872007 / 500000000) ≤ -Real.log (10000 / 11569) ∧
    -Real.log (10000 / 11569) ≤ (29148803 / 200000000) := by
  have h := checkLog_sound (w := (1569 / 21569)) (n := 12)
    (lo := (72872007 / 500000000)) (hi := (29148803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11569 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11569 / 10000) = 1/(10000 / 11569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_923 : Bounds (72872007 / 500000000) (29148803 / 200000000) (Real.log (11569 / 10000)) := by
  have h := reflection_log_923_neg
  have he : Real.log (11569 / 10000) = -Real.log (10000 / 11569) := by
    rw [show ((11569 / 10000) : ℝ) = ((10000 / 11569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_924_neg : (21333713 / 125000000) ≤ -Real.log (8431 / 10000) ∧
    -Real.log (8431 / 10000) ≤ (34133941 / 200000000) := by
  have h := checkLog_sound (w := (1569 / 18431)) (n := 12)
    (lo := (21333713 / 125000000)) (hi := (34133941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8431) = 1/(8431 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_924 : Bounds (-34133941 / 200000000) (-21333713 / 125000000) (Real.log (8431 / 10000)) := by
  have h := reflection_log_924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_925_neg : (156887 / 1000000000) ≤ -Real.log (10000000 / 10001569) ∧
    -Real.log (10000000 / 10001569) ≤ (19611 / 125000000) := by
  have h := checkLog_sound (w := (1569 / 20001569)) (n := 12)
    (lo := (156887 / 1000000000)) (hi := (19611 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001569 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001569 / 10000000) = 1/(10000000 / 10001569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_925 : Bounds (156887 / 1000000000) (19611 / 125000000) (Real.log (10001569 / 10000000)) := by
  have h := reflection_log_925_neg
  have he : Real.log (10001569 / 10000000) = -Real.log (10000000 / 10001569) := by
    rw [show ((10001569 / 10000000) : ℝ) = ((10000000 / 10001569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_926_neg : (9807 / 62500000) ≤ -Real.log (9998431 / 10000000) ∧
    -Real.log (9998431 / 10000000) ≤ (156913 / 1000000000) := by
  have h := checkLog_sound (w := (1569 / 19998431)) (n := 12)
    (lo := (9807 / 62500000)) (hi := (156913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998431) = 1/(9998431 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_926 : Bounds (-156913 / 1000000000) (-9807 / 62500000) (Real.log (9998431 / 10000000)) := by
  have h := reflection_log_926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_927_neg : (37865327 / 500000000) ≤ -Real.log (62500 / 67417) ∧
    -Real.log (62500 / 67417) ≤ (15146131 / 200000000) := by
  have h := checkLog_sound (w := (4917 / 129917)) (n := 12)
    (lo := (37865327 / 500000000)) (hi := (15146131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67417 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67417 / 62500) = 1/(62500 / 67417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_927 : Bounds (37865327 / 500000000) (15146131 / 200000000) (Real.log (67417 / 62500)) := by
  have h := reflection_log_927_neg
  have he : Real.log (67417 / 62500) = -Real.log (62500 / 67417) := by
    rw [show ((67417 / 62500) : ℝ) = ((62500 / 67417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_928_neg : (81939171 / 1000000000) ≤ -Real.log (57583 / 62500) ∧
    -Real.log (57583 / 62500) ≤ (20484793 / 250000000) := by
  have h := checkLog_sound (w := (4917 / 120083)) (n := 12)
    (lo := (81939171 / 1000000000)) (hi := (20484793 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57583) = 1/(57583 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_928 : Bounds (-20484793 / 250000000) (-81939171 / 1000000000) (Real.log (57583 / 62500)) := by
  have h := reflection_log_928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_929_neg : (75922539 / 1000000000) ≤ -Real.log (1000000 / 1078879) ∧
    -Real.log (1000000 / 1078879) ≤ (3796127 / 50000000) := by
  have h := checkLog_sound (w := (78879 / 2078879)) (n := 12)
    (lo := (75922539 / 1000000000)) (hi := (3796127 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078879 / 1000000) = 1/(1000000 / 1078879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_929 : Bounds (75922539 / 1000000000) (3796127 / 50000000) (Real.log (1078879 / 1000000)) := by
  have h := reflection_log_929_neg
  have he : Real.log (1078879 / 1000000) = -Real.log (1000000 / 1078879) := by
    rw [show ((1078879 / 1000000) : ℝ) = ((1000000 / 1078879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_930_neg : (2567621 / 31250000) ≤ -Real.log (921121 / 1000000) ∧
    -Real.log (921121 / 1000000) ≤ (82163873 / 1000000000) := by
  have h := checkLog_sound (w := (78879 / 1921121)) (n := 12)
    (lo := (2567621 / 31250000)) (hi := (82163873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921121) = 1/(921121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_930 : Bounds (-82163873 / 1000000000) (-2567621 / 31250000) (Real.log (921121 / 1000000)) := by
  have h := reflection_log_930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_931_neg : (6241333 / 1000000000) ≤ -Real.log (993778103359 / 1000000000000) ∧
    -Real.log (993778103359 / 1000000000000) ≤ (3120667 / 500000000) := by
  have h := checkLog_sound (w := (6221896641 / 1993778103359)) (n := 12)
    (lo := (6241333 / 1000000000)) (hi := (3120667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993778103359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993778103359) = 1/(993778103359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_931 : Bounds (-3120667 / 500000000) (-6241333 / 1000000000) (Real.log (993778103359 / 1000000000000)) := by
  have h := reflection_log_931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_932_neg : (1552129 / 250000000) ≤ -Real.log (3882073111 / 3906250000) ∧
    -Real.log (3882073111 / 3906250000) ≤ (6208517 / 1000000000) := by
  have h := checkLog_sound (w := (24176889 / 7788323111)) (n := 12)
    (lo := (1552129 / 250000000)) (hi := (6208517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3882073111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3882073111) = 1/(3882073111 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_932 : Bounds (-6208517 / 1000000000) (-1552129 / 250000000) (Real.log (3882073111 / 3906250000)) := by
  have h := reflection_log_932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_933_neg : (78834913 / 500000000) ≤ -Real.log (500000000000 / 585389785179) ∧
    -Real.log (500000000000 / 585389785179) ≤ (157669827 / 1000000000) := by
  have h := checkLog_sound (w := (85389785179 / 1085389785179)) (n := 12)
    (lo := (78834913 / 500000000)) (hi := (157669827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585389785179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585389785179 / 500000000000) = 1/(500000000000 / 585389785179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_933 : Bounds (78834913 / 500000000) (157669827 / 1000000000) (Real.log (585389785179 / 500000000000)) := by
  have h := reflection_log_933_neg
  have he : Real.log (585389785179 / 500000000000) = -Real.log (500000000000 / 585389785179) := by
    rw [show ((585389785179 / 500000000000) : ℝ) = ((500000000000 / 585389785179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_934_neg : (158086411 / 1000000000) ≤ -Real.log (125000000000 / 146408425169) ∧
    -Real.log (125000000000 / 146408425169) ≤ (39521603 / 250000000) := by
  have h := checkLog_sound (w := (21408425169 / 271408425169)) (n := 12)
    (lo := (158086411 / 1000000000)) (hi := (39521603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146408425169 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146408425169 / 125000000000) = 1/(125000000000 / 146408425169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_934 : Bounds (158086411 / 1000000000) (39521603 / 250000000) (Real.log (146408425169 / 125000000000)) := by
  have h := reflection_log_934_neg
  have he : Real.log (146408425169 / 125000000000) = -Real.log (125000000000 / 146408425169) := by
    rw [show ((146408425169 / 125000000000) : ℝ) = ((125000000000 / 146408425169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_935_neg : (316208673 / 1000000000) ≤ -Real.log (500000000000 / 685958254269) ∧
    -Real.log (500000000000 / 685958254269) ≤ (158104337 / 500000000) := by
  have h := checkLog_sound (w := (185958254269 / 1185958254269)) (n := 12)
    (lo := (316208673 / 1000000000)) (hi := (158104337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685958254269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685958254269 / 500000000000) = 1/(500000000000 / 685958254269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_935 : Bounds (316208673 / 1000000000) (158104337 / 500000000) (Real.log (685958254269 / 500000000000)) := by
  have h := reflection_log_935_neg
  have he : Real.log (685958254269 / 500000000000) = -Real.log (500000000000 / 685958254269) := by
    rw [show ((685958254269 / 500000000000) : ℝ) = ((500000000000 / 685958254269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_936_neg : (158206859 / 500000000) ≤ -Real.log (10000000000 / 13721978413) ∧
    -Real.log (10000000000 / 13721978413) ≤ (316413719 / 1000000000) := by
  have h := checkLog_sound (w := (3721978413 / 23721978413)) (n := 12)
    (lo := (158206859 / 500000000)) (hi := (316413719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13721978413 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13721978413 / 10000000000) = 1/(10000000000 / 13721978413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_936 : Bounds (158206859 / 500000000) (316413719 / 1000000000) (Real.log (13721978413 / 10000000000)) := by
  have h := reflection_log_936_neg
  have he : Real.log (13721978413 / 10000000000) = -Real.log (10000000000 / 13721978413) := by
    rw [show ((13721978413 / 10000000000) : ℝ) = ((10000000000 / 13721978413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_937_neg : (9114403 / 62500000) ≤ -Real.log (1000 / 1157) ∧
    -Real.log (1000 / 1157) ≤ (145830449 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 2157)) (n := 12)
    (lo := (9114403 / 62500000)) (hi := (145830449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 1000) = 1/(1000 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_937 : Bounds (9114403 / 62500000) (145830449 / 1000000000) (Real.log (1157 / 1000)) := by
  have h := reflection_log_937_neg
  have he : Real.log (1157 / 1000) = -Real.log (1000 / 1157) := by
    rw [show ((1157 / 1000) : ℝ) = ((1000 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_938_neg : (1067427 / 6250000) ≤ -Real.log (843 / 1000) ∧
    -Real.log (843 / 1000) ≤ (170788321 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 1843)) (n := 12)
    (lo := (1067427 / 6250000)) (hi := (170788321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 843) = 1/(843 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_938 : Bounds (-170788321 / 1000000000) (-1067427 / 6250000) (Real.log (843 / 1000)) := by
  have h := reflection_log_938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_939_neg : (156987 / 1000000000) ≤ -Real.log (1000000 / 1000157) ∧
    -Real.log (1000000 / 1000157) ≤ (39247 / 250000000) := by
  have h := checkLog_sound (w := (157 / 2000157)) (n := 12)
    (lo := (156987 / 1000000000)) (hi := (39247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000157 / 1000000) = 1/(1000000 / 1000157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_939 : Bounds (156987 / 1000000000) (39247 / 250000000) (Real.log (1000157 / 1000000)) := by
  have h := reflection_log_939_neg
  have he : Real.log (1000157 / 1000000) = -Real.log (1000000 / 1000157) := by
    rw [show ((1000157 / 1000000) : ℝ) = ((1000000 / 1000157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_940_neg : (39253 / 250000000) ≤ -Real.log (999843 / 1000000) ∧
    -Real.log (999843 / 1000000) ≤ (157013 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 1999843)) (n := 12)
    (lo := (39253 / 250000000)) (hi := (157013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999843) = 1/(999843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_940 : Bounds (-157013 / 1000000000) (-39253 / 250000000) (Real.log (999843 / 1000000)) := by
  have h := reflection_log_940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_941_neg : (75777007 / 1000000000) ≤ -Real.log (500000 / 539361) ∧
    -Real.log (500000 / 539361) ≤ (4736063 / 62500000) := by
  have h := checkLog_sound (w := (39361 / 1039361)) (n := 12)
    (lo := (75777007 / 1000000000)) (hi := (4736063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539361 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539361 / 500000) = 1/(500000 / 539361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_941 : Bounds (75777007 / 1000000000) (4736063 / 62500000) (Real.log (539361 / 500000)) := by
  have h := reflection_log_941_neg
  have he : Real.log (539361 / 500000) = -Real.log (500000 / 539361) := by
    rw [show ((539361 / 500000) : ℝ) = ((500000 / 539361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_942_neg : (40996721 / 500000000) ≤ -Real.log (460639 / 500000) ∧
    -Real.log (460639 / 500000) ≤ (81993443 / 1000000000) := by
  have h := checkLog_sound (w := (39361 / 960639)) (n := 12)
    (lo := (40996721 / 500000000)) (hi := (81993443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460639) = 1/(460639 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_942 : Bounds (-81993443 / 1000000000) (-40996721 / 500000000) (Real.log (460639 / 500000)) := by
  have h := reflection_log_942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_943_neg : (75969809 / 1000000000) ≤ -Real.log (100000 / 107893) ∧
    -Real.log (100000 / 107893) ≤ (7596981 / 100000000) := by
  have h := checkLog_sound (w := (7893 / 207893)) (n := 12)
    (lo := (75969809 / 1000000000)) (hi := (7596981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107893 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107893 / 100000) = 1/(100000 / 107893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_943 : Bounds (75969809 / 1000000000) (7596981 / 100000000) (Real.log (107893 / 100000)) := by
  have h := reflection_log_943_neg
  have he : Real.log (107893 / 100000) = -Real.log (100000 / 107893) := by
    rw [show ((107893 / 100000) : ℝ) = ((100000 / 107893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_944_neg : (82219241 / 1000000000) ≤ -Real.log (92107 / 100000) ∧
    -Real.log (92107 / 100000) ≤ (41109621 / 500000000) := by
  have h := checkLog_sound (w := (7893 / 192107)) (n := 12)
    (lo := (82219241 / 1000000000)) (hi := (41109621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92107) = 1/(92107 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_944 : Bounds (-41109621 / 500000000) (-82219241 / 1000000000) (Real.log (92107 / 100000)) := by
  have h := reflection_log_944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_945_neg : (6249431 / 1000000000) ≤ -Real.log (9937700551 / 10000000000) ∧
    -Real.log (9937700551 / 10000000000) ≤ (781179 / 125000000) := by
  have h := checkLog_sound (w := (62299449 / 19937700551)) (n := 12)
    (lo := (6249431 / 1000000000)) (hi := (781179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9937700551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9937700551) = 1/(9937700551 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_945 : Bounds (-781179 / 125000000) (-6249431 / 1000000000) (Real.log (9937700551 / 10000000000)) := by
  have h := reflection_log_945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_946_neg : (1243287 / 200000000) ≤ -Real.log (248450711679 / 250000000000) ∧
    -Real.log (248450711679 / 250000000000) ≤ (1554109 / 250000000) := by
  have h := checkLog_sound (w := (1549288321 / 498450711679)) (n := 12)
    (lo := (1243287 / 200000000)) (hi := (1554109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248450711679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248450711679) = 1/(248450711679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_946 : Bounds (-1554109 / 250000000) (-1243287 / 200000000) (Real.log (248450711679 / 250000000000)) := by
  have h := reflection_log_946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_947_neg : (157770449 / 1000000000) ≤ -Real.log (20000000000 / 23417947677) ∧
    -Real.log (20000000000 / 23417947677) ≤ (3155409 / 20000000) := by
  have h := checkLog_sound (w := (3417947677 / 43417947677)) (n := 12)
    (lo := (157770449 / 1000000000)) (hi := (3155409 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23417947677 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23417947677 / 20000000000) = 1/(20000000000 / 23417947677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_947 : Bounds (157770449 / 1000000000) (3155409 / 20000000) (Real.log (23417947677 / 20000000000)) := by
  have h := reflection_log_947_neg
  have he : Real.log (23417947677 / 20000000000) = -Real.log (20000000000 / 23417947677) := by
    rw [show ((23417947677 / 20000000000) : ℝ) = ((20000000000 / 23417947677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_948_neg : (3163781 / 20000000) ≤ -Real.log (500000000000 / 585693812631) ∧
    -Real.log (500000000000 / 585693812631) ≤ (158189051 / 1000000000) := by
  have h := checkLog_sound (w := (85693812631 / 1085693812631)) (n := 12)
    (lo := (3163781 / 20000000)) (hi := (158189051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585693812631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585693812631 / 500000000000) = 1/(500000000000 / 585693812631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_948 : Bounds (3163781 / 20000000) (158189051 / 1000000000) (Real.log (585693812631 / 500000000000)) := by
  have h := reflection_log_948_neg
  have he : Real.log (585693812631 / 500000000000) = -Real.log (500000000000 / 585693812631) := by
    rw [show ((585693812631 / 500000000000) : ℝ) = ((500000000000 / 585693812631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_949_neg : (158206859 / 500000000) ≤ -Real.log (500000000000 / 686098920649) ∧
    -Real.log (500000000000 / 686098920649) ≤ (316413719 / 1000000000) := by
  have h := checkLog_sound (w := (186098920649 / 1186098920649)) (n := 12)
    (lo := (158206859 / 500000000)) (hi := (316413719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686098920649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686098920649 / 500000000000) = 1/(500000000000 / 686098920649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_949 : Bounds (158206859 / 500000000) (316413719 / 1000000000) (Real.log (686098920649 / 500000000000)) := by
  have h := reflection_log_949_neg
  have he : Real.log (686098920649 / 500000000000) = -Real.log (500000000000 / 686098920649) := by
    rw [show ((686098920649 / 500000000000) : ℝ) = ((500000000000 / 686098920649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_950_neg : (316618769 / 1000000000) ≤ -Real.log (125000000000 / 171559905101) ∧
    -Real.log (125000000000 / 171559905101) ≤ (31661877 / 100000000) := by
  have h := checkLog_sound (w := (46559905101 / 296559905101)) (n := 12)
    (lo := (316618769 / 1000000000)) (hi := (31661877 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171559905101 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171559905101 / 125000000000) = 1/(125000000000 / 171559905101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_950 : Bounds (316618769 / 1000000000) (31661877 / 100000000) (Real.log (171559905101 / 125000000000)) := by
  have h := reflection_log_950_neg
  have he : Real.log (171559905101 / 125000000000) = -Real.log (125000000000 / 171559905101) := by
    rw [show ((171559905101 / 125000000000) : ℝ) = ((125000000000 / 171559905101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_951_neg : (72958437 / 500000000) ≤ -Real.log (10000 / 11571) ∧
    -Real.log (10000 / 11571) ≤ (233467 / 1600000) := by
  have h := checkLog_sound (w := (1571 / 21571)) (n := 12)
    (lo := (72958437 / 500000000)) (hi := (233467 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11571 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11571 / 10000) = 1/(10000 / 11571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_951 : Bounds (72958437 / 500000000) (233467 / 1600000) (Real.log (11571 / 10000)) := by
  have h := reflection_log_951_neg
  have he : Real.log (11571 / 10000) = -Real.log (10000 / 11571) := by
    rw [show ((11571 / 10000) : ℝ) = ((10000 / 11571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_952_neg : (170906951 / 1000000000) ≤ -Real.log (8429 / 10000) ∧
    -Real.log (8429 / 10000) ≤ (21363369 / 125000000) := by
  have h := checkLog_sound (w := (1571 / 18429)) (n := 12)
    (lo := (170906951 / 1000000000)) (hi := (21363369 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8429) = 1/(8429 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_952 : Bounds (-21363369 / 125000000) (-170906951 / 1000000000) (Real.log (8429 / 10000)) := by
  have h := reflection_log_952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_953_neg : (157087 / 1000000000) ≤ -Real.log (10000000 / 10001571) ∧
    -Real.log (10000000 / 10001571) ≤ (4909 / 31250000) := by
  have h := checkLog_sound (w := (1571 / 20001571)) (n := 12)
    (lo := (157087 / 1000000000)) (hi := (4909 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001571 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001571 / 10000000) = 1/(10000000 / 10001571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_953 : Bounds (157087 / 1000000000) (4909 / 31250000) (Real.log (10001571 / 10000000)) := by
  have h := reflection_log_953_neg
  have he : Real.log (10001571 / 10000000) = -Real.log (10000000 / 10001571) := by
    rw [show ((10001571 / 10000000) : ℝ) = ((10000000 / 10001571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_954_neg : (19639 / 125000000) ≤ -Real.log (9998429 / 10000000) ∧
    -Real.log (9998429 / 10000000) ≤ (157113 / 1000000000) := by
  have h := checkLog_sound (w := (1571 / 19998429)) (n := 12)
    (lo := (19639 / 125000000)) (hi := (157113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998429) = 1/(9998429 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_954 : Bounds (-157113 / 1000000000) (-19639 / 125000000) (Real.log (9998429 / 10000000)) := by
  have h := reflection_log_954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_955_neg : (18956071 / 250000000) ≤ -Real.log (1000000 / 1078773) ∧
    -Real.log (1000000 / 1078773) ≤ (15164857 / 200000000) := by
  have h := checkLog_sound (w := (78773 / 2078773)) (n := 12)
    (lo := (18956071 / 250000000)) (hi := (15164857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078773 / 1000000) = 1/(1000000 / 1078773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_955 : Bounds (18956071 / 250000000) (15164857 / 200000000) (Real.log (1078773 / 1000000)) := by
  have h := reflection_log_955_neg
  have he : Real.log (1078773 / 1000000) = -Real.log (1000000 / 1078773) := by
    rw [show ((1078773 / 1000000) : ℝ) = ((1000000 / 1078773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_956_neg : (82048801 / 1000000000) ≤ -Real.log (921227 / 1000000) ∧
    -Real.log (921227 / 1000000) ≤ (41024401 / 500000000) := by
  have h := checkLog_sound (w := (78773 / 1921227)) (n := 12)
    (lo := (82048801 / 1000000000)) (hi := (41024401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921227) = 1/(921227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_956 : Bounds (-41024401 / 500000000) (-82048801 / 1000000000) (Real.log (921227 / 1000000)) := by
  have h := reflection_log_956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_957_neg : (76017077 / 1000000000) ≤ -Real.log (1000000 / 1078981) ∧
    -Real.log (1000000 / 1078981) ≤ (38008539 / 500000000) := by
  have h := checkLog_sound (w := (78981 / 2078981)) (n := 12)
    (lo := (76017077 / 1000000000)) (hi := (38008539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078981 / 1000000) = 1/(1000000 / 1078981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_957 : Bounds (76017077 / 1000000000) (38008539 / 500000000) (Real.log (1078981 / 1000000)) := by
  have h := reflection_log_957_neg
  have he : Real.log (1078981 / 1000000) = -Real.log (1000000 / 1078981) := by
    rw [show ((1078981 / 1000000) : ℝ) = ((1000000 / 1078981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_958_neg : (82274613 / 1000000000) ≤ -Real.log (921019 / 1000000) ∧
    -Real.log (921019 / 1000000) ≤ (41137307 / 500000000) := by
  have h := checkLog_sound (w := (78981 / 1921019)) (n := 12)
    (lo := (82274613 / 1000000000)) (hi := (41137307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921019) = 1/(921019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_958 : Bounds (-41137307 / 500000000) (-82274613 / 1000000000) (Real.log (921019 / 1000000)) := by
  have h := reflection_log_958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_959_neg : (1251507 / 200000000) ≤ -Real.log (993762001639 / 1000000000000) ∧
    -Real.log (993762001639 / 1000000000000) ≤ (48887 / 7812500) := by
  have h := checkLog_sound (w := (6237998361 / 1993762001639)) (n := 12)
    (lo := (1251507 / 200000000)) (hi := (48887 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993762001639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993762001639) = 1/(993762001639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_959 : Bounds (-48887 / 7812500) (-1251507 / 200000000) (Real.log (993762001639 / 1000000000000)) := by
  have h := reflection_log_959_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


