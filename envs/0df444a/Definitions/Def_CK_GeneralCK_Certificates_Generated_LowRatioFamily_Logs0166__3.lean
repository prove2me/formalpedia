-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0166__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0166__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T01:20:56.431407+00:00
-- url     : https://prove2.me/theorems/bc671281-8084-46d9-860f-4371c691625b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0166 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0167, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0166 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0167, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0168)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0166 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0167, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0168)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0166 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0167, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0168) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0166 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0167, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0168).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0166 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10624_neg : (187805303 / 500000000) ≤ -Real.log (500000000000 / 727940056879) ∧
    -Real.log (500000000000 / 727940056879) ≤ (375610607 / 1000000000) := by
  have h := checkLog_sound (w := (227940056879 / 1227940056879)) (n := 12)
    (lo := (187805303 / 500000000)) (hi := (375610607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727940056879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727940056879 / 500000000000) = 1/(500000000000 / 727940056879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10624 : Bounds (187805303 / 500000000) (375610607 / 1000000000) (Real.log (727940056879 / 500000000000)) := by
  have h := reflection_log_10624_neg
  have he : Real.log (727940056879 / 500000000000) = -Real.log (500000000000 / 727940056879) := by
    rw [show ((727940056879 / 500000000000) : ℝ) = ((500000000000 / 727940056879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10625_neg : (756070547 / 1000000000) ≤ -Real.log (500000000000 / 1064945226917) ∧
    -Real.log (500000000000 / 1064945226917) ≤ (756070549 / 1000000000) := by
  have h := checkLog_sound (w := (64945226917 / 2064945226917)) (n := 12)
    (lo := (62923367 / 1000000000)) (hi := (7865421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1064945226917 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1064945226917 / 1000000000000) = 1/(500000000000 / 1064945226917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10625 : Bounds (756070547 / 1000000000) (756070549 / 1000000000) (Real.log (1064945226917 / 500000000000)) := by
  have h := reflection_log_10625_neg
  have he : Real.log (1064945226917 / 500000000000) = -Real.log (500000000000 / 1064945226917) := by
    rw [show ((1064945226917 / 500000000000) : ℝ) = ((500000000000 / 1064945226917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10626_neg : (379185601 / 500000000) ≤ -Real.log (500000000000 / 1067398119123) ∧
    -Real.log (500000000000 / 1067398119123) ≤ (189592801 / 250000000) := by
  have h := checkLog_sound (w := (67398119123 / 2067398119123)) (n := 12)
    (lo := (32612011 / 500000000)) (hi := (65224023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067398119123 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1067398119123 / 1000000000000) = 1/(500000000000 / 1067398119123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10626 : Bounds (379185601 / 500000000) (189592801 / 250000000) (Real.log (1067398119123 / 500000000000)) := by
  have h := reflection_log_10626_neg
  have he : Real.log (1067398119123 / 500000000000) = -Real.log (500000000000 / 1067398119123) := by
    rw [show ((1067398119123 / 500000000000) : ℝ) = ((500000000000 / 1067398119123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10627_neg : (38711019 / 125000000) ≤ -Real.log (1000 / 1363) ∧
    -Real.log (1000 / 1363) ≤ (309688153 / 1000000000) := by
  have h := checkLog_sound (w := (363 / 2363)) (n := 12)
    (lo := (38711019 / 125000000)) (hi := (309688153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363 / 1000) = 1/(1000 / 1363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10627 : Bounds (38711019 / 125000000) (309688153 / 1000000000) (Real.log (1363 / 1000)) := by
  have h := reflection_log_10627_neg
  have he : Real.log (1363 / 1000) = -Real.log (1000 / 1363) := by
    rw [show ((1363 / 1000) : ℝ) = ((1000 / 1363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10628_neg : (450985623 / 1000000000) ≤ -Real.log (637 / 1000) ∧
    -Real.log (637 / 1000) ≤ (56373203 / 125000000) := by
  have h := checkLog_sound (w := (363 / 1637)) (n := 12)
    (lo := (450985623 / 1000000000)) (hi := (56373203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 637) = 1/(637 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10628 : Bounds (-56373203 / 125000000) (-450985623 / 1000000000) (Real.log (637 / 1000)) := by
  have h := reflection_log_10628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10629_neg : (181467 / 500000000) ≤ -Real.log (1000000 / 1000363) ∧
    -Real.log (1000000 / 1000363) ≤ (72587 / 200000000) := by
  have h := checkLog_sound (w := (363 / 2000363)) (n := 12)
    (lo := (181467 / 500000000)) (hi := (72587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000363 / 1000000) = 1/(1000000 / 1000363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10629 : Bounds (181467 / 500000000) (72587 / 200000000) (Real.log (1000363 / 1000000)) := by
  have h := reflection_log_10629_neg
  have he : Real.log (1000363 / 1000000) = -Real.log (1000000 / 1000363) := by
    rw [show ((1000363 / 1000000) : ℝ) = ((1000000 / 1000363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10630_neg : (72613 / 200000000) ≤ -Real.log (999637 / 1000000) ∧
    -Real.log (999637 / 1000000) ≤ (181533 / 500000000) := by
  have h := checkLog_sound (w := (363 / 1999637)) (n := 12)
    (lo := (72613 / 200000000)) (hi := (181533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999637) = 1/(999637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10630 : Bounds (-181533 / 500000000) (-72613 / 200000000) (Real.log (999637 / 1000000)) := by
  have h := reflection_log_10630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10631_neg : (169973971 / 1000000000) ≤ -Real.log (500000 / 592637) ∧
    -Real.log (500000 / 592637) ≤ (42493493 / 250000000) := by
  have h := checkLog_sound (w := (92637 / 1092637)) (n := 12)
    (lo := (169973971 / 1000000000)) (hi := (42493493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592637 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592637 / 500000) = 1/(500000 / 592637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10631 : Bounds (169973971 / 1000000000) (42493493 / 250000000) (Real.log (592637 / 500000)) := by
  have h := reflection_log_10631_neg
  have he : Real.log (592637 / 500000) = -Real.log (500000 / 592637) := by
    rw [show ((592637 / 500000) : ℝ) = ((500000 / 592637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10632_neg : (102451709 / 500000000) ≤ -Real.log (407363 / 500000) ∧
    -Real.log (407363 / 500000) ≤ (204903419 / 1000000000) := by
  have h := checkLog_sound (w := (92637 / 907363)) (n := 12)
    (lo := (102451709 / 500000000)) (hi := (204903419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 407363) = 1/(407363 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10632 : Bounds (-204903419 / 1000000000) (-102451709 / 500000000) (Real.log (407363 / 500000)) := by
  have h := reflection_log_10632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10633_neg : (170726257 / 1000000000) ≤ -Real.log (500000 / 593083) ∧
    -Real.log (500000 / 593083) ≤ (85363129 / 500000000) := by
  have h := checkLog_sound (w := (93083 / 1093083)) (n := 12)
    (lo := (170726257 / 1000000000)) (hi := (85363129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593083 / 500000) = 1/(500000 / 593083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10633 : Bounds (170726257 / 1000000000) (85363129 / 500000000) (Real.log (593083 / 500000)) := by
  have h := reflection_log_10633_neg
  have he : Real.log (593083 / 500000) = -Real.log (500000 / 593083) := by
    rw [show ((593083 / 500000) : ℝ) = ((500000 / 593083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10634_neg : (12874929 / 62500000) ≤ -Real.log (406917 / 500000) ∧
    -Real.log (406917 / 500000) ≤ (41199773 / 200000000) := by
  have h := checkLog_sound (w := (93083 / 906917)) (n := 12)
    (lo := (12874929 / 62500000)) (hi := (41199773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406917) = 1/(406917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10634 : Bounds (-41199773 / 200000000) (-12874929 / 62500000) (Real.log (406917 / 500000)) := by
  have h := reflection_log_10634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10635_neg : (35272607 / 1000000000) ≤ -Real.log (241335555111 / 250000000000) ∧
    -Real.log (241335555111 / 250000000000) ≤ (1102269 / 31250000) := by
  have h := checkLog_sound (w := (8664444889 / 491335555111)) (n := 12)
    (lo := (35272607 / 1000000000)) (hi := (1102269 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241335555111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241335555111) = 1/(241335555111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10635 : Bounds (-1102269 / 31250000) (-35272607 / 1000000000) (Real.log (241335555111 / 250000000000)) := by
  have h := reflection_log_10635_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10636_neg : (34929447 / 1000000000) ≤ -Real.log (241418386231 / 250000000000) ∧
    -Real.log (241418386231 / 250000000000) ≤ (4366181 / 125000000) := by
  have h := checkLog_sound (w := (8581613769 / 491418386231)) (n := 12)
    (lo := (34929447 / 1000000000)) (hi := (4366181 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241418386231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241418386231) = 1/(241418386231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10636 : Bounds (-4366181 / 125000000) (-34929447 / 1000000000) (Real.log (241418386231 / 250000000000)) := by
  have h := reflection_log_10636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10637_neg : (37487739 / 100000000) ≤ -Real.log (250000000000 / 363703257291) ∧
    -Real.log (250000000000 / 363703257291) ≤ (374877391 / 1000000000) := by
  have h := checkLog_sound (w := (113703257291 / 613703257291)) (n := 12)
    (lo := (37487739 / 100000000)) (hi := (374877391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363703257291 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363703257291 / 250000000000) = 1/(250000000000 / 363703257291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10637 : Bounds (37487739 / 100000000) (374877391 / 1000000000) (Real.log (363703257291 / 250000000000)) := by
  have h := reflection_log_10637_neg
  have he : Real.log (363703257291 / 250000000000) = -Real.log (250000000000 / 363703257291) := by
    rw [show ((363703257291 / 250000000000) : ℝ) = ((250000000000 / 363703257291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10638_neg : (188362561 / 500000000) ≤ -Real.log (250000000000 / 364375904669) ∧
    -Real.log (250000000000 / 364375904669) ≤ (376725123 / 1000000000) := by
  have h := checkLog_sound (w := (114375904669 / 614375904669)) (n := 12)
    (lo := (188362561 / 500000000)) (hi := (376725123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364375904669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364375904669 / 250000000000) = 1/(250000000000 / 364375904669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10638 : Bounds (188362561 / 500000000) (376725123 / 1000000000) (Real.log (364375904669 / 250000000000)) := by
  have h := reflection_log_10638_neg
  have he : Real.log (364375904669 / 250000000000) = -Real.log (250000000000 / 364375904669) := by
    rw [show ((364375904669 / 250000000000) : ℝ) = ((250000000000 / 364375904669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10639_neg : (379185601 / 500000000) ≤ -Real.log (250000000000 / 533699059561) ∧
    -Real.log (250000000000 / 533699059561) ≤ (189592801 / 250000000) := by
  have h := checkLog_sound (w := (33699059561 / 1033699059561)) (n := 12)
    (lo := (32612011 / 500000000)) (hi := (65224023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((533699059561 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(533699059561 / 500000000000) = 1/(250000000000 / 533699059561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10639 : Bounds (379185601 / 500000000) (189592801 / 250000000) (Real.log (533699059561 / 250000000000)) := by
  have h := reflection_log_10639_neg
  have he : Real.log (533699059561 / 250000000000) = -Real.log (250000000000 / 533699059561) := by
    rw [show ((533699059561 / 250000000000) : ℝ) = ((250000000000 / 533699059561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10640_neg : (30426951 / 40000000) ≤ -Real.log (125000000000 / 267464678179) ∧
    -Real.log (125000000000 / 267464678179) ≤ (760673777 / 1000000000) := by
  have h := checkLog_sound (w := (17464678179 / 517464678179)) (n := 12)
    (lo := (13505319 / 200000000)) (hi := (16881649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267464678179 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(267464678179 / 250000000000) = 1/(125000000000 / 267464678179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10640 : Bounds (30426951 / 40000000) (760673777 / 1000000000) (Real.log (267464678179 / 125000000000)) := by
  have h := reflection_log_10640_neg
  have he : Real.log (267464678179 / 125000000000) = -Real.log (125000000000 / 267464678179) := by
    rw [show ((267464678179 / 125000000000) : ℝ) = ((125000000000 / 267464678179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10641_neg : (310421559 / 1000000000) ≤ -Real.log (250 / 341) ∧
    -Real.log (250 / 341) ≤ (7760539 / 25000000) := by
  have h := checkLog_sound (w := (91 / 591)) (n := 12)
    (lo := (310421559 / 1000000000)) (hi := (7760539 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341 / 250) = 1/(250 / 341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10641 : Bounds (310421559 / 1000000000) (7760539 / 25000000) (Real.log (341 / 250)) := by
  have h := reflection_log_10641_neg
  have he : Real.log (341 / 250) = -Real.log (250 / 341) := by
    rw [show ((341 / 250) : ℝ) = ((250 / 341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10642_neg : (90511343 / 200000000) ≤ -Real.log (159 / 250) ∧
    -Real.log (159 / 250) ≤ (113139179 / 250000000) := by
  have h := checkLog_sound (w := (91 / 409)) (n := 12)
    (lo := (90511343 / 200000000)) (hi := (113139179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 159) = 1/(159 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10642 : Bounds (-113139179 / 250000000) (-90511343 / 200000000) (Real.log (159 / 250)) := by
  have h := reflection_log_10642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10643_neg : (363933 / 1000000000) ≤ -Real.log (250000 / 250091) ∧
    -Real.log (250000 / 250091) ≤ (181967 / 500000000) := by
  have h := checkLog_sound (w := (91 / 500091)) (n := 12)
    (lo := (363933 / 1000000000)) (hi := (181967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250091 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250091 / 250000) = 1/(250000 / 250091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10643 : Bounds (363933 / 1000000000) (181967 / 500000000) (Real.log (250091 / 250000)) := by
  have h := reflection_log_10643_neg
  have he : Real.log (250091 / 250000) = -Real.log (250000 / 250091) := by
    rw [show ((250091 / 250000) : ℝ) = ((250000 / 250091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10644_neg : (182033 / 500000000) ≤ -Real.log (249909 / 250000) ∧
    -Real.log (249909 / 250000) ≤ (364067 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 499909)) (n := 12)
    (lo := (182033 / 500000000)) (hi := (364067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249909) = 1/(249909 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10644 : Bounds (-364067 / 1000000000) (-182033 / 500000000) (Real.log (249909 / 250000)) := by
  have h := reflection_log_10644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10645_neg : (170427771 / 1000000000) ≤ -Real.log (250000 / 296453) ∧
    -Real.log (250000 / 296453) ≤ (42606943 / 250000000) := by
  have h := checkLog_sound (w := (46453 / 546453)) (n := 12)
    (lo := (170427771 / 1000000000)) (hi := (42606943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296453 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296453 / 250000) = 1/(250000 / 296453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10645 : Bounds (170427771 / 1000000000) (42606943 / 250000000) (Real.log (296453 / 250000)) := by
  have h := reflection_log_10645_neg
  have he : Real.log (296453 / 250000) = -Real.log (250000 / 296453) := by
    rw [show ((296453 / 250000) : ℝ) = ((250000 / 296453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10646_neg : (205563981 / 1000000000) ≤ -Real.log (203547 / 250000) ∧
    -Real.log (203547 / 250000) ≤ (102781991 / 500000000) := by
  have h := checkLog_sound (w := (46453 / 453547)) (n := 12)
    (lo := (205563981 / 1000000000)) (hi := (102781991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203547) = 1/(203547 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10646 : Bounds (-102781991 / 500000000) (-205563981 / 1000000000) (Real.log (203547 / 250000)) := by
  have h := reflection_log_10646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10647_neg : (171180559 / 1000000000) ≤ -Real.log (200000 / 237341) ∧
    -Real.log (200000 / 237341) ≤ (2139757 / 12500000) := by
  have h := checkLog_sound (w := (37341 / 437341)) (n := 12)
    (lo := (171180559 / 1000000000)) (hi := (2139757 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237341 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237341 / 200000) = 1/(200000 / 237341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10647 : Bounds (171180559 / 1000000000) (2139757 / 12500000) (Real.log (237341 / 200000)) := by
  have h := reflection_log_10647_neg
  have he : Real.log (237341 / 200000) = -Real.log (200000 / 237341) := by
    rw [show ((237341 / 200000) : ℝ) = ((200000 / 237341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10648_neg : (206661381 / 1000000000) ≤ -Real.log (162659 / 200000) ∧
    -Real.log (162659 / 200000) ≤ (103330691 / 500000000) := by
  have h := checkLog_sound (w := (37341 / 362659)) (n := 12)
    (lo := (206661381 / 1000000000)) (hi := (103330691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162659) = 1/(162659 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10648 : Bounds (-103330691 / 500000000) (-206661381 / 1000000000) (Real.log (162659 / 200000)) := by
  have h := reflection_log_10648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10649_neg : (17740411 / 500000000) ≤ -Real.log (38605649719 / 40000000000) ∧
    -Real.log (38605649719 / 40000000000) ≤ (35480823 / 1000000000) := by
  have h := checkLog_sound (w := (1394350281 / 78605649719)) (n := 12)
    (lo := (17740411 / 500000000)) (hi := (35480823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38605649719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38605649719) = 1/(38605649719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10649 : Bounds (-35480823 / 1000000000) (-17740411 / 500000000) (Real.log (38605649719 / 40000000000)) := by
  have h := reflection_log_10649_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10650_neg : (35136209 / 1000000000) ≤ -Real.log (60342118791 / 62500000000) ∧
    -Real.log (60342118791 / 62500000000) ≤ (3513621 / 100000000) := by
  have h := checkLog_sound (w := (2157881209 / 122842118791)) (n := 12)
    (lo := (35136209 / 1000000000)) (hi := (3513621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60342118791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60342118791) = 1/(60342118791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10650 : Bounds (-3513621 / 100000000) (-35136209 / 1000000000) (Real.log (60342118791 / 62500000000)) := by
  have h := reflection_log_10650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10651_neg : (375991753 / 1000000000) ≤ -Real.log (100000000000 / 145643512309) ∧
    -Real.log (100000000000 / 145643512309) ≤ (187995877 / 500000000) := by
  have h := checkLog_sound (w := (45643512309 / 245643512309)) (n := 12)
    (lo := (375991753 / 1000000000)) (hi := (187995877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145643512309 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145643512309 / 100000000000) = 1/(100000000000 / 145643512309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10651 : Bounds (375991753 / 1000000000) (187995877 / 500000000) (Real.log (145643512309 / 100000000000)) := by
  have h := reflection_log_10651_neg
  have he : Real.log (145643512309 / 100000000000) = -Real.log (100000000000 / 145643512309) := by
    rw [show ((145643512309 / 100000000000) : ℝ) = ((100000000000 / 145643512309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10652_neg : (18892097 / 50000000) ≤ -Real.log (100000000000 / 145913229517) ∧
    -Real.log (100000000000 / 145913229517) ≤ (377841941 / 1000000000) := by
  have h := checkLog_sound (w := (45913229517 / 245913229517)) (n := 12)
    (lo := (18892097 / 50000000)) (hi := (377841941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145913229517 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145913229517 / 100000000000) = 1/(100000000000 / 145913229517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10652 : Bounds (18892097 / 50000000) (377841941 / 1000000000) (Real.log (145913229517 / 100000000000)) := by
  have h := reflection_log_10652_neg
  have he : Real.log (145913229517 / 100000000000) = -Real.log (100000000000 / 145913229517) := by
    rw [show ((145913229517 / 100000000000) : ℝ) = ((100000000000 / 145913229517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10653_neg : (30426951 / 40000000) ≤ -Real.log (100000000000 / 213971742543) ∧
    -Real.log (100000000000 / 213971742543) ≤ (760673777 / 1000000000) := by
  have h := checkLog_sound (w := (13971742543 / 413971742543)) (n := 12)
    (lo := (13505319 / 200000000)) (hi := (16881649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213971742543 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(213971742543 / 200000000000) = 1/(100000000000 / 213971742543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10653 : Bounds (30426951 / 40000000) (760673777 / 1000000000) (Real.log (213971742543 / 100000000000)) := by
  have h := reflection_log_10653_neg
  have he : Real.log (213971742543 / 100000000000) = -Real.log (100000000000 / 213971742543) := by
    rw [show ((213971742543 / 100000000000) : ℝ) = ((100000000000 / 213971742543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10654_neg : (381489137 / 500000000) ≤ -Real.log (250000000000 / 536163522013) ∧
    -Real.log (250000000000 / 536163522013) ≤ (190744569 / 250000000) := by
  have h := checkLog_sound (w := (36163522013 / 1036163522013)) (n := 12)
    (lo := (34915547 / 500000000)) (hi := (13966219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((536163522013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(536163522013 / 500000000000) = 1/(250000000000 / 536163522013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10654 : Bounds (381489137 / 500000000) (190744569 / 250000000) (Real.log (536163522013 / 250000000000)) := by
  have h := reflection_log_10654_neg
  have he : Real.log (536163522013 / 250000000000) = -Real.log (250000000000 / 536163522013) := by
    rw [show ((536163522013 / 250000000000) : ℝ) = ((250000000000 / 536163522013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10655_neg : (77788607 / 250000000) ≤ -Real.log (200 / 273) ∧
    -Real.log (200 / 273) ≤ (311154429 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 473)) (n := 12)
    (lo := (77788607 / 250000000)) (hi := (311154429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273 / 200) = 1/(200 / 273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10655 : Bounds (77788607 / 250000000) (311154429 / 1000000000) (Real.log (273 / 200)) := by
  have h := reflection_log_10655_neg
  have he : Real.log (273 / 200) = -Real.log (200 / 273) := by
    rw [show ((273 / 200) : ℝ) = ((200 / 273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10656_neg : (11353257 / 25000000) ≤ -Real.log (127 / 200) ∧
    -Real.log (127 / 200) ≤ (454130281 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 127) = 1/(127 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10656 : Bounds (-454130281 / 1000000000) (-11353257 / 25000000) (Real.log (127 / 200)) := by
  have h := reflection_log_10656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10657_neg : (364933 / 1000000000) ≤ -Real.log (200000 / 200073) ∧
    -Real.log (200000 / 200073) ≤ (182467 / 500000000) := by
  have h := checkLog_sound (w := (73 / 400073)) (n := 12)
    (lo := (364933 / 1000000000)) (hi := (182467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200073 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200073 / 200000) = 1/(200000 / 200073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10657 : Bounds (364933 / 1000000000) (182467 / 500000000) (Real.log (200073 / 200000)) := by
  have h := reflection_log_10657_neg
  have he : Real.log (200073 / 200000) = -Real.log (200000 / 200073) := by
    rw [show ((200073 / 200000) : ℝ) = ((200000 / 200073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10658_neg : (182533 / 500000000) ≤ -Real.log (199927 / 200000) ∧
    -Real.log (199927 / 200000) ≤ (365067 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 399927)) (n := 12)
    (lo := (182533 / 500000000)) (hi := (365067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199927) = 1/(199927 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10658 : Bounds (-365067 / 1000000000) (-182533 / 500000000) (Real.log (199927 / 200000)) := by
  have h := reflection_log_10658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10659_neg : (170880523 / 1000000000) ≤ -Real.log (1000000 / 1186349) ∧
    -Real.log (1000000 / 1186349) ≤ (42720131 / 250000000) := by
  have h := checkLog_sound (w := (186349 / 2186349)) (n := 12)
    (lo := (170880523 / 1000000000)) (hi := (42720131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186349 / 1000000) = 1/(1000000 / 1186349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10659 : Bounds (170880523 / 1000000000) (42720131 / 250000000) (Real.log (1186349 / 1000000)) := by
  have h := reflection_log_10659_neg
  have he : Real.log (1186349 / 1000000) = -Real.log (1000000 / 1186349) := by
    rw [show ((1186349 / 1000000) : ℝ) = ((1000000 / 1186349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10660_neg : (206223751 / 1000000000) ≤ -Real.log (813651 / 1000000) ∧
    -Real.log (813651 / 1000000) ≤ (25777969 / 125000000) := by
  have h := checkLog_sound (w := (186349 / 1813651)) (n := 12)
    (lo := (206223751 / 1000000000)) (hi := (25777969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813651) = 1/(813651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10660 : Bounds (-25777969 / 125000000) (-206223751 / 1000000000) (Real.log (813651 / 1000000)) := by
  have h := reflection_log_10660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10661_neg : (85817327 / 500000000) ≤ -Real.log (250000 / 296811) ∧
    -Real.log (250000 / 296811) ≤ (34326931 / 200000000) := by
  have h := checkLog_sound (w := (46811 / 546811)) (n := 12)
    (lo := (85817327 / 500000000)) (hi := (34326931 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296811 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296811 / 250000) = 1/(250000 / 296811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10661 : Bounds (85817327 / 500000000) (34326931 / 200000000) (Real.log (296811 / 250000)) := by
  have h := reflection_log_10661_neg
  have he : Real.log (296811 / 250000) = -Real.log (250000 / 296811) := by
    rw [show ((296811 / 250000) : ℝ) = ((250000 / 296811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10662_neg : (207324337 / 1000000000) ≤ -Real.log (203189 / 250000) ∧
    -Real.log (203189 / 250000) ≤ (103662169 / 500000000) := by
  have h := checkLog_sound (w := (46811 / 453189)) (n := 12)
    (lo := (207324337 / 1000000000)) (hi := (103662169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203189) = 1/(203189 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10662 : Bounds (-103662169 / 500000000) (-207324337 / 1000000000) (Real.log (203189 / 250000)) := by
  have h := reflection_log_10662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10663_neg : (17844841 / 500000000) ≤ -Real.log (60308730279 / 62500000000) ∧
    -Real.log (60308730279 / 62500000000) ≤ (35689683 / 1000000000) := by
  have h := checkLog_sound (w := (2191269721 / 122808730279)) (n := 12)
    (lo := (17844841 / 500000000)) (hi := (35689683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60308730279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60308730279) = 1/(60308730279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10663 : Bounds (-35689683 / 1000000000) (-17844841 / 500000000) (Real.log (60308730279 / 62500000000)) := by
  have h := reflection_log_10663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10664_neg : (8835807 / 250000000) ≤ -Real.log (965274050199 / 1000000000000) ∧
    -Real.log (965274050199 / 1000000000000) ≤ (35343229 / 1000000000) := by
  have h := checkLog_sound (w := (34725949801 / 1965274050199)) (n := 12)
    (lo := (8835807 / 250000000)) (hi := (35343229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965274050199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965274050199) = 1/(965274050199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10664 : Bounds (-35343229 / 1000000000) (-8835807 / 250000000) (Real.log (965274050199 / 1000000000000)) := by
  have h := reflection_log_10664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10665_neg : (15084171 / 40000000) ≤ -Real.log (250000000000 / 364514085277) ∧
    -Real.log (250000000000 / 364514085277) ≤ (94276069 / 250000000) := by
  have h := checkLog_sound (w := (114514085277 / 614514085277)) (n := 12)
    (lo := (15084171 / 40000000)) (hi := (94276069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364514085277 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364514085277 / 250000000000) = 1/(250000000000 / 364514085277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10665 : Bounds (15084171 / 40000000) (94276069 / 250000000) (Real.log (364514085277 / 250000000000)) := by
  have h := reflection_log_10665_neg
  have he : Real.log (364514085277 / 250000000000) = -Real.log (250000000000 / 364514085277) := by
    rw [show ((364514085277 / 250000000000) : ℝ) = ((250000000000 / 364514085277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10666_neg : (23684937 / 62500000) ≤ -Real.log (125000000000 / 182595391483) ∧
    -Real.log (125000000000 / 182595391483) ≤ (378958993 / 1000000000) := by
  have h := checkLog_sound (w := (57595391483 / 307595391483)) (n := 12)
    (lo := (23684937 / 62500000)) (hi := (378958993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182595391483 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182595391483 / 125000000000) = 1/(125000000000 / 182595391483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10666 : Bounds (23684937 / 62500000) (378958993 / 1000000000) (Real.log (182595391483 / 125000000000)) := by
  have h := reflection_log_10666_neg
  have he : Real.log (182595391483 / 125000000000) = -Real.log (125000000000 / 182595391483) := by
    rw [show ((182595391483 / 125000000000) : ℝ) = ((125000000000 / 182595391483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10667_neg : (381489137 / 500000000) ≤ -Real.log (20000000000 / 42893081761) ∧
    -Real.log (20000000000 / 42893081761) ≤ (190744569 / 250000000) := by
  have h := checkLog_sound (w := (2893081761 / 82893081761)) (n := 12)
    (lo := (34915547 / 500000000)) (hi := (13966219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42893081761 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(42893081761 / 40000000000) = 1/(20000000000 / 42893081761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10667 : Bounds (381489137 / 500000000) (190744569 / 250000000) (Real.log (42893081761 / 20000000000)) := by
  have h := reflection_log_10667_neg
  have he : Real.log (42893081761 / 20000000000) = -Real.log (20000000000 / 42893081761) := by
    rw [show ((42893081761 / 20000000000) : ℝ) = ((20000000000 / 42893081761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10668_neg : (191321177 / 250000000) ≤ -Real.log (500000000000 / 1074803149607) ∧
    -Real.log (500000000000 / 1074803149607) ≤ (76528471 / 100000000) := by
  have h := checkLog_sound (w := (74803149607 / 2074803149607)) (n := 12)
    (lo := (9017191 / 125000000)) (hi := (72137529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1074803149607 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1074803149607 / 1000000000000) = 1/(500000000000 / 1074803149607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10668 : Bounds (191321177 / 250000000) (76528471 / 100000000) (Real.log (1074803149607 / 500000000000)) := by
  have h := reflection_log_10668_neg
  have he : Real.log (1074803149607 / 500000000000) = -Real.log (500000000000 / 1074803149607) := by
    rw [show ((1074803149607 / 500000000000) : ℝ) = ((500000000000 / 1074803149607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10669_neg : (311886761 / 1000000000) ≤ -Real.log (500 / 683) ∧
    -Real.log (500 / 683) ≤ (155943381 / 500000000) := by
  have h := checkLog_sound (w := (183 / 1183)) (n := 12)
    (lo := (311886761 / 1000000000)) (hi := (155943381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683 / 500) = 1/(500 / 683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10669 : Bounds (311886761 / 1000000000) (155943381 / 500000000) (Real.log (683 / 500)) := by
  have h := reflection_log_10669_neg
  have he : Real.log (683 / 500) = -Real.log (500 / 683) := by
    rw [show ((683 / 500) : ℝ) = ((500 / 683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10670_neg : (113926581 / 250000000) ≤ -Real.log (317 / 500) ∧
    -Real.log (317 / 500) ≤ (18228253 / 40000000) := by
  have h := checkLog_sound (w := (183 / 817)) (n := 12)
    (lo := (113926581 / 250000000)) (hi := (18228253 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 317) = 1/(317 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10670 : Bounds (-18228253 / 40000000) (-113926581 / 250000000) (Real.log (317 / 500)) := by
  have h := reflection_log_10670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10671_neg : (365933 / 1000000000) ≤ -Real.log (500000 / 500183) ∧
    -Real.log (500000 / 500183) ≤ (182967 / 500000000) := by
  have h := checkLog_sound (w := (183 / 1000183)) (n := 12)
    (lo := (365933 / 1000000000)) (hi := (182967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500183 / 500000) = 1/(500000 / 500183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10671 : Bounds (365933 / 1000000000) (182967 / 500000000) (Real.log (500183 / 500000)) := by
  have h := reflection_log_10671_neg
  have he : Real.log (500183 / 500000) = -Real.log (500000 / 500183) := by
    rw [show ((500183 / 500000) : ℝ) = ((500000 / 500183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10672_neg : (183033 / 500000000) ≤ -Real.log (499817 / 500000) ∧
    -Real.log (499817 / 500000) ≤ (366067 / 1000000000) := by
  have h := checkLog_sound (w := (183 / 999817)) (n := 12)
    (lo := (183033 / 500000000)) (hi := (366067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499817) = 1/(499817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10672 : Bounds (-366067 / 1000000000) (-183033 / 500000000) (Real.log (499817 / 500000)) := by
  have h := reflection_log_10672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10673_neg : (171333913 / 1000000000) ≤ -Real.log (1000000 / 1186887) ∧
    -Real.log (1000000 / 1186887) ≤ (85666957 / 500000000) := by
  have h := checkLog_sound (w := (186887 / 2186887)) (n := 12)
    (lo := (171333913 / 1000000000)) (hi := (85666957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186887 / 1000000) = 1/(1000000 / 1186887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10673 : Bounds (171333913 / 1000000000) (85666957 / 500000000) (Real.log (1186887 / 1000000)) := by
  have h := reflection_log_10673_neg
  have he : Real.log (1186887 / 1000000) = -Real.log (1000000 / 1186887) := by
    rw [show ((1186887 / 1000000) : ℝ) = ((1000000 / 1186887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10674_neg : (206885187 / 1000000000) ≤ -Real.log (813113 / 1000000) ∧
    -Real.log (813113 / 1000000) ≤ (51721297 / 250000000) := by
  have h := checkLog_sound (w := (186887 / 1813113)) (n := 12)
    (lo := (206885187 / 1000000000)) (hi := (51721297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813113) = 1/(813113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10674 : Bounds (-51721297 / 250000000) (-206885187 / 1000000000) (Real.log (813113 / 1000000)) := by
  have h := reflection_log_10674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10675_neg : (5377767 / 31250000) ≤ -Real.log (1000000 / 1187783) ∧
    -Real.log (1000000 / 1187783) ≤ (34417709 / 200000000) := by
  have h := checkLog_sound (w := (187783 / 2187783)) (n := 12)
    (lo := (5377767 / 31250000)) (hi := (34417709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187783 / 1000000) = 1/(1000000 / 1187783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10675 : Bounds (5377767 / 31250000) (34417709 / 200000000) (Real.log (1187783 / 1000000)) := by
  have h := reflection_log_10675_neg
  have he : Real.log (1187783 / 1000000) = -Real.log (1000000 / 1187783) := by
    rw [show ((1187783 / 1000000) : ℝ) = ((1000000 / 1187783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10676_neg : (207987733 / 1000000000) ≤ -Real.log (812217 / 1000000) ∧
    -Real.log (812217 / 1000000) ≤ (103993867 / 500000000) := by
  have h := checkLog_sound (w := (187783 / 1812217)) (n := 12)
    (lo := (207987733 / 1000000000)) (hi := (103993867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812217) = 1/(812217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10676 : Bounds (-103993867 / 500000000) (-207987733 / 1000000000) (Real.log (812217 / 1000000)) := by
  have h := reflection_log_10676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10677_neg : (8974797 / 250000000) ≤ -Real.log (964737544911 / 1000000000000) ∧
    -Real.log (964737544911 / 1000000000000) ≤ (35899189 / 1000000000) := by
  have h := checkLog_sound (w := (35262455089 / 1964737544911)) (n := 12)
    (lo := (8974797 / 250000000)) (hi := (35899189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964737544911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964737544911) = 1/(964737544911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10677 : Bounds (-35899189 / 1000000000) (-8974797 / 250000000) (Real.log (964737544911 / 1000000000000)) := by
  have h := reflection_log_10677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10678_neg : (17775637 / 500000000) ≤ -Real.log (965073249231 / 1000000000000) ∧
    -Real.log (965073249231 / 1000000000000) ≤ (1422051 / 40000000) := by
  have h := checkLog_sound (w := (34926750769 / 1965073249231)) (n := 12)
    (lo := (17775637 / 500000000)) (hi := (1422051 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965073249231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965073249231) = 1/(965073249231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10678 : Bounds (-1422051 / 40000000) (-17775637 / 500000000) (Real.log (965073249231 / 1000000000000)) := by
  have h := reflection_log_10678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10679_neg : (3782191 / 10000000) ≤ -Real.log (250000000000 / 364920681381) ∧
    -Real.log (250000000000 / 364920681381) ≤ (378219101 / 1000000000) := by
  have h := checkLog_sound (w := (114920681381 / 614920681381)) (n := 12)
    (lo := (3782191 / 10000000)) (hi := (378219101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364920681381 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364920681381 / 250000000000) = 1/(250000000000 / 364920681381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10679 : Bounds (3782191 / 10000000) (378219101 / 1000000000) (Real.log (364920681381 / 250000000000)) := by
  have h := reflection_log_10679_neg
  have he : Real.log (364920681381 / 250000000000) = -Real.log (250000000000 / 364920681381) := by
    rw [show ((364920681381 / 250000000000) : ℝ) = ((250000000000 / 364920681381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10680_neg : (380076277 / 1000000000) ≤ -Real.log (500000000000 / 731198066527) ∧
    -Real.log (500000000000 / 731198066527) ≤ (190038139 / 500000000) := by
  have h := checkLog_sound (w := (231198066527 / 1231198066527)) (n := 12)
    (lo := (380076277 / 1000000000)) (hi := (190038139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731198066527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731198066527 / 500000000000) = 1/(500000000000 / 731198066527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10680 : Bounds (380076277 / 1000000000) (190038139 / 500000000) (Real.log (731198066527 / 500000000000)) := by
  have h := reflection_log_10680_neg
  have he : Real.log (731198066527 / 500000000000) = -Real.log (500000000000 / 731198066527) := by
    rw [show ((731198066527 / 500000000000) : ℝ) = ((500000000000 / 731198066527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10681_neg : (191321177 / 250000000) ≤ -Real.log (250000000000 / 537401574803) ∧
    -Real.log (250000000000 / 537401574803) ≤ (76528471 / 100000000) := by
  have h := checkLog_sound (w := (37401574803 / 1037401574803)) (n := 12)
    (lo := (9017191 / 125000000)) (hi := (72137529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537401574803 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(537401574803 / 500000000000) = 1/(250000000000 / 537401574803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10681 : Bounds (191321177 / 250000000) (76528471 / 100000000) (Real.log (537401574803 / 250000000000)) := by
  have h := reflection_log_10681_neg
  have he : Real.log (537401574803 / 250000000000) = -Real.log (250000000000 / 537401574803) := by
    rw [show ((537401574803 / 250000000000) : ℝ) = ((250000000000 / 537401574803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10682_neg : (153518617 / 200000000) ≤ -Real.log (500000000000 / 1077287066247) ∧
    -Real.log (500000000000 / 1077287066247) ≤ (767593087 / 1000000000) := by
  have h := checkLog_sound (w := (77287066247 / 2077287066247)) (n := 12)
    (lo := (14889181 / 200000000)) (hi := (37222953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077287066247 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1077287066247 / 1000000000000) = 1/(500000000000 / 1077287066247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10682 : Bounds (153518617 / 200000000) (767593087 / 1000000000) (Real.log (1077287066247 / 500000000000)) := by
  have h := reflection_log_10682_neg
  have he : Real.log (1077287066247 / 500000000000) = -Real.log (500000000000 / 1077287066247) := by
    rw [show ((1077287066247 / 500000000000) : ℝ) = ((500000000000 / 1077287066247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10683_neg : (312618557 / 1000000000) ≤ -Real.log (1000 / 1367) ∧
    -Real.log (1000 / 1367) ≤ (156309279 / 500000000) := by
  have h := checkLog_sound (w := (367 / 2367)) (n := 12)
    (lo := (312618557 / 1000000000)) (hi := (156309279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1367 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1367 / 1000) = 1/(1000 / 1367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10683 : Bounds (312618557 / 1000000000) (156309279 / 500000000) (Real.log (1367 / 1000)) := by
  have h := reflection_log_10683_neg
  have he : Real.log (1367 / 1000) = -Real.log (1000 / 1367) := by
    rw [show ((1367 / 1000) : ℝ) = ((1000 / 1367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10684_neg : (57160607 / 125000000) ≤ -Real.log (633 / 1000) ∧
    -Real.log (633 / 1000) ≤ (457284857 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1633)) (n := 12)
    (lo := (57160607 / 125000000)) (hi := (457284857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 633) = 1/(633 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10684 : Bounds (-457284857 / 1000000000) (-57160607 / 125000000) (Real.log (633 / 1000)) := by
  have h := reflection_log_10684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10685_neg : (91733 / 250000000) ≤ -Real.log (1000000 / 1000367) ∧
    -Real.log (1000000 / 1000367) ≤ (366933 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2000367)) (n := 12)
    (lo := (91733 / 250000000)) (hi := (366933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000367 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000367 / 1000000) = 1/(1000000 / 1000367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10685 : Bounds (91733 / 250000000) (366933 / 1000000000) (Real.log (1000367 / 1000000)) := by
  have h := reflection_log_10685_neg
  have he : Real.log (1000367 / 1000000) = -Real.log (1000000 / 1000367) := by
    rw [show ((1000367 / 1000000) : ℝ) = ((1000000 / 1000367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10686_neg : (367067 / 1000000000) ≤ -Real.log (999633 / 1000000) ∧
    -Real.log (999633 / 1000000) ≤ (91767 / 250000000) := by
  have h := checkLog_sound (w := (367 / 1999633)) (n := 12)
    (lo := (367067 / 1000000000)) (hi := (91767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999633) = 1/(999633 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10686 : Bounds (-91767 / 250000000) (-367067 / 1000000000) (Real.log (999633 / 1000000)) := by
  have h := reflection_log_10686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10687_neg : (171787939 / 1000000000) ≤ -Real.log (500000 / 593713) ∧
    -Real.log (500000 / 593713) ≤ (8589397 / 50000000) := by
  have h := checkLog_sound (w := (93713 / 1093713)) (n := 12)
    (lo := (171787939 / 1000000000)) (hi := (8589397 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593713 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593713 / 500000) = 1/(500000 / 593713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10687 : Bounds (171787939 / 1000000000) (8589397 / 50000000) (Real.log (593713 / 500000)) := by
  have h := reflection_log_10687_neg
  have he : Real.log (593713 / 500000) = -Real.log (500000 / 593713) := by
    rw [show ((593713 / 500000) : ℝ) = ((500000 / 593713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0167 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10688_neg : (51887073 / 250000000) ≤ -Real.log (406287 / 500000) ∧
    -Real.log (406287 / 500000) ≤ (207548293 / 1000000000) := by
  have h := checkLog_sound (w := (93713 / 906287)) (n := 12)
    (lo := (51887073 / 250000000)) (hi := (207548293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406287) = 1/(406287 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10688 : Bounds (-207548293 / 1000000000) (-51887073 / 250000000) (Real.log (406287 / 500000)) := by
  have h := reflection_log_10688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10689_neg : (172542227 / 1000000000) ≤ -Real.log (500000 / 594161) ∧
    -Real.log (500000 / 594161) ≤ (43135557 / 250000000) := by
  have h := checkLog_sound (w := (94161 / 1094161)) (n := 12)
    (lo := (172542227 / 1000000000)) (hi := (43135557 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594161 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594161 / 500000) = 1/(500000 / 594161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10689 : Bounds (172542227 / 1000000000) (43135557 / 250000000) (Real.log (594161 / 500000)) := by
  have h := reflection_log_10689_neg
  have he : Real.log (594161 / 500000) = -Real.log (500000 / 594161) := by
    rw [show ((594161 / 500000) : ℝ) = ((500000 / 594161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10690_neg : (208651569 / 1000000000) ≤ -Real.log (405839 / 500000) ∧
    -Real.log (405839 / 500000) ≤ (20865157 / 100000000) := by
  have h := checkLog_sound (w := (94161 / 905839)) (n := 12)
    (lo := (208651569 / 1000000000)) (hi := (20865157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405839) = 1/(405839 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10690 : Bounds (-20865157 / 100000000) (-208651569 / 1000000000) (Real.log (405839 / 500000)) := by
  have h := reflection_log_10690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10691_neg : (36109341 / 1000000000) ≤ -Real.log (241133706079 / 250000000000) ∧
    -Real.log (241133706079 / 250000000000) ≤ (18054671 / 500000000) := by
  have h := checkLog_sound (w := (8866293921 / 491133706079)) (n := 12)
    (lo := (36109341 / 1000000000)) (hi := (18054671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241133706079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241133706079) = 1/(241133706079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10691 : Bounds (-18054671 / 500000000) (-36109341 / 1000000000) (Real.log (241133706079 / 250000000000)) := by
  have h := reflection_log_10691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10692_neg : (1117511 / 31250000) ≤ -Real.log (241217873631 / 250000000000) ∧
    -Real.log (241217873631 / 250000000000) ≤ (35760353 / 1000000000) := by
  have h := checkLog_sound (w := (8782126369 / 491217873631)) (n := 12)
    (lo := (1117511 / 31250000)) (hi := (35760353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241217873631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241217873631) = 1/(241217873631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10692 : Bounds (-35760353 / 1000000000) (-1117511 / 31250000) (Real.log (241217873631 / 250000000000)) := by
  have h := reflection_log_10692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10693_neg : (379336231 / 1000000000) ≤ -Real.log (250000000000 / 365328573151) ∧
    -Real.log (250000000000 / 365328573151) ≤ (47417029 / 125000000) := by
  have h := checkLog_sound (w := (115328573151 / 615328573151)) (n := 12)
    (lo := (379336231 / 1000000000)) (hi := (47417029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365328573151 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365328573151 / 250000000000) = 1/(250000000000 / 365328573151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10693 : Bounds (379336231 / 1000000000) (47417029 / 125000000) (Real.log (365328573151 / 250000000000)) := by
  have h := reflection_log_10693_neg
  have he : Real.log (365328573151 / 250000000000) = -Real.log (250000000000 / 365328573151) := by
    rw [show ((365328573151 / 250000000000) : ℝ) = ((250000000000 / 365328573151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10694_neg : (381193797 / 1000000000) ≤ -Real.log (500000000000 / 732015651527) ∧
    -Real.log (500000000000 / 732015651527) ≤ (190596899 / 500000000) := by
  have h := checkLog_sound (w := (232015651527 / 1232015651527)) (n := 12)
    (lo := (381193797 / 1000000000)) (hi := (190596899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732015651527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732015651527 / 500000000000) = 1/(500000000000 / 732015651527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10694 : Bounds (381193797 / 1000000000) (190596899 / 500000000) (Real.log (732015651527 / 500000000000)) := by
  have h := reflection_log_10694_neg
  have he : Real.log (732015651527 / 500000000000) = -Real.log (500000000000 / 732015651527) := by
    rw [show ((732015651527 / 500000000000) : ℝ) = ((500000000000 / 732015651527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10695_neg : (153518617 / 200000000) ≤ -Real.log (250000000000 / 538643533123) ∧
    -Real.log (250000000000 / 538643533123) ≤ (767593087 / 1000000000) := by
  have h := checkLog_sound (w := (38643533123 / 1038643533123)) (n := 12)
    (lo := (14889181 / 200000000)) (hi := (37222953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538643533123 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(538643533123 / 500000000000) = 1/(250000000000 / 538643533123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10695 : Bounds (153518617 / 200000000) (767593087 / 1000000000) (Real.log (538643533123 / 250000000000)) := by
  have h := reflection_log_10695_neg
  have he : Real.log (538643533123 / 250000000000) = -Real.log (250000000000 / 538643533123) := by
    rw [show ((538643533123 / 250000000000) : ℝ) = ((250000000000 / 538643533123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10696_neg : (384951707 / 500000000) ≤ -Real.log (125000000000 / 269944707741) ∧
    -Real.log (125000000000 / 269944707741) ≤ (96237927 / 125000000) := by
  have h := checkLog_sound (w := (19944707741 / 519944707741)) (n := 12)
    (lo := (38378117 / 500000000)) (hi := (15351247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269944707741 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269944707741 / 250000000000) = 1/(125000000000 / 269944707741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10696 : Bounds (384951707 / 500000000) (96237927 / 125000000) (Real.log (269944707741 / 125000000000)) := by
  have h := reflection_log_10696_neg
  have he : Real.log (269944707741 / 125000000000) = -Real.log (125000000000 / 269944707741) := by
    rw [show ((269944707741 / 125000000000) : ℝ) = ((125000000000 / 269944707741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10697_neg : (313349819 / 1000000000) ≤ -Real.log (125 / 171) ∧
    -Real.log (125 / 171) ≤ (15667491 / 50000000) := by
  have h := checkLog_sound (w := (23 / 148)) (n := 12)
    (lo := (313349819 / 1000000000)) (hi := (15667491 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171 / 125) = 1/(125 / 171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10697 : Bounds (313349819 / 1000000000) (15667491 / 50000000) (Real.log (171 / 125)) := by
  have h := reflection_log_10697_neg
  have he : Real.log (171 / 125) = -Real.log (125 / 171) := by
    rw [show ((171 / 125) : ℝ) = ((125 / 171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10698_neg : (114716471 / 250000000) ≤ -Real.log (79 / 125) ∧
    -Real.log (79 / 125) ≤ (91773177 / 200000000) := by
  have h := checkLog_sound (w := (23 / 102)) (n := 12)
    (lo := (114716471 / 250000000)) (hi := (91773177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 79) = 1/(79 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10698 : Bounds (-91773177 / 200000000) (-114716471 / 250000000) (Real.log (79 / 125)) := by
  have h := reflection_log_10698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10699_neg : (91983 / 250000000) ≤ -Real.log (62500 / 62523) ∧
    -Real.log (62500 / 62523) ≤ (367933 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 125023)) (n := 12)
    (lo := (91983 / 250000000)) (hi := (367933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62523 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62523 / 62500) = 1/(62500 / 62523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10699 : Bounds (91983 / 250000000) (367933 / 1000000000) (Real.log (62523 / 62500)) := by
  have h := reflection_log_10699_neg
  have he : Real.log (62523 / 62500) = -Real.log (62500 / 62523) := by
    rw [show ((62523 / 62500) : ℝ) = ((62500 / 62523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10700_neg : (368067 / 1000000000) ≤ -Real.log (62477 / 62500) ∧
    -Real.log (62477 / 62500) ≤ (92017 / 250000000) := by
  have h := checkLog_sound (w := (23 / 124977)) (n := 12)
    (lo := (368067 / 1000000000)) (hi := (92017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62477) = 1/(62477 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10700 : Bounds (-92017 / 250000000) (-368067 / 1000000000) (Real.log (62477 / 62500)) := by
  have h := reflection_log_10700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10701_neg : (172240917 / 1000000000) ≤ -Real.log (250000 / 296991) ∧
    -Real.log (250000 / 296991) ≤ (86120459 / 500000000) := by
  have h := checkLog_sound (w := (46991 / 546991)) (n := 12)
    (lo := (172240917 / 1000000000)) (hi := (86120459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296991 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296991 / 250000) = 1/(250000 / 296991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10701 : Bounds (172240917 / 1000000000) (86120459 / 500000000) (Real.log (296991 / 250000)) := by
  have h := reflection_log_10701_neg
  have he : Real.log (296991 / 250000) = -Real.log (250000 / 296991) := by
    rw [show ((296991 / 250000) : ℝ) = ((250000 / 296991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10702_neg : (52052651 / 250000000) ≤ -Real.log (203009 / 250000) ∧
    -Real.log (203009 / 250000) ≤ (41642121 / 200000000) := by
  have h := checkLog_sound (w := (46991 / 453009)) (n := 12)
    (lo := (52052651 / 250000000)) (hi := (41642121 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203009) = 1/(203009 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10702 : Bounds (-41642121 / 200000000) (-52052651 / 250000000) (Real.log (203009 / 250000)) := by
  have h := reflection_log_10702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10703_neg : (172996547 / 1000000000) ≤ -Real.log (500000 / 594431) ∧
    -Real.log (500000 / 594431) ≤ (43249137 / 250000000) := by
  have h := checkLog_sound (w := (94431 / 1094431)) (n := 12)
    (lo := (172996547 / 1000000000)) (hi := (43249137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594431 / 500000) = 1/(500000 / 594431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10703 : Bounds (172996547 / 1000000000) (43249137 / 250000000) (Real.log (594431 / 500000)) := by
  have h := reflection_log_10703_neg
  have he : Real.log (594431 / 500000) = -Real.log (500000 / 594431) := by
    rw [show ((594431 / 500000) : ℝ) = ((500000 / 594431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10704_neg : (209317079 / 1000000000) ≤ -Real.log (405569 / 500000) ∧
    -Real.log (405569 / 500000) ≤ (5232927 / 25000000) := by
  have h := checkLog_sound (w := (94431 / 905569)) (n := 12)
    (lo := (209317079 / 1000000000)) (hi := (5232927 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405569) = 1/(405569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10704 : Bounds (-5232927 / 25000000) (-209317079 / 1000000000) (Real.log (405569 / 500000)) := by
  have h := reflection_log_10704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10705_neg : (36320531 / 1000000000) ≤ -Real.log (241082786239 / 250000000000) ∧
    -Real.log (241082786239 / 250000000000) ≤ (9080133 / 250000000) := by
  have h := checkLog_sound (w := (8917213761 / 491082786239)) (n := 12)
    (lo := (36320531 / 1000000000)) (hi := (9080133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241082786239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241082786239) = 1/(241082786239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10705 : Bounds (-9080133 / 250000000) (-36320531 / 1000000000) (Real.log (241082786239 / 250000000000)) := by
  have h := reflection_log_10705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10706_neg : (35969687 / 1000000000) ≤ -Real.log (60291845919 / 62500000000) ∧
    -Real.log (60291845919 / 62500000000) ≤ (4496211 / 125000000) := by
  have h := checkLog_sound (w := (2208154081 / 122791845919)) (n := 12)
    (lo := (35969687 / 1000000000)) (hi := (4496211 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60291845919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60291845919) = 1/(60291845919 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10706 : Bounds (-4496211 / 125000000) (-35969687 / 1000000000) (Real.log (60291845919 / 62500000000)) := by
  have h := reflection_log_10706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10707_neg : (190225761 / 500000000) ≤ -Real.log (500000000000 / 731472496293) ∧
    -Real.log (500000000000 / 731472496293) ≤ (380451523 / 1000000000) := by
  have h := checkLog_sound (w := (231472496293 / 1231472496293)) (n := 12)
    (lo := (190225761 / 500000000)) (hi := (380451523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731472496293 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731472496293 / 500000000000) = 1/(500000000000 / 731472496293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10707 : Bounds (190225761 / 500000000) (380451523 / 1000000000) (Real.log (731472496293 / 500000000000)) := by
  have h := reflection_log_10707_neg
  have he : Real.log (731472496293 / 500000000000) = -Real.log (500000000000 / 731472496293) := by
    rw [show ((731472496293 / 500000000000) : ℝ) = ((500000000000 / 731472496293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10708_neg : (191156813 / 500000000) ≤ -Real.log (500000000000 / 732835842977) ∧
    -Real.log (500000000000 / 732835842977) ≤ (382313627 / 1000000000) := by
  have h := checkLog_sound (w := (232835842977 / 1232835842977)) (n := 12)
    (lo := (191156813 / 500000000)) (hi := (382313627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732835842977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732835842977 / 500000000000) = 1/(500000000000 / 732835842977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10708 : Bounds (191156813 / 500000000) (382313627 / 1000000000) (Real.log (732835842977 / 500000000000)) := by
  have h := reflection_log_10708_neg
  have he : Real.log (732835842977 / 500000000000) = -Real.log (500000000000 / 732835842977) := by
    rw [show ((732835842977 / 500000000000) : ℝ) = ((500000000000 / 732835842977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10709_neg : (384951707 / 500000000) ≤ -Real.log (500000000000 / 1079778830963) ∧
    -Real.log (500000000000 / 1079778830963) ≤ (96237927 / 125000000) := by
  have h := checkLog_sound (w := (79778830963 / 2079778830963)) (n := 12)
    (lo := (38378117 / 500000000)) (hi := (15351247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079778830963 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1079778830963 / 1000000000000) = 1/(500000000000 / 1079778830963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10709 : Bounds (384951707 / 500000000) (96237927 / 125000000) (Real.log (1079778830963 / 500000000000)) := by
  have h := reflection_log_10709_neg
  have he : Real.log (1079778830963 / 500000000000) = -Real.log (500000000000 / 1079778830963) := by
    rw [show ((1079778830963 / 500000000000) : ℝ) = ((500000000000 / 1079778830963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10710_neg : (772215703 / 1000000000) ≤ -Real.log (500000000000 / 1082278481013) ∧
    -Real.log (500000000000 / 1082278481013) ≤ (154443141 / 200000000) := by
  have h := checkLog_sound (w := (82278481013 / 2082278481013)) (n := 12)
    (lo := (79068523 / 1000000000)) (hi := (19767131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082278481013 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1082278481013 / 1000000000000) = 1/(500000000000 / 1082278481013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10710 : Bounds (772215703 / 1000000000) (154443141 / 200000000) (Real.log (1082278481013 / 500000000000)) := by
  have h := reflection_log_10710_neg
  have he : Real.log (1082278481013 / 500000000000) = -Real.log (500000000000 / 1082278481013) := by
    rw [show ((1082278481013 / 500000000000) : ℝ) = ((500000000000 / 1082278481013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10711_neg : (157040273 / 500000000) ≤ -Real.log (1000 / 1369) ∧
    -Real.log (1000 / 1369) ≤ (314080547 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 2369)) (n := 12)
    (lo := (157040273 / 500000000)) (hi := (314080547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1369 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1369 / 1000) = 1/(1000 / 1369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10711 : Bounds (157040273 / 500000000) (314080547 / 1000000000) (Real.log (1369 / 1000)) := by
  have h := reflection_log_10711_neg
  have he : Real.log (1369 / 1000) = -Real.log (1000 / 1369) := by
    rw [show ((1369 / 1000) : ℝ) = ((1000 / 1369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10712_neg : (57556177 / 125000000) ≤ -Real.log (631 / 1000) ∧
    -Real.log (631 / 1000) ≤ (460449417 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 1631)) (n := 12)
    (lo := (57556177 / 125000000)) (hi := (460449417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 631) = 1/(631 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10712 : Bounds (-460449417 / 1000000000) (-57556177 / 125000000) (Real.log (631 / 1000)) := by
  have h := reflection_log_10712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10713_neg : (368931 / 1000000000) ≤ -Real.log (1000000 / 1000369) ∧
    -Real.log (1000000 / 1000369) ≤ (92233 / 250000000) := by
  have h := checkLog_sound (w := (369 / 2000369)) (n := 12)
    (lo := (368931 / 1000000000)) (hi := (92233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000369 / 1000000) = 1/(1000000 / 1000369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10713 : Bounds (368931 / 1000000000) (92233 / 250000000) (Real.log (1000369 / 1000000)) := by
  have h := reflection_log_10713_neg
  have he : Real.log (1000369 / 1000000) = -Real.log (1000000 / 1000369) := by
    rw [show ((1000369 / 1000000) : ℝ) = ((1000000 / 1000369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10714_neg : (92267 / 250000000) ≤ -Real.log (999631 / 1000000) ∧
    -Real.log (999631 / 1000000) ≤ (369069 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 1999631)) (n := 12)
    (lo := (92267 / 250000000)) (hi := (369069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999631) = 1/(999631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10714 : Bounds (-369069 / 1000000000) (-92267 / 250000000) (Real.log (999631 / 1000000)) := by
  have h := reflection_log_10714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10715_neg : (43173633 / 250000000) ≤ -Real.log (1000000 / 1188503) ∧
    -Real.log (1000000 / 1188503) ≤ (172694533 / 1000000000) := by
  have h := checkLog_sound (w := (188503 / 2188503)) (n := 12)
    (lo := (43173633 / 250000000)) (hi := (172694533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188503 / 1000000) = 1/(1000000 / 1188503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10715 : Bounds (43173633 / 250000000) (172694533 / 1000000000) (Real.log (1188503 / 1000000)) := by
  have h := reflection_log_10715_neg
  have he : Real.log (1188503 / 1000000) = -Real.log (1000000 / 1188503) := by
    rw [show ((1188503 / 1000000) : ℝ) = ((1000000 / 1188503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10716_neg : (52218647 / 250000000) ≤ -Real.log (811497 / 1000000) ∧
    -Real.log (811497 / 1000000) ≤ (208874589 / 1000000000) := by
  have h := checkLog_sound (w := (188503 / 1811497)) (n := 12)
    (lo := (52218647 / 250000000)) (hi := (208874589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811497) = 1/(811497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10716 : Bounds (-208874589 / 1000000000) (-52218647 / 250000000) (Real.log (811497 / 1000000)) := by
  have h := reflection_log_10716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10717_neg : (173450659 / 1000000000) ≤ -Real.log (500000 / 594701) ∧
    -Real.log (500000 / 594701) ≤ (8672533 / 50000000) := by
  have h := checkLog_sound (w := (94701 / 1094701)) (n := 12)
    (lo := (173450659 / 1000000000)) (hi := (8672533 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594701 / 500000) = 1/(500000 / 594701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10717 : Bounds (173450659 / 1000000000) (8672533 / 50000000) (Real.log (594701 / 500000)) := by
  have h := reflection_log_10717_neg
  have he : Real.log (594701 / 500000) = -Real.log (500000 / 594701) := by
    rw [show ((594701 / 500000) : ℝ) = ((500000 / 594701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10718_neg : (26247879 / 125000000) ≤ -Real.log (405299 / 500000) ∧
    -Real.log (405299 / 500000) ≤ (209983033 / 1000000000) := by
  have h := checkLog_sound (w := (94701 / 905299)) (n := 12)
    (lo := (26247879 / 125000000)) (hi := (209983033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405299) = 1/(405299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10718 : Bounds (-209983033 / 1000000000) (-26247879 / 125000000) (Real.log (405299 / 500000)) := by
  have h := reflection_log_10718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10719_neg : (9133093 / 250000000) ≤ -Real.log (241031720599 / 250000000000) ∧
    -Real.log (241031720599 / 250000000000) ≤ (36532373 / 1000000000) := by
  have h := checkLog_sound (w := (8968279401 / 491031720599)) (n := 12)
    (lo := (9133093 / 250000000)) (hi := (36532373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241031720599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241031720599) = 1/(241031720599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10719 : Bounds (-36532373 / 1000000000) (-9133093 / 250000000) (Real.log (241031720599 / 250000000000)) := by
  have h := reflection_log_10719_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10720_neg : (4522507 / 125000000) ≤ -Real.log (964466618991 / 1000000000000) ∧
    -Real.log (964466618991 / 1000000000000) ≤ (36180057 / 1000000000) := by
  have h := checkLog_sound (w := (35533381009 / 1964466618991)) (n := 12)
    (lo := (4522507 / 125000000)) (hi := (36180057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964466618991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964466618991) = 1/(964466618991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10720 : Bounds (-36180057 / 1000000000) (-4522507 / 125000000) (Real.log (964466618991 / 1000000000000)) := by
  have h := reflection_log_10720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10721_neg : (2384807 / 6250000) ≤ -Real.log (62500000000 / 91536305741) ∧
    -Real.log (62500000000 / 91536305741) ≤ (381569121 / 1000000000) := by
  have h := checkLog_sound (w := (29036305741 / 154036305741)) (n := 12)
    (lo := (2384807 / 6250000)) (hi := (381569121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91536305741 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91536305741 / 62500000000) = 1/(62500000000 / 91536305741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10721 : Bounds (2384807 / 6250000) (381569121 / 1000000000) (Real.log (91536305741 / 62500000000)) := by
  have h := reflection_log_10721_neg
  have he : Real.log (91536305741 / 62500000000) = -Real.log (62500000000 / 91536305741) := by
    rw [show ((91536305741 / 62500000000) : ℝ) = ((62500000000 / 91536305741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10722_neg : (383433691 / 1000000000) ≤ -Real.log (62500000000 / 91707140901) ∧
    -Real.log (62500000000 / 91707140901) ≤ (95858423 / 250000000) := by
  have h := checkLog_sound (w := (29207140901 / 154207140901)) (n := 12)
    (lo := (383433691 / 1000000000)) (hi := (95858423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91707140901 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91707140901 / 62500000000) = 1/(62500000000 / 91707140901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10722 : Bounds (383433691 / 1000000000) (95858423 / 250000000) (Real.log (91707140901 / 62500000000)) := by
  have h := reflection_log_10722_neg
  have he : Real.log (91707140901 / 62500000000) = -Real.log (62500000000 / 91707140901) := by
    rw [show ((91707140901 / 62500000000) : ℝ) = ((62500000000 / 91707140901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10723_neg : (772215703 / 1000000000) ≤ -Real.log (125000000000 / 270569620253) ∧
    -Real.log (125000000000 / 270569620253) ≤ (154443141 / 200000000) := by
  have h := checkLog_sound (w := (20569620253 / 520569620253)) (n := 12)
    (lo := (79068523 / 1000000000)) (hi := (19767131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270569620253 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270569620253 / 250000000000) = 1/(125000000000 / 270569620253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10723 : Bounds (772215703 / 1000000000) (154443141 / 200000000) (Real.log (270569620253 / 125000000000)) := by
  have h := reflection_log_10723_neg
  have he : Real.log (270569620253 / 125000000000) = -Real.log (125000000000 / 270569620253) := by
    rw [show ((270569620253 / 125000000000) : ℝ) = ((125000000000 / 270569620253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10724_neg : (387264981 / 500000000) ≤ -Real.log (500000000000 / 1084786053883) ∧
    -Real.log (500000000000 / 1084786053883) ≤ (193632491 / 250000000) := by
  have h := checkLog_sound (w := (84786053883 / 2084786053883)) (n := 12)
    (lo := (40691391 / 500000000)) (hi := (81382783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084786053883 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1084786053883 / 1000000000000) = 1/(500000000000 / 1084786053883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10724 : Bounds (387264981 / 500000000) (193632491 / 250000000) (Real.log (1084786053883 / 500000000000)) := by
  have h := reflection_log_10724_neg
  have he : Real.log (1084786053883 / 500000000000) = -Real.log (500000000000 / 1084786053883) := by
    rw [show ((1084786053883 / 500000000000) : ℝ) = ((500000000000 / 1084786053883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10725_neg : (314810739 / 1000000000) ≤ -Real.log (100 / 137) ∧
    -Real.log (100 / 137) ≤ (15740537 / 50000000) := by
  have h := checkLog_sound (w := (37 / 237)) (n := 12)
    (lo := (314810739 / 1000000000)) (hi := (15740537 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137 / 100) = 1/(100 / 137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10725 : Bounds (314810739 / 1000000000) (15740537 / 50000000) (Real.log (137 / 100)) := by
  have h := reflection_log_10725_neg
  have he : Real.log (137 / 100) = -Real.log (100 / 137) := by
    rw [show ((137 / 100) : ℝ) = ((100 / 137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10726_neg : (462035459 / 1000000000) ≤ -Real.log (63 / 100) ∧
    -Real.log (63 / 100) ≤ (23101773 / 50000000) := by
  have h := checkLog_sound (w := (37 / 163)) (n := 12)
    (lo := (462035459 / 1000000000)) (hi := (23101773 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 63) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 63) = 1/(63 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10726 : Bounds (-23101773 / 50000000) (-462035459 / 1000000000) (Real.log (63 / 100)) := by
  have h := reflection_log_10726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10727_neg : (369931 / 1000000000) ≤ -Real.log (100000 / 100037) ∧
    -Real.log (100000 / 100037) ≤ (92483 / 250000000) := by
  have h := checkLog_sound (w := (37 / 200037)) (n := 12)
    (lo := (369931 / 1000000000)) (hi := (92483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100037 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100037 / 100000) = 1/(100000 / 100037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10727 : Bounds (369931 / 1000000000) (92483 / 250000000) (Real.log (100037 / 100000)) := by
  have h := reflection_log_10727_neg
  have he : Real.log (100037 / 100000) = -Real.log (100000 / 100037) := by
    rw [show ((100037 / 100000) : ℝ) = ((100000 / 100037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10728_neg : (92517 / 250000000) ≤ -Real.log (99963 / 100000) ∧
    -Real.log (99963 / 100000) ≤ (370069 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 199963)) (n := 12)
    (lo := (92517 / 250000000)) (hi := (370069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99963) = 1/(99963 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10728 : Bounds (-370069 / 1000000000) (-92517 / 250000000) (Real.log (99963 / 100000)) := by
  have h := reflection_log_10728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10729_neg : (8657397 / 50000000) ≤ -Real.log (500000 / 594521) ∧
    -Real.log (500000 / 594521) ≤ (173147941 / 1000000000) := by
  have h := checkLog_sound (w := (94521 / 1094521)) (n := 12)
    (lo := (8657397 / 50000000)) (hi := (173147941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594521 / 500000) = 1/(500000 / 594521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10729 : Bounds (8657397 / 50000000) (173147941 / 1000000000) (Real.log (594521 / 500000)) := by
  have h := reflection_log_10729_neg
  have he : Real.log (594521 / 500000) = -Real.log (500000 / 594521) := by
    rw [show ((594521 / 500000) : ℝ) = ((500000 / 594521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10730_neg : (104769507 / 500000000) ≤ -Real.log (405479 / 500000) ∧
    -Real.log (405479 / 500000) ≤ (41907803 / 200000000) := by
  have h := checkLog_sound (w := (94521 / 905479)) (n := 12)
    (lo := (104769507 / 500000000)) (hi := (41907803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405479) = 1/(405479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10730 : Bounds (-41907803 / 200000000) (-104769507 / 500000000) (Real.log (405479 / 500000)) := by
  have h := reflection_log_10730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10731_neg : (86952283 / 500000000) ≤ -Real.log (500000 / 594971) ∧
    -Real.log (500000 / 594971) ≤ (173904567 / 1000000000) := by
  have h := checkLog_sound (w := (94971 / 1094971)) (n := 12)
    (lo := (86952283 / 500000000)) (hi := (173904567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594971 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594971 / 500000) = 1/(500000 / 594971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10731 : Bounds (86952283 / 500000000) (173904567 / 1000000000) (Real.log (594971 / 500000)) := by
  have h := reflection_log_10731_neg
  have he : Real.log (594971 / 500000) = -Real.log (500000 / 594971) := by
    rw [show ((594971 / 500000) : ℝ) = ((500000 / 594971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10732_neg : (52662357 / 250000000) ≤ -Real.log (405029 / 500000) ∧
    -Real.log (405029 / 500000) ≤ (210649429 / 1000000000) := by
  have h := checkLog_sound (w := (94971 / 905029)) (n := 12)
    (lo := (52662357 / 250000000)) (hi := (210649429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405029) = 1/(405029 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10732 : Bounds (-210649429 / 1000000000) (-52662357 / 250000000) (Real.log (405029 / 500000)) := by
  have h := reflection_log_10732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10733_neg : (18372431 / 500000000) ≤ -Real.log (240980509159 / 250000000000) ∧
    -Real.log (240980509159 / 250000000000) ≤ (36744863 / 1000000000) := by
  have h := checkLog_sound (w := (9019490841 / 490980509159)) (n := 12)
    (lo := (18372431 / 500000000)) (hi := (36744863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240980509159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240980509159) = 1/(240980509159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10733 : Bounds (-36744863 / 1000000000) (-18372431 / 500000000) (Real.log (240980509159 / 250000000000)) := by
  have h := reflection_log_10733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10734_neg : (36391073 / 1000000000) ≤ -Real.log (241065780559 / 250000000000) ∧
    -Real.log (241065780559 / 250000000000) ≤ (18195537 / 500000000) := by
  have h := checkLog_sound (w := (8934219441 / 491065780559)) (n := 12)
    (lo := (36391073 / 1000000000)) (hi := (18195537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241065780559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241065780559) = 1/(241065780559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10734 : Bounds (-18195537 / 500000000) (-36391073 / 1000000000) (Real.log (241065780559 / 250000000000)) := by
  have h := reflection_log_10734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10735_neg : (76537391 / 200000000) ≤ -Real.log (250000000000 / 366554741429) ∧
    -Real.log (250000000000 / 366554741429) ≤ (95671739 / 250000000) := by
  have h := checkLog_sound (w := (116554741429 / 616554741429)) (n := 12)
    (lo := (76537391 / 200000000)) (hi := (95671739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366554741429 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366554741429 / 250000000000) = 1/(250000000000 / 366554741429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10735 : Bounds (76537391 / 200000000) (95671739 / 250000000) (Real.log (366554741429 / 250000000000)) := by
  have h := reflection_log_10735_neg
  have he : Real.log (366554741429 / 250000000000) = -Real.log (250000000000 / 366554741429) := by
    rw [show ((366554741429 / 250000000000) : ℝ) = ((250000000000 / 366554741429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10736_neg : (76910799 / 200000000) ≤ -Real.log (250000000000 / 367239753203) ∧
    -Real.log (250000000000 / 367239753203) ≤ (96138499 / 250000000) := by
  have h := checkLog_sound (w := (117239753203 / 617239753203)) (n := 12)
    (lo := (76910799 / 200000000)) (hi := (96138499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367239753203 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367239753203 / 250000000000) = 1/(250000000000 / 367239753203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10736 : Bounds (76910799 / 200000000) (96138499 / 250000000) (Real.log (367239753203 / 250000000000)) := by
  have h := reflection_log_10736_neg
  have he : Real.log (367239753203 / 250000000000) = -Real.log (250000000000 / 367239753203) := by
    rw [show ((367239753203 / 250000000000) : ℝ) = ((250000000000 / 367239753203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10737_neg : (387264981 / 500000000) ≤ -Real.log (250000000000 / 542393026941) ∧
    -Real.log (250000000000 / 542393026941) ≤ (193632491 / 250000000) := by
  have h := checkLog_sound (w := (42393026941 / 1042393026941)) (n := 12)
    (lo := (40691391 / 500000000)) (hi := (81382783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542393026941 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(542393026941 / 500000000000) = 1/(250000000000 / 542393026941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10737 : Bounds (387264981 / 500000000) (193632491 / 250000000) (Real.log (542393026941 / 250000000000)) := by
  have h := reflection_log_10737_neg
  have he : Real.log (542393026941 / 250000000000) = -Real.log (250000000000 / 542393026941) := by
    rw [show ((542393026941 / 250000000000) : ℝ) = ((250000000000 / 542393026941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10738_neg : (388423099 / 500000000) ≤ -Real.log (250000000000 / 543650793651) ∧
    -Real.log (250000000000 / 543650793651) ≤ (3884231 / 5000000) := by
  have h := checkLog_sound (w := (43650793651 / 1043650793651)) (n := 12)
    (lo := (41849509 / 500000000)) (hi := (83699019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543650793651 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(543650793651 / 500000000000) = 1/(250000000000 / 543650793651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10738 : Bounds (388423099 / 500000000) (3884231 / 5000000) (Real.log (543650793651 / 250000000000)) := by
  have h := reflection_log_10738_neg
  have he : Real.log (543650793651 / 250000000000) = -Real.log (250000000000 / 543650793651) := by
    rw [show ((543650793651 / 250000000000) : ℝ) = ((250000000000 / 543650793651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10739_neg : (788851 / 2500000) ≤ -Real.log (1000 / 1371) ∧
    -Real.log (1000 / 1371) ≤ (315540401 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 2371)) (n := 12)
    (lo := (788851 / 2500000)) (hi := (315540401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1371 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1371 / 1000) = 1/(1000 / 1371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10739 : Bounds (788851 / 2500000) (315540401 / 1000000000) (Real.log (1371 / 1000)) := by
  have h := reflection_log_10739_neg
  have he : Real.log (1371 / 1000) = -Real.log (1000 / 1371) := by
    rw [show ((1371 / 1000) : ℝ) = ((1000 / 1371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10740_neg : (231812011 / 500000000) ≤ -Real.log (629 / 1000) ∧
    -Real.log (629 / 1000) ≤ (463624023 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 1629)) (n := 12)
    (lo := (231812011 / 500000000)) (hi := (463624023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 629) = 1/(629 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10740 : Bounds (-463624023 / 1000000000) (-231812011 / 500000000) (Real.log (629 / 1000)) := by
  have h := reflection_log_10740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10741_neg : (370931 / 1000000000) ≤ -Real.log (1000000 / 1000371) ∧
    -Real.log (1000000 / 1000371) ≤ (92733 / 250000000) := by
  have h := checkLog_sound (w := (371 / 2000371)) (n := 12)
    (lo := (370931 / 1000000000)) (hi := (92733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000371 / 1000000) = 1/(1000000 / 1000371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10741 : Bounds (370931 / 1000000000) (92733 / 250000000) (Real.log (1000371 / 1000000)) := by
  have h := reflection_log_10741_neg
  have he : Real.log (1000371 / 1000000) = -Real.log (1000000 / 1000371) := by
    rw [show ((1000371 / 1000000) : ℝ) = ((1000000 / 1000371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10742_neg : (92767 / 250000000) ≤ -Real.log (999629 / 1000000) ∧
    -Real.log (999629 / 1000000) ≤ (371069 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 1999629)) (n := 12)
    (lo := (92767 / 250000000)) (hi := (371069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999629) = 1/(999629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10742 : Bounds (-371069 / 1000000000) (-92767 / 250000000) (Real.log (999629 / 1000000)) := by
  have h := reflection_log_10742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10743_neg : (21700143 / 125000000) ≤ -Real.log (1000000 / 1189581) ∧
    -Real.log (1000000 / 1189581) ≤ (34720229 / 200000000) := by
  have h := checkLog_sound (w := (189581 / 2189581)) (n := 12)
    (lo := (21700143 / 125000000)) (hi := (34720229 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189581 / 1000000) = 1/(1000000 / 1189581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10743 : Bounds (21700143 / 125000000) (34720229 / 200000000) (Real.log (1189581 / 1000000)) := by
  have h := reflection_log_10743_neg
  have he : Real.log (1189581 / 1000000) = -Real.log (1000000 / 1189581) := by
    rw [show ((1189581 / 1000000) : ℝ) = ((1000000 / 1189581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10744_neg : (210203881 / 1000000000) ≤ -Real.log (810419 / 1000000) ∧
    -Real.log (810419 / 1000000) ≤ (105101941 / 500000000) := by
  have h := checkLog_sound (w := (189581 / 1810419)) (n := 12)
    (lo := (210203881 / 1000000000)) (hi := (105101941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810419) = 1/(810419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10744 : Bounds (-105101941 / 500000000) (-210203881 / 1000000000) (Real.log (810419 / 1000000)) := by
  have h := reflection_log_10744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10745_neg : (174358267 / 1000000000) ≤ -Real.log (500000 / 595241) ∧
    -Real.log (500000 / 595241) ≤ (43589567 / 250000000) := by
  have h := checkLog_sound (w := (95241 / 1095241)) (n := 12)
    (lo := (174358267 / 1000000000)) (hi := (43589567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595241 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595241 / 500000) = 1/(500000 / 595241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10745 : Bounds (174358267 / 1000000000) (43589567 / 250000000) (Real.log (595241 / 500000)) := by
  have h := reflection_log_10745_neg
  have he : Real.log (595241 / 500000) = -Real.log (500000 / 595241) := by
    rw [show ((595241 / 500000) : ℝ) = ((500000 / 595241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10746_neg : (21131627 / 100000000) ≤ -Real.log (404759 / 500000) ∧
    -Real.log (404759 / 500000) ≤ (211316271 / 1000000000) := by
  have h := checkLog_sound (w := (95241 / 904759)) (n := 12)
    (lo := (21131627 / 100000000)) (hi := (211316271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404759) = 1/(404759 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10746 : Bounds (-211316271 / 1000000000) (-21131627 / 100000000) (Real.log (404759 / 500000)) := by
  have h := reflection_log_10746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10747_neg : (36958003 / 1000000000) ≤ -Real.log (240929151919 / 250000000000) ∧
    -Real.log (240929151919 / 250000000000) ≤ (9239501 / 250000000) := by
  have h := checkLog_sound (w := (9070848081 / 490929151919)) (n := 12)
    (lo := (36958003 / 1000000000)) (hi := (9239501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240929151919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240929151919) = 1/(240929151919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10747 : Bounds (-9239501 / 250000000) (-36958003 / 1000000000) (Real.log (240929151919 / 250000000000)) := by
  have h := reflection_log_10747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10748_neg : (2287671 / 62500000) ≤ -Real.log (964059044439 / 1000000000000) ∧
    -Real.log (964059044439 / 1000000000000) ≤ (36602737 / 1000000000) := by
  have h := checkLog_sound (w := (35940955561 / 1964059044439)) (n := 12)
    (lo := (2287671 / 62500000)) (hi := (36602737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964059044439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964059044439) = 1/(964059044439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10748 : Bounds (-36602737 / 1000000000) (-2287671 / 62500000) (Real.log (964059044439 / 1000000000000)) := by
  have h := reflection_log_10748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10749_neg : (15352201 / 40000000) ≤ -Real.log (500000000000 / 733929609251) ∧
    -Real.log (500000000000 / 733929609251) ≤ (191902513 / 500000000) := by
  have h := checkLog_sound (w := (233929609251 / 1233929609251)) (n := 12)
    (lo := (15352201 / 40000000)) (hi := (191902513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733929609251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733929609251 / 500000000000) = 1/(500000000000 / 733929609251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10749 : Bounds (15352201 / 40000000) (191902513 / 500000000) (Real.log (733929609251 / 500000000000)) := by
  have h := reflection_log_10749_neg
  have he : Real.log (733929609251 / 500000000000) = -Real.log (500000000000 / 733929609251) := by
    rw [show ((733929609251 / 500000000000) : ℝ) = ((500000000000 / 733929609251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10750_neg : (385674537 / 1000000000) ≤ -Real.log (500000000000 / 735302982763) ∧
    -Real.log (500000000000 / 735302982763) ≤ (192837269 / 500000000) := by
  have h := checkLog_sound (w := (235302982763 / 1235302982763)) (n := 12)
    (lo := (385674537 / 1000000000)) (hi := (192837269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735302982763 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735302982763 / 500000000000) = 1/(500000000000 / 735302982763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10750 : Bounds (385674537 / 1000000000) (192837269 / 500000000) (Real.log (735302982763 / 500000000000)) := by
  have h := reflection_log_10750_neg
  have he : Real.log (735302982763 / 500000000000) = -Real.log (500000000000 / 735302982763) := by
    rw [show ((735302982763 / 500000000000) : ℝ) = ((500000000000 / 735302982763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10751_neg : (388423099 / 500000000) ≤ -Real.log (500000000000 / 1087301587301) ∧
    -Real.log (500000000000 / 1087301587301) ≤ (3884231 / 5000000) := by
  have h := checkLog_sound (w := (87301587301 / 2087301587301)) (n := 12)
    (lo := (41849509 / 500000000)) (hi := (83699019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087301587301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1087301587301 / 1000000000000) = 1/(500000000000 / 1087301587301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10751 : Bounds (388423099 / 500000000) (3884231 / 5000000) (Real.log (1087301587301 / 500000000000)) := by
  have h := reflection_log_10751_neg
  have he : Real.log (1087301587301 / 500000000000) = -Real.log (500000000000 / 1087301587301) := by
    rw [show ((1087301587301 / 500000000000) : ℝ) = ((500000000000 / 1087301587301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0168 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10752_neg : (389582211 / 500000000) ≤ -Real.log (500000000000 / 1089825119237) ∧
    -Real.log (500000000000 / 1089825119237) ≤ (97395553 / 125000000) := by
  have h := checkLog_sound (w := (89825119237 / 2089825119237)) (n := 12)
    (lo := (43008621 / 500000000)) (hi := (86017243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089825119237 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1089825119237 / 1000000000000) = 1/(500000000000 / 1089825119237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10752 : Bounds (389582211 / 500000000) (97395553 / 125000000) (Real.log (1089825119237 / 500000000000)) := by
  have h := reflection_log_10752_neg
  have he : Real.log (1089825119237 / 500000000000) = -Real.log (500000000000 / 1089825119237) := by
    rw [show ((1089825119237 / 500000000000) : ℝ) = ((500000000000 / 1089825119237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10753_neg : (316269529 / 1000000000) ≤ -Real.log (250 / 343) ∧
    -Real.log (250 / 343) ≤ (31626953 / 100000000) := by
  have h := checkLog_sound (w := (93 / 593)) (n := 12)
    (lo := (316269529 / 1000000000)) (hi := (31626953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343 / 250) = 1/(250 / 343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10753 : Bounds (316269529 / 1000000000) (31626953 / 100000000) (Real.log (343 / 250)) := by
  have h := reflection_log_10753_neg
  have he : Real.log (343 / 250) = -Real.log (250 / 343) := by
    rw [show ((343 / 250) : ℝ) = ((250 / 343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10754_neg : (58151889 / 125000000) ≤ -Real.log (157 / 250) ∧
    -Real.log (157 / 250) ≤ (465215113 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 407)) (n := 12)
    (lo := (58151889 / 125000000)) (hi := (465215113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 157) = 1/(157 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10754 : Bounds (-465215113 / 1000000000) (-58151889 / 125000000) (Real.log (157 / 250)) := by
  have h := reflection_log_10754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10755_neg : (37193 / 100000000) ≤ -Real.log (250000 / 250093) ∧
    -Real.log (250000 / 250093) ≤ (371931 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 500093)) (n := 12)
    (lo := (37193 / 100000000)) (hi := (371931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250093 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250093 / 250000) = 1/(250000 / 250093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10755 : Bounds (37193 / 100000000) (371931 / 1000000000) (Real.log (250093 / 250000)) := by
  have h := reflection_log_10755_neg
  have he : Real.log (250093 / 250000) = -Real.log (250000 / 250093) := by
    rw [show ((250093 / 250000) : ℝ) = ((250000 / 250093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10756_neg : (372069 / 1000000000) ≤ -Real.log (249907 / 250000) ∧
    -Real.log (249907 / 250000) ≤ (37207 / 100000000) := by
  have h := checkLog_sound (w := (93 / 499907)) (n := 12)
    (lo := (372069 / 1000000000)) (hi := (37207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249907) = 1/(249907 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10756 : Bounds (-37207 / 100000000) (-372069 / 1000000000) (Real.log (249907 / 250000)) := by
  have h := reflection_log_10756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10757_neg : (87027071 / 500000000) ≤ -Real.log (25000 / 29753) ∧
    -Real.log (25000 / 29753) ≤ (174054143 / 1000000000) := by
  have h := checkLog_sound (w := (4753 / 54753)) (n := 12)
    (lo := (87027071 / 500000000)) (hi := (174054143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29753 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29753 / 25000) = 1/(25000 / 29753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10757 : Bounds (87027071 / 500000000) (174054143 / 1000000000) (Real.log (29753 / 25000)) := by
  have h := reflection_log_10757_neg
  have he : Real.log (29753 / 25000) = -Real.log (25000 / 29753) := by
    rw [show ((29753 / 25000) : ℝ) = ((25000 / 29753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10758_neg : (21086919 / 100000000) ≤ -Real.log (20247 / 25000) ∧
    -Real.log (20247 / 25000) ≤ (210869191 / 1000000000) := by
  have h := checkLog_sound (w := (4753 / 45247)) (n := 12)
    (lo := (21086919 / 100000000)) (hi := (210869191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20247) = 1/(20247 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10758 : Bounds (-210869191 / 1000000000) (-21086919 / 100000000) (Real.log (20247 / 25000)) := by
  have h := reflection_log_10758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10759_neg : (174812601 / 1000000000) ≤ -Real.log (1000000 / 1191023) ∧
    -Real.log (1000000 / 1191023) ≤ (87406301 / 500000000) := by
  have h := checkLog_sound (w := (191023 / 2191023)) (n := 12)
    (lo := (174812601 / 1000000000)) (hi := (87406301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191023 / 1000000) = 1/(1000000 / 1191023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10759 : Bounds (174812601 / 1000000000) (87406301 / 500000000) (Real.log (1191023 / 1000000)) := by
  have h := reflection_log_10759_neg
  have he : Real.log (1191023 / 1000000) = -Real.log (1000000 / 1191023) := by
    rw [show ((1191023 / 1000000) : ℝ) = ((1000000 / 1191023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10760_neg : (26498099 / 125000000) ≤ -Real.log (808977 / 1000000) ∧
    -Real.log (808977 / 1000000) ≤ (211984793 / 1000000000) := by
  have h := checkLog_sound (w := (191023 / 1808977)) (n := 12)
    (lo := (26498099 / 125000000)) (hi := (211984793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808977) = 1/(808977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10760 : Bounds (-211984793 / 1000000000) (-26498099 / 125000000) (Real.log (808977 / 1000000)) := by
  have h := reflection_log_10760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10761_neg : (3717219 / 100000000) ≤ -Real.log (963510213471 / 1000000000000) ∧
    -Real.log (963510213471 / 1000000000000) ≤ (37172191 / 1000000000) := by
  have h := checkLog_sound (w := (36489786529 / 1963510213471)) (n := 12)
    (lo := (3717219 / 100000000)) (hi := (37172191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963510213471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963510213471) = 1/(963510213471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10761 : Bounds (-37172191 / 1000000000) (-3717219 / 100000000) (Real.log (963510213471 / 1000000000000)) := by
  have h := reflection_log_10761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10762_neg : (4601881 / 125000000) ≤ -Real.log (602408991 / 625000000) ∧
    -Real.log (602408991 / 625000000) ≤ (36815049 / 1000000000) := by
  have h := checkLog_sound (w := (22591009 / 1227408991)) (n := 12)
    (lo := (4601881 / 125000000)) (hi := (36815049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 602408991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 602408991) = 1/(602408991 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10762 : Bounds (-36815049 / 1000000000) (-4601881 / 125000000) (Real.log (602408991 / 625000000)) := by
  have h := reflection_log_10762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10763_neg : (96230833 / 250000000) ≤ -Real.log (500000000000 / 734750827283) ∧
    -Real.log (500000000000 / 734750827283) ≤ (384923333 / 1000000000) := by
  have h := checkLog_sound (w := (234750827283 / 1234750827283)) (n := 12)
    (lo := (96230833 / 250000000)) (hi := (384923333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734750827283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734750827283 / 500000000000) = 1/(500000000000 / 734750827283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10763 : Bounds (96230833 / 250000000) (384923333 / 1000000000) (Real.log (734750827283 / 500000000000)) := by
  have h := reflection_log_10763_neg
  have he : Real.log (734750827283 / 500000000000) = -Real.log (500000000000 / 734750827283) := by
    rw [show ((734750827283 / 500000000000) : ℝ) = ((500000000000 / 734750827283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10764_neg : (193398697 / 500000000) ≤ -Real.log (500000000000 / 736129086489) ∧
    -Real.log (500000000000 / 736129086489) ≤ (77359479 / 200000000) := by
  have h := checkLog_sound (w := (236129086489 / 1236129086489)) (n := 12)
    (lo := (193398697 / 500000000)) (hi := (77359479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736129086489 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736129086489 / 500000000000) = 1/(500000000000 / 736129086489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10764 : Bounds (193398697 / 500000000) (77359479 / 200000000) (Real.log (736129086489 / 500000000000)) := by
  have h := reflection_log_10764_neg
  have he : Real.log (736129086489 / 500000000000) = -Real.log (500000000000 / 736129086489) := by
    rw [show ((736129086489 / 500000000000) : ℝ) = ((500000000000 / 736129086489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10765_neg : (389582211 / 500000000) ≤ -Real.log (125000000000 / 272456279809) ∧
    -Real.log (125000000000 / 272456279809) ≤ (97395553 / 125000000) := by
  have h := checkLog_sound (w := (22456279809 / 522456279809)) (n := 12)
    (lo := (43008621 / 500000000)) (hi := (86017243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272456279809 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272456279809 / 250000000000) = 1/(125000000000 / 272456279809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10765 : Bounds (389582211 / 500000000) (97395553 / 125000000) (Real.log (272456279809 / 125000000000)) := by
  have h := reflection_log_10765_neg
  have he : Real.log (272456279809 / 125000000000) = -Real.log (125000000000 / 272456279809) := by
    rw [show ((272456279809 / 125000000000) : ℝ) = ((125000000000 / 272456279809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10766_neg : (781484641 / 1000000000) ≤ -Real.log (500000000000 / 1092356687899) ∧
    -Real.log (500000000000 / 1092356687899) ≤ (781484643 / 1000000000) := by
  have h := checkLog_sound (w := (92356687899 / 2092356687899)) (n := 12)
    (lo := (88337461 / 1000000000)) (hi := (44168731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092356687899 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1092356687899 / 1000000000000) = 1/(500000000000 / 1092356687899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10766 : Bounds (781484641 / 1000000000) (781484643 / 1000000000) (Real.log (1092356687899 / 500000000000)) := by
  have h := reflection_log_10766_neg
  have he : Real.log (1092356687899 / 500000000000) = -Real.log (500000000000 / 1092356687899) := by
    rw [show ((1092356687899 / 500000000000) : ℝ) = ((500000000000 / 1092356687899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10767_neg : (158499063 / 500000000) ≤ -Real.log (1000 / 1373) ∧
    -Real.log (1000 / 1373) ≤ (316998127 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2373)) (n := 12)
    (lo := (158499063 / 500000000)) (hi := (316998127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1373 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1373 / 1000) = 1/(1000 / 1373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10767 : Bounds (158499063 / 500000000) (316998127 / 1000000000) (Real.log (1373 / 1000)) := by
  have h := reflection_log_10767_neg
  have he : Real.log (1373 / 1000) = -Real.log (1000 / 1373) := by
    rw [show ((1373 / 1000) : ℝ) = ((1000 / 1373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10768_neg : (233404369 / 500000000) ≤ -Real.log (627 / 1000) ∧
    -Real.log (627 / 1000) ≤ (466808739 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 1627)) (n := 12)
    (lo := (233404369 / 500000000)) (hi := (466808739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 627) = 1/(627 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10768 : Bounds (-466808739 / 1000000000) (-233404369 / 500000000) (Real.log (627 / 1000)) := by
  have h := reflection_log_10768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10769_neg : (37293 / 100000000) ≤ -Real.log (1000000 / 1000373) ∧
    -Real.log (1000000 / 1000373) ≤ (372931 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2000373)) (n := 12)
    (lo := (37293 / 100000000)) (hi := (372931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000373 / 1000000) = 1/(1000000 / 1000373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10769 : Bounds (37293 / 100000000) (372931 / 1000000000) (Real.log (1000373 / 1000000)) := by
  have h := reflection_log_10769_neg
  have he : Real.log (1000373 / 1000000) = -Real.log (1000000 / 1000373) := by
    rw [show ((1000373 / 1000000) : ℝ) = ((1000000 / 1000373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10770_neg : (373069 / 1000000000) ≤ -Real.log (999627 / 1000000) ∧
    -Real.log (999627 / 1000000) ≤ (37307 / 100000000) := by
  have h := checkLog_sound (w := (373 / 1999627)) (n := 12)
    (lo := (373069 / 1000000000)) (hi := (37307 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999627) = 1/(999627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10770 : Bounds (-37307 / 100000000) (-373069 / 1000000000) (Real.log (999627 / 1000000)) := by
  have h := reflection_log_10770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10771_neg : (6980311 / 40000000) ≤ -Real.log (50000 / 59533) ∧
    -Real.log (50000 / 59533) ≤ (681671 / 3906250) := by
  have h := checkLog_sound (w := (9533 / 109533)) (n := 12)
    (lo := (6980311 / 40000000)) (hi := (681671 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59533 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59533 / 50000) = 1/(50000 / 59533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10771 : Bounds (6980311 / 40000000) (681671 / 3906250) (Real.log (59533 / 50000)) := by
  have h := reflection_log_10771_neg
  have he : Real.log (59533 / 50000) = -Real.log (50000 / 59533) := by
    rw [show ((59533 / 50000) : ℝ) = ((50000 / 59533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10772_neg : (105768089 / 500000000) ≤ -Real.log (40467 / 50000) ∧
    -Real.log (40467 / 50000) ≤ (211536179 / 1000000000) := by
  have h := checkLog_sound (w := (9533 / 90467)) (n := 12)
    (lo := (105768089 / 500000000)) (hi := (211536179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40467) = 1/(40467 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10772 : Bounds (-211536179 / 1000000000) (-105768089 / 500000000) (Real.log (40467 / 50000)) := by
  have h := reflection_log_10772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10773_neg : (175266729 / 1000000000) ≤ -Real.log (250000 / 297891) ∧
    -Real.log (250000 / 297891) ≤ (17526673 / 100000000) := by
  have h := checkLog_sound (w := (47891 / 547891)) (n := 12)
    (lo := (175266729 / 1000000000)) (hi := (17526673 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297891 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297891 / 250000) = 1/(250000 / 297891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10773 : Bounds (175266729 / 1000000000) (17526673 / 100000000) (Real.log (297891 / 250000)) := by
  have h := reflection_log_10773_neg
  have he : Real.log (297891 / 250000) = -Real.log (250000 / 297891) := by
    rw [show ((297891 / 250000) : ℝ) = ((250000 / 297891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10774_neg : (106326881 / 500000000) ≤ -Real.log (202109 / 250000) ∧
    -Real.log (202109 / 250000) ≤ (212653763 / 1000000000) := by
  have h := checkLog_sound (w := (47891 / 452109)) (n := 12)
    (lo := (106326881 / 500000000)) (hi := (212653763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202109) = 1/(202109 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10774 : Bounds (-212653763 / 1000000000) (-106326881 / 500000000) (Real.log (202109 / 250000)) := by
  have h := reflection_log_10774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10775_neg : (4673379 / 125000000) ≤ -Real.log (60206452119 / 62500000000) ∧
    -Real.log (60206452119 / 62500000000) ≤ (37387033 / 1000000000) := by
  have h := checkLog_sound (w := (2293547881 / 122706452119)) (n := 12)
    (lo := (4673379 / 125000000)) (hi := (37387033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60206452119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60206452119) = 1/(60206452119 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10775 : Bounds (-37387033 / 1000000000) (-4673379 / 125000000) (Real.log (60206452119 / 62500000000)) := by
  have h := reflection_log_10775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10776_neg : (37028403 / 1000000000) ≤ -Real.log (2409121911 / 2500000000) ∧
    -Real.log (2409121911 / 2500000000) ≤ (9257101 / 250000000) := by
  have h := checkLog_sound (w := (90878089 / 4909121911)) (n := 12)
    (lo := (37028403 / 1000000000)) (hi := (9257101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2409121911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2409121911) = 1/(2409121911 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10776 : Bounds (-9257101 / 250000000) (-37028403 / 1000000000) (Real.log (2409121911 / 2500000000)) := by
  have h := reflection_log_10776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10777_neg : (386043953 / 1000000000) ≤ -Real.log (500000000000 / 735574665777) ∧
    -Real.log (500000000000 / 735574665777) ≤ (193021977 / 500000000) := by
  have h := checkLog_sound (w := (235574665777 / 1235574665777)) (n := 12)
    (lo := (386043953 / 1000000000)) (hi := (193021977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735574665777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735574665777 / 500000000000) = 1/(500000000000 / 735574665777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10777 : Bounds (386043953 / 1000000000) (193021977 / 500000000) (Real.log (735574665777 / 500000000000)) := by
  have h := reflection_log_10777_neg
  have he : Real.log (735574665777 / 500000000000) = -Real.log (500000000000 / 735574665777) := by
    rw [show ((735574665777 / 500000000000) : ℝ) = ((500000000000 / 735574665777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10778_neg : (387920491 / 1000000000) ≤ -Real.log (500000000000 / 736956295861) ∧
    -Real.log (500000000000 / 736956295861) ≤ (96980123 / 250000000) := by
  have h := checkLog_sound (w := (236956295861 / 1236956295861)) (n := 12)
    (lo := (387920491 / 1000000000)) (hi := (96980123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736956295861 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736956295861 / 500000000000) = 1/(500000000000 / 736956295861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10778 : Bounds (387920491 / 1000000000) (96980123 / 250000000) (Real.log (736956295861 / 500000000000)) := by
  have h := reflection_log_10778_neg
  have he : Real.log (736956295861 / 500000000000) = -Real.log (500000000000 / 736956295861) := by
    rw [show ((736956295861 / 500000000000) : ℝ) = ((500000000000 / 736956295861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10779_neg : (781484641 / 1000000000) ≤ -Real.log (250000000000 / 546178343949) ∧
    -Real.log (250000000000 / 546178343949) ≤ (781484643 / 1000000000) := by
  have h := checkLog_sound (w := (46178343949 / 1046178343949)) (n := 12)
    (lo := (88337461 / 1000000000)) (hi := (44168731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546178343949 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(546178343949 / 500000000000) = 1/(250000000000 / 546178343949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10779 : Bounds (781484641 / 1000000000) (781484643 / 1000000000) (Real.log (546178343949 / 250000000000)) := by
  have h := reflection_log_10779_neg
  have he : Real.log (546178343949 / 250000000000) = -Real.log (250000000000 / 546178343949) := by
    rw [show ((546178343949 / 250000000000) : ℝ) = ((250000000000 / 546178343949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10780_neg : (48987929 / 62500000) ≤ -Real.log (500000000000 / 1094896331739) ∧
    -Real.log (500000000000 / 1094896331739) ≤ (391903433 / 500000000) := by
  have h := checkLog_sound (w := (94896331739 / 2094896331739)) (n := 12)
    (lo := (22664921 / 250000000)) (hi := (18131937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094896331739 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1094896331739 / 1000000000000) = 1/(500000000000 / 1094896331739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10780 : Bounds (48987929 / 62500000) (391903433 / 500000000) (Real.log (1094896331739 / 500000000000)) := by
  have h := reflection_log_10780_neg
  have he : Real.log (1094896331739 / 500000000000) = -Real.log (500000000000 / 1094896331739) := by
    rw [show ((1094896331739 / 500000000000) : ℝ) = ((500000000000 / 1094896331739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10781_neg : (317726193 / 1000000000) ≤ -Real.log (500 / 687) ∧
    -Real.log (500 / 687) ≤ (158863097 / 500000000) := by
  have h := checkLog_sound (w := (187 / 1187)) (n := 12)
    (lo := (317726193 / 1000000000)) (hi := (158863097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687 / 500) = 1/(500 / 687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10781 : Bounds (317726193 / 1000000000) (158863097 / 500000000) (Real.log (687 / 500)) := by
  have h := reflection_log_10781_neg
  have he : Real.log (687 / 500) = -Real.log (500 / 687) := by
    rw [show ((687 / 500) : ℝ) = ((500 / 687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10782_neg : (468404907 / 1000000000) ≤ -Real.log (313 / 500) ∧
    -Real.log (313 / 500) ≤ (117101227 / 250000000) := by
  have h := checkLog_sound (w := (187 / 813)) (n := 12)
    (lo := (468404907 / 1000000000)) (hi := (117101227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 313) = 1/(313 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10782 : Bounds (-117101227 / 250000000) (-468404907 / 1000000000) (Real.log (313 / 500)) := by
  have h := reflection_log_10782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10783_neg : (37393 / 100000000) ≤ -Real.log (500000 / 500187) ∧
    -Real.log (500000 / 500187) ≤ (373931 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1000187)) (n := 12)
    (lo := (37393 / 100000000)) (hi := (373931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500187 / 500000) = 1/(500000 / 500187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10783 : Bounds (37393 / 100000000) (373931 / 1000000000) (Real.log (500187 / 500000)) := by
  have h := reflection_log_10783_neg
  have he : Real.log (500187 / 500000) = -Real.log (500000 / 500187) := by
    rw [show ((500187 / 500000) : ℝ) = ((500000 / 500187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10784_neg : (374069 / 1000000000) ≤ -Real.log (499813 / 500000) ∧
    -Real.log (499813 / 500000) ≤ (37407 / 100000000) := by
  have h := checkLog_sound (w := (187 / 999813)) (n := 12)
    (lo := (374069 / 1000000000)) (hi := (37407 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499813) = 1/(499813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10784 : Bounds (-37407 / 100000000) (-374069 / 1000000000) (Real.log (499813 / 500000)) := by
  have h := reflection_log_10784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10785_neg : (43930163 / 250000000) ≤ -Real.log (200000 / 238421) ∧
    -Real.log (200000 / 238421) ≤ (175720653 / 1000000000) := by
  have h := checkLog_sound (w := (38421 / 438421)) (n := 12)
    (lo := (43930163 / 250000000)) (hi := (175720653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238421 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238421 / 200000) = 1/(200000 / 238421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10785 : Bounds (43930163 / 250000000) (175720653 / 1000000000) (Real.log (238421 / 200000)) := by
  have h := reflection_log_10785_neg
  have he : Real.log (238421 / 200000) = -Real.log (200000 / 238421) := by
    rw [show ((238421 / 200000) : ℝ) = ((200000 / 238421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10786_neg : (213323179 / 1000000000) ≤ -Real.log (161579 / 200000) ∧
    -Real.log (161579 / 200000) ≤ (10666159 / 50000000) := by
  have h := checkLog_sound (w := (38421 / 361579)) (n := 12)
    (lo := (213323179 / 1000000000)) (hi := (10666159 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 161579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 161579) = 1/(161579 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10786 : Bounds (-10666159 / 50000000) (-213323179 / 1000000000) (Real.log (161579 / 200000)) := by
  have h := reflection_log_10786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10787_neg : (37602527 / 1000000000) ≤ -Real.log (38523826759 / 40000000000) ∧
    -Real.log (38523826759 / 40000000000) ≤ (1175079 / 31250000) := by
  have h := checkLog_sound (w := (1476173241 / 78523826759)) (n := 12)
    (lo := (37602527 / 1000000000)) (hi := (1175079 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38523826759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38523826759) = 1/(38523826759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10787 : Bounds (-1175079 / 31250000) (-37602527 / 1000000000) (Real.log (38523826759 / 40000000000)) := by
  have h := reflection_log_10787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10788_neg : (4655301 / 125000000) ≤ -Real.log (1505379 / 1562500) ∧
    -Real.log (1505379 / 1562500) ≤ (37242409 / 1000000000) := by
  have h := checkLog_sound (w := (57121 / 3067879)) (n := 12)
    (lo := (4655301 / 125000000)) (hi := (37242409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1562500 / 1505379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1562500 / 1505379) = 1/(1505379 / 1562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10788 : Bounds (-37242409 / 1000000000) (-4655301 / 125000000) (Real.log (1505379 / 1562500)) := by
  have h := reflection_log_10788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10789_neg : (389043831 / 1000000000) ≤ -Real.log (5000000000 / 7377846131) ∧
    -Real.log (5000000000 / 7377846131) ≤ (48630479 / 125000000) := by
  have h := checkLog_sound (w := (2377846131 / 12377846131)) (n := 12)
    (lo := (389043831 / 1000000000)) (hi := (48630479 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7377846131 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7377846131 / 5000000000) = 1/(5000000000 / 7377846131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10789 : Bounds (389043831 / 1000000000) (48630479 / 125000000) (Real.log (7377846131 / 5000000000)) := by
  have h := reflection_log_10789_neg
  have he : Real.log (7377846131 / 5000000000) = -Real.log (5000000000 / 7377846131) := by
    rw [show ((7377846131 / 5000000000) : ℝ) = ((5000000000 / 7377846131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10790_neg : (48987929 / 62500000) ≤ -Real.log (250000000000 / 547448165869) ∧
    -Real.log (250000000000 / 547448165869) ≤ (391903433 / 500000000) := by
  have h := checkLog_sound (w := (47448165869 / 1047448165869)) (n := 12)
    (lo := (22664921 / 250000000)) (hi := (18131937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547448165869 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(547448165869 / 500000000000) = 1/(250000000000 / 547448165869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10790 : Bounds (48987929 / 62500000) (391903433 / 500000000) (Real.log (547448165869 / 250000000000)) := by
  have h := reflection_log_10790_neg
  have he : Real.log (547448165869 / 250000000000) = -Real.log (250000000000 / 547448165869) := by
    rw [show ((547448165869 / 250000000000) : ℝ) = ((250000000000 / 547448165869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10791_neg : (786131101 / 1000000000) ≤ -Real.log (500000000000 / 1097444089457) ∧
    -Real.log (500000000000 / 1097444089457) ≤ (786131103 / 1000000000) := by
  have h := checkLog_sound (w := (97444089457 / 2097444089457)) (n := 12)
    (lo := (92983921 / 1000000000)) (hi := (46491961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097444089457 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1097444089457 / 1000000000000) = 1/(500000000000 / 1097444089457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10791 : Bounds (786131101 / 1000000000) (786131103 / 1000000000) (Real.log (1097444089457 / 500000000000)) := by
  have h := reflection_log_10791_neg
  have he : Real.log (1097444089457 / 500000000000) = -Real.log (500000000000 / 1097444089457) := by
    rw [show ((1097444089457 / 500000000000) : ℝ) = ((500000000000 / 1097444089457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10792_neg : (318453731 / 1000000000) ≤ -Real.log (8 / 11) ∧
    -Real.log (8 / 11) ≤ (79613433 / 250000000) := by
  have h := checkLog_sound (w := (3 / 19)) (n := 12)
    (lo := (318453731 / 1000000000)) (hi := (79613433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11 / 8) = 1/(8 / 11) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10792 : Bounds (318453731 / 1000000000) (79613433 / 250000000) (Real.log (11 / 8)) := by
  have h := reflection_log_10792_neg
  have he : Real.log (11 / 8) = -Real.log (8 / 11) := by
    rw [show ((11 / 8) : ℝ) = ((8 / 11) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10793_neg : (470003629 / 1000000000) ≤ -Real.log (5 / 8) ∧
    -Real.log (5 / 8) ≤ (47000363 / 100000000) := by
  have h := checkLog_sound (w := (3 / 13)) (n := 12)
    (lo := (470003629 / 1000000000)) (hi := (47000363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 5) = 1/(5 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10793 : Bounds (-47000363 / 100000000) (-470003629 / 1000000000) (Real.log (5 / 8)) := by
  have h := reflection_log_10793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10794_neg : (374929 / 1000000000) ≤ -Real.log (8000 / 8003) ∧
    -Real.log (8000 / 8003) ≤ (37493 / 100000000) := by
  have h := checkLog_sound (w := (3 / 16003)) (n := 12)
    (lo := (374929 / 1000000000)) (hi := (37493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8003 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8003 / 8000) = 1/(8000 / 8003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10794 : Bounds (374929 / 1000000000) (37493 / 100000000) (Real.log (8003 / 8000)) := by
  have h := reflection_log_10794_neg
  have he : Real.log (8003 / 8000) = -Real.log (8000 / 8003) := by
    rw [show ((8003 / 8000) : ℝ) = ((8000 / 8003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10795_neg : (37507 / 100000000) ≤ -Real.log (7997 / 8000) ∧
    -Real.log (7997 / 8000) ≤ (375071 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 15997)) (n := 12)
    (lo := (37507 / 100000000)) (hi := (375071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 7997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 7997) = 1/(7997 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10795 : Bounds (-375071 / 1000000000) (-37507 / 100000000) (Real.log (7997 / 8000)) := by
  have h := reflection_log_10795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10796_neg : (21926803 / 125000000) ≤ -Real.log (50000 / 59587) ∧
    -Real.log (50000 / 59587) ≤ (7016577 / 40000000) := by
  have h := checkLog_sound (w := (9587 / 109587)) (n := 12)
    (lo := (21926803 / 125000000)) (hi := (7016577 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59587 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59587 / 50000) = 1/(50000 / 59587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10796 : Bounds (21926803 / 125000000) (7016577 / 40000000) (Real.log (59587 / 50000)) := by
  have h := reflection_log_10796_neg
  have he : Real.log (59587 / 50000) = -Real.log (50000 / 59587) := by
    rw [show ((59587 / 50000) : ℝ) = ((50000 / 59587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10797_neg : (21287149 / 100000000) ≤ -Real.log (40413 / 50000) ∧
    -Real.log (40413 / 50000) ≤ (212871491 / 1000000000) := by
  have h := checkLog_sound (w := (9587 / 90413)) (n := 12)
    (lo := (21287149 / 100000000)) (hi := (212871491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40413) = 1/(40413 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10797 : Bounds (-212871491 / 1000000000) (-21287149 / 100000000) (Real.log (40413 / 50000)) := by
  have h := reflection_log_10797_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10798_neg : (5505449 / 31250000) ≤ -Real.log (500000 / 596323) ∧
    -Real.log (500000 / 596323) ≤ (176174369 / 1000000000) := by
  have h := checkLog_sound (w := (96323 / 1096323)) (n := 12)
    (lo := (5505449 / 31250000)) (hi := (176174369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596323 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596323 / 500000) = 1/(500000 / 596323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10798 : Bounds (5505449 / 31250000) (176174369 / 1000000000) (Real.log (596323 / 500000)) := by
  have h := reflection_log_10798_neg
  have he : Real.log (596323 / 500000) = -Real.log (500000 / 596323) := by
    rw [show ((596323 / 500000) : ℝ) = ((500000 / 596323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10799_neg : (42798609 / 200000000) ≤ -Real.log (403677 / 500000) ∧
    -Real.log (403677 / 500000) ≤ (106996523 / 500000000) := by
  have h := checkLog_sound (w := (96323 / 903677)) (n := 12)
    (lo := (42798609 / 200000000)) (hi := (106996523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403677) = 1/(403677 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10799 : Bounds (-106996523 / 500000000) (-42798609 / 200000000) (Real.log (403677 / 500000)) := by
  have h := reflection_log_10799_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10800_neg : (37818677 / 1000000000) ≤ -Real.log (240721879671 / 250000000000) ∧
    -Real.log (240721879671 / 250000000000) ≤ (18909339 / 500000000) := by
  have h := checkLog_sound (w := (9278120329 / 490721879671)) (n := 12)
    (lo := (37818677 / 1000000000)) (hi := (18909339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240721879671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240721879671) = 1/(240721879671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10800 : Bounds (-18909339 / 500000000) (-37818677 / 1000000000) (Real.log (240721879671 / 250000000000)) := by
  have h := reflection_log_10800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10801_neg : (7491413 / 200000000) ≤ -Real.log (2408089431 / 2500000000) ∧
    -Real.log (2408089431 / 2500000000) ≤ (18728533 / 500000000) := by
  have h := checkLog_sound (w := (91910569 / 4908089431)) (n := 12)
    (lo := (7491413 / 200000000)) (hi := (18728533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2408089431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2408089431) = 1/(2408089431 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10801 : Bounds (-18728533 / 500000000) (-7491413 / 200000000) (Real.log (2408089431 / 2500000000)) := by
  have h := reflection_log_10801_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10802_neg : (194142957 / 500000000) ≤ -Real.log (500000000000 / 737225645213) ∧
    -Real.log (500000000000 / 737225645213) ≤ (77657183 / 200000000) := by
  have h := checkLog_sound (w := (237225645213 / 1237225645213)) (n := 12)
    (lo := (194142957 / 500000000)) (hi := (77657183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737225645213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737225645213 / 500000000000) = 1/(500000000000 / 737225645213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10802 : Bounds (194142957 / 500000000) (77657183 / 200000000) (Real.log (737225645213 / 500000000000)) := by
  have h := reflection_log_10802_neg
  have he : Real.log (737225645213 / 500000000000) = -Real.log (500000000000 / 737225645213) := by
    rw [show ((737225645213 / 500000000000) : ℝ) = ((500000000000 / 737225645213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10803_neg : (390167413 / 1000000000) ≤ -Real.log (250000000000 / 369307020217) ∧
    -Real.log (250000000000 / 369307020217) ≤ (195083707 / 500000000) := by
  have h := checkLog_sound (w := (119307020217 / 619307020217)) (n := 12)
    (lo := (390167413 / 1000000000)) (hi := (195083707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369307020217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369307020217 / 250000000000) = 1/(250000000000 / 369307020217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10803 : Bounds (390167413 / 1000000000) (195083707 / 500000000) (Real.log (369307020217 / 250000000000)) := by
  have h := reflection_log_10803_neg
  have he : Real.log (369307020217 / 250000000000) = -Real.log (250000000000 / 369307020217) := by
    rw [show ((369307020217 / 250000000000) : ℝ) = ((250000000000 / 369307020217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10804_neg : (786131101 / 1000000000) ≤ -Real.log (31250000000 / 68590255591) ∧
    -Real.log (31250000000 / 68590255591) ≤ (786131103 / 1000000000) := by
  have h := checkLog_sound (w := (6090255591 / 131090255591)) (n := 12)
    (lo := (92983921 / 1000000000)) (hi := (46491961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68590255591 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68590255591 / 62500000000) = 1/(31250000000 / 68590255591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10804 : Bounds (786131101 / 1000000000) (786131103 / 1000000000) (Real.log (68590255591 / 31250000000)) := by
  have h := reflection_log_10804_neg
  have he : Real.log (68590255591 / 31250000000) = -Real.log (31250000000 / 68590255591) := by
    rw [show ((68590255591 / 31250000000) : ℝ) = ((31250000000 / 68590255591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10805_neg : (788457359 / 1000000000) ≤ -Real.log (5 / 11) ∧
    -Real.log (5 / 11) ≤ (788457361 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 21)) (n := 12)
    (lo := (95310179 / 1000000000)) (hi := (4765509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11 / 10) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11 / 10) = 1/(5 / 11) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10805 : Bounds (788457359 / 1000000000) (788457361 / 1000000000) (Real.log (11 / 5)) := by
  have h := reflection_log_10805_neg
  have he : Real.log (11 / 5) = -Real.log (5 / 11) := by
    rw [show ((11 / 5) : ℝ) = ((5 / 11) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10806_neg : (319180739 / 1000000000) ≤ -Real.log (125 / 172) ∧
    -Real.log (125 / 172) ≤ (15959037 / 50000000) := by
  have h := checkLog_sound (w := (47 / 297)) (n := 12)
    (lo := (319180739 / 1000000000)) (hi := (15959037 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172 / 125) = 1/(125 / 172) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10806 : Bounds (319180739 / 1000000000) (15959037 / 50000000) (Real.log (172 / 125)) := by
  have h := reflection_log_10806_neg
  have he : Real.log (172 / 125) = -Real.log (125 / 172) := by
    rw [show ((172 / 125) : ℝ) = ((125 / 172) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10807_neg : (47160491 / 100000000) ≤ -Real.log (78 / 125) ∧
    -Real.log (78 / 125) ≤ (471604911 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 203)) (n := 12)
    (lo := (47160491 / 100000000)) (hi := (471604911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 78) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 78) = 1/(78 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10807 : Bounds (-471604911 / 1000000000) (-47160491 / 100000000) (Real.log (78 / 125)) := by
  have h := reflection_log_10807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10808_neg : (375929 / 1000000000) ≤ -Real.log (125000 / 125047) ∧
    -Real.log (125000 / 125047) ≤ (37593 / 100000000) := by
  have h := checkLog_sound (w := (47 / 250047)) (n := 12)
    (lo := (375929 / 1000000000)) (hi := (37593 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125047 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125047 / 125000) = 1/(125000 / 125047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10808 : Bounds (375929 / 1000000000) (37593 / 100000000) (Real.log (125047 / 125000)) := by
  have h := reflection_log_10808_neg
  have he : Real.log (125047 / 125000) = -Real.log (125000 / 125047) := by
    rw [show ((125047 / 125000) : ℝ) = ((125000 / 125047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10809_neg : (37607 / 100000000) ≤ -Real.log (124953 / 125000) ∧
    -Real.log (124953 / 125000) ≤ (376071 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 249953)) (n := 12)
    (lo := (37607 / 100000000)) (hi := (376071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124953) = 1/(124953 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10809 : Bounds (-376071 / 1000000000) (-37607 / 100000000) (Real.log (124953 / 125000)) := by
  have h := reflection_log_10809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10810_neg : (2198343 / 12500000) ≤ -Real.log (25000 / 29807) ∧
    -Real.log (25000 / 29807) ≤ (175867441 / 1000000000) := by
  have h := checkLog_sound (w := (4807 / 54807)) (n := 12)
    (lo := (2198343 / 12500000)) (hi := (175867441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29807 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29807 / 25000) = 1/(25000 / 29807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10810 : Bounds (2198343 / 12500000) (175867441 / 1000000000) (Real.log (29807 / 25000)) := by
  have h := reflection_log_10810_neg
  have he : Real.log (29807 / 25000) = -Real.log (25000 / 29807) := by
    rw [show ((29807 / 25000) : ℝ) = ((25000 / 29807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10811_neg : (42707963 / 200000000) ≤ -Real.log (20193 / 25000) ∧
    -Real.log (20193 / 25000) ≤ (26692477 / 125000000) := by
  have h := checkLog_sound (w := (4807 / 45193)) (n := 12)
    (lo := (42707963 / 200000000)) (hi := (26692477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20193) = 1/(20193 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10811 : Bounds (-26692477 / 125000000) (-42707963 / 200000000) (Real.log (20193 / 25000)) := by
  have h := reflection_log_10811_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10812_neg : (88313939 / 500000000) ≤ -Real.log (1000000 / 1193187) ∧
    -Real.log (1000000 / 1193187) ≤ (176627879 / 1000000000) := by
  have h := checkLog_sound (w := (193187 / 2193187)) (n := 12)
    (lo := (88313939 / 500000000)) (hi := (176627879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193187 / 1000000) = 1/(1000000 / 1193187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10812 : Bounds (88313939 / 500000000) (176627879 / 1000000000) (Real.log (1193187 / 1000000)) := by
  have h := reflection_log_10812_neg
  have he : Real.log (1193187 / 1000000) = -Real.log (1000000 / 1193187) := by
    rw [show ((1193187 / 1000000) : ℝ) = ((1000000 / 1193187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10813_neg : (214663359 / 1000000000) ≤ -Real.log (806813 / 1000000) ∧
    -Real.log (806813 / 1000000) ≤ (670823 / 3125000) := by
  have h := checkLog_sound (w := (193187 / 1806813)) (n := 12)
    (lo := (214663359 / 1000000000)) (hi := (670823 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806813) = 1/(806813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10813 : Bounds (-670823 / 3125000) (-214663359 / 1000000000) (Real.log (806813 / 1000000)) := by
  have h := reflection_log_10813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10814_neg : (38035481 / 1000000000) ≤ -Real.log (962678783031 / 1000000000000) ∧
    -Real.log (962678783031 / 1000000000000) ≤ (19017741 / 500000000) := by
  have h := checkLog_sound (w := (37321216969 / 1962678783031)) (n := 12)
    (lo := (38035481 / 1000000000)) (hi := (19017741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962678783031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962678783031) = 1/(962678783031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10814 : Bounds (-19017741 / 500000000) (-38035481 / 1000000000) (Real.log (962678783031 / 1000000000000)) := by
  have h := reflection_log_10814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10815_neg : (18836187 / 500000000) ≤ -Real.log (601892751 / 625000000) ∧
    -Real.log (601892751 / 625000000) ≤ (301379 / 8000000) := by
  have h := checkLog_sound (w := (23107249 / 1226892751)) (n := 12)
    (lo := (18836187 / 500000000)) (hi := (301379 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 601892751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 601892751) = 1/(601892751 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10815 : Bounds (-301379 / 8000000) (-18836187 / 500000000) (Real.log (601892751 / 625000000)) := by
  have h := reflection_log_10815_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


