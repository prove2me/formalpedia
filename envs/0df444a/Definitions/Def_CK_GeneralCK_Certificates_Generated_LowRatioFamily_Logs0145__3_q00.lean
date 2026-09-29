-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0145__3_q00
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0145__3_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T05:02:16.373634+00:00
-- url     : https://prove2.me/theorems/6d5d2f51-4f49-4fc7-be00-411ce5f5ba1b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0146, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0147) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0145 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0146, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0147) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0145 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9280_neg : (31034607 / 200000000) ≤ -Real.log (856267 / 1000000) ∧
    -Real.log (856267 / 1000000) ≤ (38793259 / 250000000) := by
  have h := checkLog_sound (w := (143733 / 1856267)) (n := 12)
    (lo := (31034607 / 200000000)) (hi := (38793259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 856267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 856267) = 1/(856267 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9280 : Bounds (-38793259 / 250000000) (-31034607 / 200000000) (Real.log (856267 / 1000000)) := by
  have h := reflection_log_9280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9281_neg : (20875561 / 1000000000) ≤ -Real.log (979340824711 / 1000000000000) ∧
    -Real.log (979340824711 / 1000000000000) ≤ (10437781 / 500000000) := by
  have h := checkLog_sound (w := (20659175289 / 1979340824711)) (n := 12)
    (lo := (20875561 / 1000000000)) (hi := (10437781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979340824711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979340824711) = 1/(979340824711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9281 : Bounds (-10437781 / 500000000) (-20875561 / 1000000000) (Real.log (979340824711 / 1000000000000)) := by
  have h := reflection_log_9281_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9282_neg : (20717073 / 1000000000) ≤ -Real.log (15304625799 / 15625000000) ∧
    -Real.log (15304625799 / 15625000000) ≤ (10358537 / 500000000) := by
  have h := checkLog_sound (w := (320374201 / 30929625799)) (n := 12)
    (lo := (20717073 / 1000000000)) (hi := (10358537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15304625799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15304625799) = 1/(15304625799 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9282 : Bounds (-10358537 / 500000000) (-20717073 / 1000000000) (Real.log (15304625799 / 15625000000)) := by
  have h := reflection_log_9282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9283_neg : (72091443 / 250000000) ≤ -Real.log (500000000000 / 667122622571) ∧
    -Real.log (500000000000 / 667122622571) ≤ (288365773 / 1000000000) := by
  have h := checkLog_sound (w := (167122622571 / 1167122622571)) (n := 12)
    (lo := (72091443 / 250000000)) (hi := (288365773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667122622571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667122622571 / 500000000000) = 1/(500000000000 / 667122622571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9283 : Bounds (72091443 / 250000000) (288365773 / 1000000000) (Real.log (667122622571 / 500000000000)) := by
  have h := reflection_log_9283_neg
  have he : Real.log (667122622571 / 500000000000) = -Real.log (500000000000 / 667122622571) := by
    rw [show ((667122622571 / 500000000000) : ℝ) = ((500000000000 / 667122622571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9284_neg : (289470509 / 1000000000) ≤ -Real.log (500000000000 / 667860024969) ∧
    -Real.log (500000000000 / 667860024969) ≤ (28947051 / 100000000) := by
  have h := checkLog_sound (w := (167860024969 / 1167860024969)) (n := 12)
    (lo := (289470509 / 1000000000)) (hi := (28947051 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667860024969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667860024969 / 500000000000) = 1/(500000000000 / 667860024969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9284 : Bounds (289470509 / 1000000000) (28947051 / 100000000) (Real.log (667860024969 / 500000000000)) := by
  have h := reflection_log_9284_neg
  have he : Real.log (667860024969 / 500000000000) = -Real.log (500000000000 / 667860024969) := by
    rw [show ((667860024969 / 500000000000) : ℝ) = ((500000000000 / 667860024969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9285_neg : (580793629 / 1000000000) ≤ -Real.log (125000000000 / 223432055749) ∧
    -Real.log (125000000000 / 223432055749) ≤ (58079363 / 100000000) := by
  have h := checkLog_sound (w := (98432055749 / 348432055749)) (n := 12)
    (lo := (580793629 / 1000000000)) (hi := (58079363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223432055749 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223432055749 / 125000000000) = 1/(125000000000 / 223432055749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9285 : Bounds (580793629 / 1000000000) (58079363 / 100000000) (Real.log (223432055749 / 125000000000)) := by
  have h := reflection_log_9285_neg
  have he : Real.log (223432055749 / 125000000000) = -Real.log (125000000000 / 223432055749) := by
    rw [show ((223432055749 / 125000000000) : ℝ) = ((125000000000 / 223432055749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9286_neg : (145470131 / 250000000) ≤ -Real.log (500000000000 / 894700139471) ∧
    -Real.log (500000000000 / 894700139471) ≤ (23275221 / 40000000) := by
  have h := checkLog_sound (w := (394700139471 / 1394700139471)) (n := 12)
    (lo := (145470131 / 250000000)) (hi := (23275221 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((894700139471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(894700139471 / 500000000000) = 1/(500000000000 / 894700139471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9286 : Bounds (145470131 / 250000000) (23275221 / 40000000) (Real.log (894700139471 / 500000000000)) := by
  have h := reflection_log_9286_neg
  have he : Real.log (894700139471 / 500000000000) = -Real.log (500000000000 / 894700139471) := by
    rw [show ((894700139471 / 500000000000) : ℝ) = ((500000000000 / 894700139471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9287_neg : (249590721 / 1000000000) ≤ -Real.log (2000 / 2567) ∧
    -Real.log (2000 / 2567) ≤ (124795361 / 500000000) := by
  have h := checkLog_sound (w := (567 / 4567)) (n := 12)
    (lo := (249590721 / 1000000000)) (hi := (124795361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2567 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2567 / 2000) = 1/(2000 / 2567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9287 : Bounds (249590721 / 1000000000) (124795361 / 500000000) (Real.log (2567 / 2000)) := by
  have h := reflection_log_9287_neg
  have he : Real.log (2567 / 2000) = -Real.log (2000 / 2567) := by
    rw [show ((2567 / 2000) : ℝ) = ((2000 / 2567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9288_neg : (333377031 / 1000000000) ≤ -Real.log (1433 / 2000) ∧
    -Real.log (1433 / 2000) ≤ (41672129 / 125000000) := by
  have h := checkLog_sound (w := (567 / 3433)) (n := 12)
    (lo := (333377031 / 1000000000)) (hi := (41672129 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1433) = 1/(1433 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9288 : Bounds (-41672129 / 125000000) (-333377031 / 1000000000) (Real.log (1433 / 2000)) := by
  have h := reflection_log_9288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9289_neg : (283459 / 1000000000) ≤ -Real.log (2000000 / 2000567) ∧
    -Real.log (2000000 / 2000567) ≤ (14173 / 50000000) := by
  have h := checkLog_sound (w := (567 / 4000567)) (n := 12)
    (lo := (283459 / 1000000000)) (hi := (14173 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000567 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000567 / 2000000) = 1/(2000000 / 2000567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9289 : Bounds (283459 / 1000000000) (14173 / 50000000) (Real.log (2000567 / 2000000)) := by
  have h := reflection_log_9289_neg
  have he : Real.log (2000567 / 2000000) = -Real.log (2000000 / 2000567) := by
    rw [show ((2000567 / 2000000) : ℝ) = ((2000000 / 2000567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9290_neg : (14177 / 50000000) ≤ -Real.log (1999433 / 2000000) ∧
    -Real.log (1999433 / 2000000) ≤ (283541 / 1000000000) := by
  have h := checkLog_sound (w := (567 / 3999433)) (n := 12)
    (lo := (14177 / 50000000)) (hi := (283541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999433) = 1/(1999433 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9290 : Bounds (-283541 / 1000000000) (-14177 / 50000000) (Real.log (1999433 / 2000000)) := by
  have h := reflection_log_9290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9291_neg : (134052631 / 1000000000) ≤ -Real.log (1000000 / 1143453) ∧
    -Real.log (1000000 / 1143453) ≤ (16756579 / 125000000) := by
  have h := checkLog_sound (w := (143453 / 2143453)) (n := 12)
    (lo := (134052631 / 1000000000)) (hi := (16756579 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1143453 / 1000000) = 1/(1000000 / 1143453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9291 : Bounds (134052631 / 1000000000) (16756579 / 125000000) (Real.log (1143453 / 1000000)) := by
  have h := reflection_log_9291_neg
  have he : Real.log (1143453 / 1000000) = -Real.log (1000000 / 1143453) := by
    rw [show ((1143453 / 1000000) : ℝ) = ((1000000 / 1143453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9292_neg : (19355761 / 125000000) ≤ -Real.log (856547 / 1000000) ∧
    -Real.log (856547 / 1000000) ≤ (154846089 / 1000000000) := by
  have h := checkLog_sound (w := (143453 / 1856547)) (n := 12)
    (lo := (19355761 / 125000000)) (hi := (154846089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 856547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 856547) = 1/(856547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9292 : Bounds (-154846089 / 1000000000) (-19355761 / 125000000) (Real.log (856547 / 1000000)) := by
  have h := reflection_log_9292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9293_neg : (67263261 / 500000000) ≤ -Real.log (200000 / 228799) ∧
    -Real.log (200000 / 228799) ≤ (134526523 / 1000000000) := by
  have h := checkLog_sound (w := (28799 / 428799)) (n := 12)
    (lo := (67263261 / 500000000)) (hi := (134526523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228799 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228799 / 200000) = 1/(200000 / 228799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9293 : Bounds (67263261 / 500000000) (134526523 / 1000000000) (Real.log (228799 / 200000)) := by
  have h := reflection_log_9293_neg
  have he : Real.log (228799 / 200000) = -Real.log (200000 / 228799) := by
    rw [show ((228799 / 200000) : ℝ) = ((200000 / 228799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9294_neg : (155479061 / 1000000000) ≤ -Real.log (171201 / 200000) ∧
    -Real.log (171201 / 200000) ≤ (77739531 / 500000000) := by
  have h := checkLog_sound (w := (28799 / 371201)) (n := 12)
    (lo := (155479061 / 1000000000)) (hi := (77739531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 171201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 171201) = 1/(171201 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9294 : Bounds (-77739531 / 500000000) (-155479061 / 1000000000) (Real.log (171201 / 200000)) := by
  have h := reflection_log_9294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9295_neg : (20952539 / 1000000000) ≤ -Real.log (39170617599 / 40000000000) ∧
    -Real.log (39170617599 / 40000000000) ≤ (1047627 / 50000000) := by
  have h := checkLog_sound (w := (829382401 / 79170617599)) (n := 12)
    (lo := (20952539 / 1000000000)) (hi := (1047627 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39170617599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39170617599) = 1/(39170617599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9295 : Bounds (-1047627 / 50000000) (-20952539 / 1000000000) (Real.log (39170617599 / 40000000000)) := by
  have h := reflection_log_9295_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9296_neg : (1299591 / 62500000) ≤ -Real.log (979421236791 / 1000000000000) ∧
    -Real.log (979421236791 / 1000000000000) ≤ (20793457 / 1000000000) := by
  have h := checkLog_sound (w := (20578763209 / 1979421236791)) (n := 12)
    (lo := (1299591 / 62500000)) (hi := (20793457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979421236791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979421236791) = 1/(979421236791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9296 : Bounds (-20793457 / 1000000000) (-1299591 / 62500000) (Real.log (979421236791 / 1000000000000)) := by
  have h := reflection_log_9296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9297_neg : (288898719 / 1000000000) ≤ -Real.log (125000000000 / 166869564659) ∧
    -Real.log (125000000000 / 166869564659) ≤ (1805617 / 6250000) := by
  have h := checkLog_sound (w := (41869564659 / 291869564659)) (n := 12)
    (lo := (288898719 / 1000000000)) (hi := (1805617 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166869564659 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166869564659 / 125000000000) = 1/(125000000000 / 166869564659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9297 : Bounds (288898719 / 1000000000) (1805617 / 6250000) (Real.log (166869564659 / 125000000000)) := by
  have h := reflection_log_9297_neg
  have he : Real.log (166869564659 / 125000000000) = -Real.log (125000000000 / 166869564659) := by
    rw [show ((166869564659 / 125000000000) : ℝ) = ((125000000000 / 166869564659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9298_neg : (18125349 / 62500000) ≤ -Real.log (250000000000 / 334108737683) ∧
    -Real.log (250000000000 / 334108737683) ≤ (58001117 / 200000000) := by
  have h := checkLog_sound (w := (84108737683 / 584108737683)) (n := 12)
    (lo := (18125349 / 62500000)) (hi := (58001117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334108737683 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334108737683 / 250000000000) = 1/(250000000000 / 334108737683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9298 : Bounds (18125349 / 62500000) (58001117 / 200000000) (Real.log (334108737683 / 250000000000)) := by
  have h := reflection_log_9298_neg
  have he : Real.log (334108737683 / 250000000000) = -Real.log (250000000000 / 334108737683) := by
    rw [show ((334108737683 / 250000000000) : ℝ) = ((250000000000 / 334108737683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9299_neg : (145470131 / 250000000) ≤ -Real.log (50000000000 / 89470013947) ∧
    -Real.log (50000000000 / 89470013947) ≤ (23275221 / 40000000) := by
  have h := checkLog_sound (w := (39470013947 / 139470013947)) (n := 12)
    (lo := (145470131 / 250000000)) (hi := (23275221 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89470013947 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89470013947 / 50000000000) = 1/(50000000000 / 89470013947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9299 : Bounds (145470131 / 250000000) (23275221 / 40000000) (Real.log (89470013947 / 50000000000)) := by
  have h := reflection_log_9299_neg
  have he : Real.log (89470013947 / 50000000000) = -Real.log (50000000000 / 89470013947) := by
    rw [show ((89470013947 / 50000000000) : ℝ) = ((50000000000 / 89470013947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9300_neg : (582967753 / 1000000000) ≤ -Real.log (250000000000 / 447836706211) ∧
    -Real.log (250000000000 / 447836706211) ≤ (291483877 / 500000000) := by
  have h := checkLog_sound (w := (197836706211 / 697836706211)) (n := 12)
    (lo := (582967753 / 1000000000)) (hi := (291483877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447836706211 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447836706211 / 250000000000) = 1/(250000000000 / 447836706211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9300 : Bounds (582967753 / 1000000000) (291483877 / 500000000) (Real.log (447836706211 / 250000000000)) := by
  have h := reflection_log_9300_neg
  have he : Real.log (447836706211 / 250000000000) = -Real.log (250000000000 / 447836706211) := by
    rw [show ((447836706211 / 250000000000) : ℝ) = ((250000000000 / 447836706211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9301_neg : (49996041 / 200000000) ≤ -Real.log (250 / 321) ∧
    -Real.log (250 / 321) ≤ (124990103 / 500000000) := by
  have h := checkLog_sound (w := (71 / 571)) (n := 12)
    (lo := (49996041 / 200000000)) (hi := (124990103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321 / 250) = 1/(250 / 321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9301 : Bounds (49996041 / 200000000) (124990103 / 500000000) (Real.log (321 / 250)) := by
  have h := reflection_log_9301_neg
  have he : Real.log (321 / 250) = -Real.log (250 / 321) := by
    rw [show ((321 / 250) : ℝ) = ((250 / 321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9302_neg : (41759389 / 125000000) ≤ -Real.log (179 / 250) ∧
    -Real.log (179 / 250) ≤ (334075113 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 429)) (n := 12)
    (lo := (41759389 / 125000000)) (hi := (334075113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 179) = 1/(179 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9302 : Bounds (-334075113 / 1000000000) (-41759389 / 125000000) (Real.log (179 / 250)) := by
  have h := reflection_log_9302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9303_neg : (283959 / 1000000000) ≤ -Real.log (250000 / 250071) ∧
    -Real.log (250000 / 250071) ≤ (7099 / 25000000) := by
  have h := checkLog_sound (w := (71 / 500071)) (n := 12)
    (lo := (283959 / 1000000000)) (hi := (7099 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250071 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250071 / 250000) = 1/(250000 / 250071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9303 : Bounds (283959 / 1000000000) (7099 / 25000000) (Real.log (250071 / 250000)) := by
  have h := reflection_log_9303_neg
  have he : Real.log (250071 / 250000) = -Real.log (250000 / 250071) := by
    rw [show ((250071 / 250000) : ℝ) = ((250000 / 250071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9304_neg : (7101 / 25000000) ≤ -Real.log (249929 / 250000) ∧
    -Real.log (249929 / 250000) ≤ (284041 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 499929)) (n := 12)
    (lo := (7101 / 25000000)) (hi := (284041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249929) = 1/(249929 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9304 : Bounds (-284041 / 1000000000) (-7101 / 25000000) (Real.log (249929 / 250000)) := by
  have h := reflection_log_9304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9305_neg : (134280861 / 1000000000) ≤ -Real.log (500000 / 571857) ∧
    -Real.log (500000 / 571857) ≤ (67140431 / 500000000) := by
  have h := checkLog_sound (w := (71857 / 1071857)) (n := 12)
    (lo := (134280861 / 1000000000)) (hi := (67140431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571857 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571857 / 500000) = 1/(500000 / 571857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9305 : Bounds (134280861 / 1000000000) (67140431 / 500000000) (Real.log (571857 / 500000)) := by
  have h := reflection_log_9305_neg
  have he : Real.log (571857 / 500000) = -Real.log (500000 / 571857) := by
    rw [show ((571857 / 500000) : ℝ) = ((500000 / 571857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9306_neg : (77575423 / 500000000) ≤ -Real.log (428143 / 500000) ∧
    -Real.log (428143 / 500000) ≤ (155150847 / 1000000000) := by
  have h := checkLog_sound (w := (71857 / 928143)) (n := 12)
    (lo := (77575423 / 500000000)) (hi := (155150847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 428143) = 1/(428143 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9306 : Bounds (-155150847 / 1000000000) (-77575423 / 500000000) (Real.log (428143 / 500000)) := by
  have h := reflection_log_9306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9307_neg : (33688661 / 250000000) ≤ -Real.log (15625 / 17879) ∧
    -Real.log (15625 / 17879) ≤ (26950929 / 200000000) := by
  have h := checkLog_sound (w := (1127 / 16752)) (n := 12)
    (lo := (33688661 / 250000000)) (hi := (26950929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17879 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17879 / 15625) = 1/(15625 / 17879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9307 : Bounds (33688661 / 250000000) (26950929 / 200000000) (Real.log (17879 / 15625)) := by
  have h := reflection_log_9307_neg
  have he : Real.log (17879 / 15625) = -Real.log (15625 / 17879) := by
    rw [show ((17879 / 15625) : ℝ) = ((15625 / 17879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9308_neg : (38946003 / 250000000) ≤ -Real.log (13371 / 15625) ∧
    -Real.log (13371 / 15625) ≤ (155784013 / 1000000000) := by
  have h := checkLog_sound (w := (1127 / 14498)) (n := 12)
    (lo := (38946003 / 250000000)) (hi := (155784013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13371) = 1/(13371 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9308 : Bounds (-155784013 / 1000000000) (-38946003 / 250000000) (Real.log (13371 / 15625)) := by
  have h := reflection_log_9308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9309_neg : (2628671 / 125000000) ≤ -Real.log (239060109 / 244140625) ∧
    -Real.log (239060109 / 244140625) ≤ (21029369 / 1000000000) := by
  have h := checkLog_sound (w := (2540258 / 241600367)) (n := 12)
    (lo := (2628671 / 125000000)) (hi := (21029369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 239060109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 239060109) = 1/(239060109 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9309 : Bounds (-21029369 / 1000000000) (-2628671 / 125000000) (Real.log (239060109 / 244140625)) := by
  have h := reflection_log_9309_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9310_neg : (652187 / 31250000) ≤ -Real.log (244836571551 / 250000000000) ∧
    -Real.log (244836571551 / 250000000000) ≤ (4173997 / 200000000) := by
  have h := checkLog_sound (w := (5163428449 / 494836571551)) (n := 12)
    (lo := (652187 / 31250000)) (hi := (4173997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244836571551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244836571551) = 1/(244836571551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9310 : Bounds (-4173997 / 200000000) (-652187 / 31250000) (Real.log (244836571551 / 250000000000)) := by
  have h := reflection_log_9310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9311_neg : (72357927 / 250000000) ≤ -Real.log (1000000000 / 1335668223) ∧
    -Real.log (1000000000 / 1335668223) ≤ (289431709 / 1000000000) := by
  have h := checkLog_sound (w := (335668223 / 2335668223)) (n := 12)
    (lo := (72357927 / 250000000)) (hi := (289431709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335668223 / 1000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1335668223 / 1000000000) = 1/(1000000000 / 1335668223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9311 : Bounds (72357927 / 250000000) (289431709 / 1000000000) (Real.log (1335668223 / 1000000000)) := by
  have h := reflection_log_9311_neg
  have he : Real.log (1335668223 / 1000000000) = -Real.log (1000000000 / 1335668223) := by
    rw [show ((1335668223 / 1000000000) : ℝ) = ((1000000000 / 1335668223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9312_neg : (290538657 / 1000000000) ≤ -Real.log (20000000000 / 26742951163) ∧
    -Real.log (20000000000 / 26742951163) ≤ (145269329 / 500000000) := by
  have h := checkLog_sound (w := (6742951163 / 46742951163)) (n := 12)
    (lo := (290538657 / 1000000000)) (hi := (145269329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26742951163 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26742951163 / 20000000000) = 1/(20000000000 / 26742951163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9312 : Bounds (290538657 / 1000000000) (145269329 / 500000000) (Real.log (26742951163 / 20000000000)) := by
  have h := reflection_log_9312_neg
  have he : Real.log (26742951163 / 20000000000) = -Real.log (20000000000 / 26742951163) := by
    rw [show ((26742951163 / 20000000000) : ℝ) = ((20000000000 / 26742951163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9313_neg : (582967753 / 1000000000) ≤ -Real.log (500000000000 / 895673412421) ∧
    -Real.log (500000000000 / 895673412421) ≤ (291483877 / 500000000) := by
  have h := checkLog_sound (w := (395673412421 / 1395673412421)) (n := 12)
    (lo := (582967753 / 1000000000)) (hi := (291483877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((895673412421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(895673412421 / 500000000000) = 1/(500000000000 / 895673412421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9313 : Bounds (582967753 / 1000000000) (291483877 / 500000000) (Real.log (895673412421 / 500000000000)) := by
  have h := reflection_log_9313_neg
  have he : Real.log (895673412421 / 500000000000) = -Real.log (500000000000 / 895673412421) := by
    rw [show ((895673412421 / 500000000000) : ℝ) = ((500000000000 / 895673412421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9314_neg : (584055317 / 1000000000) ≤ -Real.log (500000000000 / 896648044693) ∧
    -Real.log (500000000000 / 896648044693) ≤ (292027659 / 500000000) := by
  have h := checkLog_sound (w := (396648044693 / 1396648044693)) (n := 12)
    (lo := (584055317 / 1000000000)) (hi := (292027659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((896648044693 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(896648044693 / 500000000000) = 1/(500000000000 / 896648044693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9314 : Bounds (584055317 / 1000000000) (292027659 / 500000000) (Real.log (896648044693 / 500000000000)) := by
  have h := reflection_log_9314_neg
  have he : Real.log (896648044693 / 500000000000) = -Real.log (500000000000 / 896648044693) := by
    rw [show ((896648044693 / 500000000000) : ℝ) = ((500000000000 / 896648044693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9315_neg : (250369537 / 1000000000) ≤ -Real.log (2000 / 2569) ∧
    -Real.log (2000 / 2569) ≤ (125184769 / 500000000) := by
  have h := checkLog_sound (w := (569 / 4569)) (n := 12)
    (lo := (250369537 / 1000000000)) (hi := (125184769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2569 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2569 / 2000) = 1/(2000 / 2569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9315 : Bounds (250369537 / 1000000000) (125184769 / 500000000) (Real.log (2569 / 2000)) := by
  have h := reflection_log_9315_neg
  have he : Real.log (2569 / 2000) = -Real.log (2000 / 2569) := by
    rw [show ((2569 / 2000) : ℝ) = ((2000 / 2569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9316_neg : (334773679 / 1000000000) ≤ -Real.log (1431 / 2000) ∧
    -Real.log (1431 / 2000) ≤ (4184671 / 12500000) := by
  have h := checkLog_sound (w := (569 / 3431)) (n := 12)
    (lo := (334773679 / 1000000000)) (hi := (4184671 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1431) = 1/(1431 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9316 : Bounds (-4184671 / 12500000) (-334773679 / 1000000000) (Real.log (1431 / 2000)) := by
  have h := reflection_log_9316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9317_neg : (284459 / 1000000000) ≤ -Real.log (2000000 / 2000569) ∧
    -Real.log (2000000 / 2000569) ≤ (14223 / 50000000) := by
  have h := checkLog_sound (w := (569 / 4000569)) (n := 12)
    (lo := (284459 / 1000000000)) (hi := (14223 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000569 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000569 / 2000000) = 1/(2000000 / 2000569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9317 : Bounds (284459 / 1000000000) (14223 / 50000000) (Real.log (2000569 / 2000000)) := by
  have h := reflection_log_9317_neg
  have he : Real.log (2000569 / 2000000) = -Real.log (2000000 / 2000569) := by
    rw [show ((2000569 / 2000000) : ℝ) = ((2000000 / 2000569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9318_neg : (14227 / 50000000) ≤ -Real.log (1999431 / 2000000) ∧
    -Real.log (1999431 / 2000000) ≤ (284541 / 1000000000) := by
  have h := checkLog_sound (w := (569 / 3999431)) (n := 12)
    (lo := (14227 / 50000000)) (hi := (284541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999431) = 1/(1999431 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9318 : Bounds (-284541 / 1000000000) (-14227 / 50000000) (Real.log (1999431 / 2000000)) := by
  have h := reflection_log_9318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9319_neg : (134509039 / 1000000000) ≤ -Real.log (40000 / 45759) ∧
    -Real.log (40000 / 45759) ≤ (1681363 / 12500000) := by
  have h := checkLog_sound (w := (5759 / 85759)) (n := 12)
    (lo := (134509039 / 1000000000)) (hi := (1681363 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45759 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45759 / 40000) = 1/(40000 / 45759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9319 : Bounds (134509039 / 1000000000) (1681363 / 12500000) (Real.log (45759 / 40000)) := by
  have h := reflection_log_9319_neg
  have he : Real.log (45759 / 40000) = -Real.log (40000 / 45759) := by
    rw [show ((45759 / 40000) : ℝ) = ((40000 / 45759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9320_neg : (155455697 / 1000000000) ≤ -Real.log (34241 / 40000) ∧
    -Real.log (34241 / 40000) ≤ (77727849 / 500000000) := by
  have h := checkLog_sound (w := (5759 / 74241)) (n := 12)
    (lo := (155455697 / 1000000000)) (hi := (77727849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34241) = 1/(34241 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9320 : Bounds (-77727849 / 500000000) (-155455697 / 1000000000) (Real.log (34241 / 40000)) := by
  have h := reflection_log_9320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9321_neg : (134983587 / 1000000000) ≤ -Real.log (500000 / 572259) ∧
    -Real.log (500000 / 572259) ≤ (33745897 / 250000000) := by
  have h := checkLog_sound (w := (72259 / 1072259)) (n := 12)
    (lo := (134983587 / 1000000000)) (hi := (33745897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572259 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572259 / 500000) = 1/(500000 / 572259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9321 : Bounds (134983587 / 1000000000) (33745897 / 250000000) (Real.log (572259 / 500000)) := by
  have h := reflection_log_9321_neg
  have he : Real.log (572259 / 500000) = -Real.log (500000 / 572259) := by
    rw [show ((572259 / 500000) : ℝ) = ((500000 / 572259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9322_neg : (78045113 / 500000000) ≤ -Real.log (427741 / 500000) ∧
    -Real.log (427741 / 500000) ≤ (156090227 / 1000000000) := by
  have h := checkLog_sound (w := (72259 / 927741)) (n := 12)
    (lo := (78045113 / 500000000)) (hi := (156090227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427741) = 1/(427741 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9322 : Bounds (-156090227 / 1000000000) (-78045113 / 500000000) (Real.log (427741 / 500000)) := by
  have h := reflection_log_9322_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9323_neg : (10553319 / 500000000) ≤ -Real.log (244778636919 / 250000000000) ∧
    -Real.log (244778636919 / 250000000000) ≤ (21106639 / 1000000000) := by
  have h := checkLog_sound (w := (5221363081 / 494778636919)) (n := 12)
    (lo := (10553319 / 500000000)) (hi := (21106639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244778636919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244778636919) = 1/(244778636919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9323 : Bounds (-21106639 / 1000000000) (-10553319 / 500000000) (Real.log (244778636919 / 250000000000)) := by
  have h := reflection_log_9323_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9324_neg : (10473329 / 500000000) ≤ -Real.log (1566833919 / 1600000000) ∧
    -Real.log (1566833919 / 1600000000) ≤ (20946659 / 1000000000) := by
  have h := checkLog_sound (w := (33166081 / 3166833919)) (n := 12)
    (lo := (10473329 / 500000000)) (hi := (20946659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1566833919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1566833919) = 1/(1566833919 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9324 : Bounds (-20946659 / 1000000000) (-10473329 / 500000000) (Real.log (1566833919 / 1600000000)) := by
  have h := reflection_log_9324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9325_neg : (289964737 / 1000000000) ≤ -Real.log (500000000000 / 668190181361) ∧
    -Real.log (500000000000 / 668190181361) ≤ (144982369 / 500000000) := by
  have h := checkLog_sound (w := (168190181361 / 1168190181361)) (n := 12)
    (lo := (289964737 / 1000000000)) (hi := (144982369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668190181361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668190181361 / 500000000000) = 1/(500000000000 / 668190181361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9325 : Bounds (289964737 / 1000000000) (144982369 / 500000000) (Real.log (668190181361 / 500000000000)) := by
  have h := reflection_log_9325_neg
  have he : Real.log (668190181361 / 500000000000) = -Real.log (500000000000 / 668190181361) := by
    rw [show ((668190181361 / 500000000000) : ℝ) = ((500000000000 / 668190181361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9326_neg : (291073813 / 1000000000) ≤ -Real.log (500000000000 / 668931666593) ∧
    -Real.log (500000000000 / 668931666593) ≤ (145536907 / 500000000) := by
  have h := checkLog_sound (w := (168931666593 / 1168931666593)) (n := 12)
    (lo := (291073813 / 1000000000)) (hi := (145536907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668931666593 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668931666593 / 500000000000) = 1/(500000000000 / 668931666593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9326 : Bounds (291073813 / 1000000000) (145536907 / 500000000) (Real.log (668931666593 / 500000000000)) := by
  have h := reflection_log_9326_neg
  have he : Real.log (668931666593 / 500000000000) = -Real.log (500000000000 / 668931666593) := by
    rw [show ((668931666593 / 500000000000) : ℝ) = ((500000000000 / 668931666593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9327_neg : (584055317 / 1000000000) ≤ -Real.log (125000000000 / 224162011173) ∧
    -Real.log (125000000000 / 224162011173) ≤ (292027659 / 500000000) := by
  have h := checkLog_sound (w := (99162011173 / 349162011173)) (n := 12)
    (lo := (584055317 / 1000000000)) (hi := (292027659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((224162011173 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(224162011173 / 125000000000) = 1/(125000000000 / 224162011173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9327 : Bounds (584055317 / 1000000000) (292027659 / 500000000) (Real.log (224162011173 / 125000000000)) := by
  have h := reflection_log_9327_neg
  have he : Real.log (224162011173 / 125000000000) = -Real.log (125000000000 / 224162011173) := by
    rw [show ((224162011173 / 125000000000) : ℝ) = ((125000000000 / 224162011173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9328_neg : (585143217 / 1000000000) ≤ -Real.log (250000000000 / 448812019567) ∧
    -Real.log (250000000000 / 448812019567) ≤ (292571609 / 500000000) := by
  have h := checkLog_sound (w := (198812019567 / 698812019567)) (n := 12)
    (lo := (585143217 / 1000000000)) (hi := (292571609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((448812019567 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(448812019567 / 250000000000) = 1/(250000000000 / 448812019567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9328 : Bounds (585143217 / 1000000000) (292571609 / 500000000) (Real.log (448812019567 / 250000000000)) := by
  have h := reflection_log_9328_neg
  have he : Real.log (448812019567 / 250000000000) = -Real.log (250000000000 / 448812019567) := by
    rw [show ((448812019567 / 250000000000) : ℝ) = ((250000000000 / 448812019567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9329_neg : (125379359 / 500000000) ≤ -Real.log (200 / 257) ∧
    -Real.log (200 / 257) ≤ (250758719 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 457)) (n := 12)
    (lo := (125379359 / 500000000)) (hi := (250758719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257 / 200) = 1/(200 / 257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9329 : Bounds (125379359 / 500000000) (250758719 / 1000000000) (Real.log (257 / 200)) := by
  have h := reflection_log_9329_neg
  have he : Real.log (257 / 200) = -Real.log (200 / 257) := by
    rw [show ((257 / 200) : ℝ) = ((200 / 257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9330_neg : (10483523 / 31250000) ≤ -Real.log (143 / 200) ∧
    -Real.log (143 / 200) ≤ (335472737 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 343)) (n := 12)
    (lo := (10483523 / 31250000)) (hi := (335472737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 143) = 1/(143 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9330 : Bounds (-335472737 / 1000000000) (-10483523 / 31250000) (Real.log (143 / 200)) := by
  have h := reflection_log_9330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9331_neg : (284959 / 1000000000) ≤ -Real.log (200000 / 200057) ∧
    -Real.log (200000 / 200057) ≤ (1781 / 6250000) := by
  have h := checkLog_sound (w := (57 / 400057)) (n := 12)
    (lo := (284959 / 1000000000)) (hi := (1781 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200057 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200057 / 200000) = 1/(200000 / 200057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9331 : Bounds (284959 / 1000000000) (1781 / 6250000) (Real.log (200057 / 200000)) := by
  have h := reflection_log_9331_neg
  have he : Real.log (200057 / 200000) = -Real.log (200000 / 200057) := by
    rw [show ((200057 / 200000) : ℝ) = ((200000 / 200057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9332_neg : (3563 / 12500000) ≤ -Real.log (199943 / 200000) ∧
    -Real.log (199943 / 200000) ≤ (285041 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 399943)) (n := 12)
    (lo := (3563 / 12500000)) (hi := (285041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199943) = 1/(199943 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9332 : Bounds (-285041 / 1000000000) (-3563 / 12500000) (Real.log (199943 / 200000)) := by
  have h := reflection_log_9332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9333_neg : (134738039 / 1000000000) ≤ -Real.log (1000000 / 1144237) ∧
    -Real.log (1000000 / 1144237) ≤ (3368451 / 25000000) := by
  have h := checkLog_sound (w := (144237 / 2144237)) (n := 12)
    (lo := (134738039 / 1000000000)) (hi := (3368451 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1144237 / 1000000) = 1/(1000000 / 1144237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9333 : Bounds (134738039 / 1000000000) (3368451 / 25000000) (Real.log (1144237 / 1000000)) := by
  have h := reflection_log_9333_neg
  have he : Real.log (1144237 / 1000000) = -Real.log (1000000 / 1144237) := by
    rw [show ((1144237 / 1000000) : ℝ) = ((1000000 / 1144237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9334_neg : (15576181 / 100000000) ≤ -Real.log (855763 / 1000000) ∧
    -Real.log (855763 / 1000000) ≤ (155761811 / 1000000000) := by
  have h := checkLog_sound (w := (144237 / 1855763)) (n := 12)
    (lo := (15576181 / 100000000)) (hi := (155761811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 855763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 855763) = 1/(855763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9334 : Bounds (-155761811 / 1000000000) (-15576181 / 100000000) (Real.log (855763 / 1000000)) := by
  have h := reflection_log_9334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9335_neg : (27042321 / 200000000) ≤ -Real.log (1000000 / 1144779) ∧
    -Real.log (1000000 / 1144779) ≤ (67605803 / 500000000) := by
  have h := checkLog_sound (w := (144779 / 2144779)) (n := 12)
    (lo := (27042321 / 200000000)) (hi := (67605803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1144779 / 1000000) = 1/(1000000 / 1144779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9335 : Bounds (27042321 / 200000000) (67605803 / 500000000) (Real.log (1144779 / 1000000)) := by
  have h := reflection_log_9335_neg
  have he : Real.log (1144779 / 1000000) = -Real.log (1000000 / 1144779) := by
    rw [show ((1144779 / 1000000) : ℝ) = ((1000000 / 1144779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9336_neg : (156395363 / 1000000000) ≤ -Real.log (855221 / 1000000) ∧
    -Real.log (855221 / 1000000) ≤ (39098841 / 250000000) := by
  have h := checkLog_sound (w := (144779 / 1855221)) (n := 12)
    (lo := (156395363 / 1000000000)) (hi := (39098841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 855221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 855221) = 1/(855221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9336 : Bounds (-39098841 / 250000000) (-156395363 / 1000000000) (Real.log (855221 / 1000000)) := by
  have h := reflection_log_9336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9337_neg : (10591879 / 500000000) ≤ -Real.log (979039041159 / 1000000000000) ∧
    -Real.log (979039041159 / 1000000000000) ≤ (21183759 / 1000000000) := by
  have h := checkLog_sound (w := (20960958841 / 1979039041159)) (n := 12)
    (lo := (10591879 / 500000000)) (hi := (21183759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979039041159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979039041159) = 1/(979039041159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9337 : Bounds (-21183759 / 1000000000) (-10591879 / 500000000) (Real.log (979039041159 / 1000000000000)) := by
  have h := reflection_log_9337_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9338_neg : (21023771 / 1000000000) ≤ -Real.log (979195687831 / 1000000000000) ∧
    -Real.log (979195687831 / 1000000000000) ≤ (5255943 / 250000000) := by
  have h := checkLog_sound (w := (20804312169 / 1979195687831)) (n := 12)
    (lo := (21023771 / 1000000000)) (hi := (5255943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979195687831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979195687831) = 1/(979195687831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9338 : Bounds (-5255943 / 250000000) (-21023771 / 1000000000) (Real.log (979195687831 / 1000000000000)) := by
  have h := reflection_log_9338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9339_neg : (290499849 / 1000000000) ≤ -Real.log (500000000000 / 668547833921) ∧
    -Real.log (500000000000 / 668547833921) ≤ (5809997 / 20000000) := by
  have h := checkLog_sound (w := (168547833921 / 1168547833921)) (n := 12)
    (lo := (290499849 / 1000000000)) (hi := (5809997 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668547833921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668547833921 / 500000000000) = 1/(500000000000 / 668547833921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9339 : Bounds (290499849 / 1000000000) (5809997 / 20000000) (Real.log (668547833921 / 500000000000)) := by
  have h := reflection_log_9339_neg
  have he : Real.log (668547833921 / 500000000000) = -Real.log (500000000000 / 668547833921) := by
    rw [show ((668547833921 / 500000000000) : ℝ) = ((500000000000 / 668547833921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9340_neg : (291606969 / 1000000000) ≤ -Real.log (100000000000 / 133857681231) ∧
    -Real.log (100000000000 / 133857681231) ≤ (29160697 / 100000000) := by
  have h := checkLog_sound (w := (33857681231 / 233857681231)) (n := 12)
    (lo := (291606969 / 1000000000)) (hi := (29160697 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133857681231 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133857681231 / 100000000000) = 1/(100000000000 / 133857681231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9340 : Bounds (291606969 / 1000000000) (29160697 / 100000000) (Real.log (133857681231 / 100000000000)) := by
  have h := reflection_log_9340_neg
  have he : Real.log (133857681231 / 100000000000) = -Real.log (100000000000 / 133857681231) := by
    rw [show ((133857681231 / 100000000000) : ℝ) = ((100000000000 / 133857681231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9341_neg : (585143217 / 1000000000) ≤ -Real.log (500000000000 / 897624039133) ∧
    -Real.log (500000000000 / 897624039133) ≤ (292571609 / 500000000) := by
  have h := checkLog_sound (w := (397624039133 / 1397624039133)) (n := 12)
    (lo := (585143217 / 1000000000)) (hi := (292571609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897624039133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897624039133 / 500000000000) = 1/(500000000000 / 897624039133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9341 : Bounds (585143217 / 1000000000) (292571609 / 500000000) (Real.log (897624039133 / 500000000000)) := by
  have h := reflection_log_9341_neg
  have he : Real.log (897624039133 / 500000000000) = -Real.log (500000000000 / 897624039133) := by
    rw [show ((897624039133 / 500000000000) : ℝ) = ((500000000000 / 897624039133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9342_neg : (293115727 / 500000000) ≤ -Real.log (250000000000 / 449300699301) ∧
    -Real.log (250000000000 / 449300699301) ≤ (117246291 / 200000000) := by
  have h := checkLog_sound (w := (199300699301 / 699300699301)) (n := 12)
    (lo := (293115727 / 500000000)) (hi := (117246291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449300699301 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449300699301 / 250000000000) = 1/(250000000000 / 449300699301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9342 : Bounds (293115727 / 500000000) (117246291 / 200000000) (Real.log (449300699301 / 250000000000)) := by
  have h := reflection_log_9342_neg
  have he : Real.log (449300699301 / 250000000000) = -Real.log (250000000000 / 449300699301) := by
    rw [show ((449300699301 / 250000000000) : ℝ) = ((250000000000 / 449300699301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9343_neg : (251147747 / 1000000000) ≤ -Real.log (2000 / 2571) ∧
    -Real.log (2000 / 2571) ≤ (62786937 / 250000000) := by
  have h := checkLog_sound (w := (571 / 4571)) (n := 12)
    (lo := (251147747 / 1000000000)) (hi := (62786937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2571 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2571 / 2000) = 1/(2000 / 2571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9343 : Bounds (251147747 / 1000000000) (62786937 / 250000000) (Real.log (2571 / 2000)) := by
  have h := reflection_log_9343_neg
  have he : Real.log (2571 / 2000) = -Real.log (2000 / 2571) := by
    rw [show ((2571 / 2000) : ℝ) = ((2000 / 2571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


