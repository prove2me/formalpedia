-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0241__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0241__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T22:06:42.054354+00:00
-- url     : https://prove2.me/theorems/16b7710d-3581-44f1-9283-2667bbef6961
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0241 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0242, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0241 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0242, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0243)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0241 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0242, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0243)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0241 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0242, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0243) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0241 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0242, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0243).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0241 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15424_neg : (2510342813 / 500000000) ≤ -Real.log (33 / 5000) ∧
    -Real.log (33 / 5000) ≤ (2510342817 / 500000000) := by
  have h := checkLog_sound (w := (97 / 1153)) (n := 12)
    (lo := (84327683 / 500000000)) (hi := (168655367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 528) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 528) = 1/(33 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15424 : Bounds (-2510342817 / 500000000) (-2510342813 / 500000000) (Real.log (33 / 5000)) := by
  have h := reflection_log_15424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15425_neg : (496453 / 500000000) ≤ -Real.log (5000000 / 5004967) ∧
    -Real.log (5000000 / 5004967) ≤ (992907 / 1000000000) := by
  have h := checkLog_sound (w := (4967 / 10004967)) (n := 12)
    (lo := (496453 / 500000000)) (hi := (992907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004967 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004967 / 5000000) = 1/(5000000 / 5004967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15425 : Bounds (496453 / 500000000) (992907 / 1000000000) (Real.log (5004967 / 5000000)) := by
  have h := reflection_log_15425_neg
  have he : Real.log (5004967 / 5000000) = -Real.log (5000000 / 5004967) := by
    rw [show ((5004967 / 5000000) : ℝ) = ((5000000 / 5004967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15426_neg : (993893 / 1000000000) ≤ -Real.log (4995033 / 5000000) ∧
    -Real.log (4995033 / 5000000) ≤ (496947 / 500000000) := by
  have h := checkLog_sound (w := (4967 / 9995033)) (n := 12)
    (lo := (993893 / 1000000000)) (hi := (496947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995033) = 1/(4995033 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15426 : Bounds (-496947 / 500000000) (-993893 / 1000000000) (Real.log (4995033 / 5000000)) := by
  have h := reflection_log_15426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15427_neg : (498645749 / 1000000000) ≤ -Real.log (100000 / 164649) ∧
    -Real.log (100000 / 164649) ≤ (1994583 / 4000000) := by
  have h := checkLog_sound (w := (64649 / 264649)) (n := 12)
    (lo := (498645749 / 1000000000)) (hi := (1994583 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164649 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164649 / 100000) = 1/(100000 / 164649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15427 : Bounds (498645749 / 1000000000) (1994583 / 4000000) (Real.log (164649 / 100000)) := by
  have h := reflection_log_15427_neg
  have he : Real.log (164649 / 100000) = -Real.log (100000 / 164649) := by
    rw [show ((164649 / 100000) : ℝ) = ((100000 / 164649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15428_neg : (64990219 / 62500000) ≤ -Real.log (35351 / 100000) ∧
    -Real.log (35351 / 100000) ≤ (519921753 / 500000000) := by
  have h := checkLog_sound (w := (14649 / 85351)) (n := 12)
    (lo := (86674081 / 250000000)) (hi := (13867853 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35351) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35351) = 1/(35351 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15428 : Bounds (-519921753 / 500000000) (-64990219 / 62500000) (Real.log (35351 / 100000)) := by
  have h := reflection_log_15428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15429_neg : (49921589 / 100000000) ≤ -Real.log (1000000 / 1647429) ∧
    -Real.log (1000000 / 1647429) ≤ (499215891 / 1000000000) := by
  have h := checkLog_sound (w := (647429 / 2647429)) (n := 12)
    (lo := (49921589 / 100000000)) (hi := (499215891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647429 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647429 / 1000000) = 1/(1000000 / 1647429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15429 : Bounds (49921589 / 100000000) (499215891 / 1000000000) (Real.log (1647429 / 1000000)) := by
  have h := reflection_log_15429_neg
  have he : Real.log (1647429 / 1000000) = -Real.log (1000000 / 1647429) := by
    rw [show ((1647429 / 1000000) : ℝ) = ((1000000 / 1647429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15430_neg : (521251629 / 500000000) ≤ -Real.log (352571 / 1000000) ∧
    -Real.log (352571 / 1000000) ≤ (52125163 / 50000000) := by
  have h := checkLog_sound (w := (147429 / 852571)) (n := 12)
    (lo := (174678039 / 500000000)) (hi := (349356079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352571) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 352571) = 1/(352571 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15430 : Bounds (-52125163 / 50000000) (-521251629 / 500000000) (Real.log (352571 / 1000000)) := by
  have h := reflection_log_15430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15431_neg : (543287367 / 1000000000) ≤ -Real.log (580835689959 / 1000000000000) ∧
    -Real.log (580835689959 / 1000000000000) ≤ (67910921 / 125000000) := by
  have h := checkLog_sound (w := (419164310041 / 1580835689959)) (n := 12)
    (lo := (543287367 / 1000000000)) (hi := (67910921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 580835689959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 580835689959) = 1/(580835689959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15431 : Bounds (-67910921 / 125000000) (-543287367 / 1000000000) (Real.log (580835689959 / 1000000000000)) := by
  have h := reflection_log_15431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15432_neg : (135299439 / 250000000) ≤ -Real.log (5820506799 / 10000000000) ∧
    -Real.log (5820506799 / 10000000000) ≤ (541197757 / 1000000000) := by
  have h := checkLog_sound (w := (4179493201 / 15820506799)) (n := 12)
    (lo := (135299439 / 250000000)) (hi := (541197757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5820506799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5820506799) = 1/(5820506799 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15432 : Bounds (-541197757 / 1000000000) (-135299439 / 250000000) (Real.log (5820506799 / 10000000000)) := by
  have h := reflection_log_15432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15433_neg : (1538489253 / 1000000000) ≤ -Real.log (500000000000 / 2328774292099) ∧
    -Real.log (500000000000 / 2328774292099) ≤ (192311157 / 125000000) := by
  have h := checkLog_sound (w := (328774292099 / 4328774292099)) (n := 12)
    (lo := (152194893 / 1000000000)) (hi := (76097447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2328774292099 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2328774292099 / 2000000000000) = 1/(500000000000 / 2328774292099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15433 : Bounds (1538489253 / 1000000000) (192311157 / 125000000) (Real.log (2328774292099 / 500000000000)) := by
  have h := reflection_log_15433_neg
  have he : Real.log (2328774292099 / 500000000000) = -Real.log (500000000000 / 2328774292099) := by
    rw [show ((2328774292099 / 500000000000) : ℝ) = ((500000000000 / 2328774292099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15434_neg : (385429787 / 250000000) ≤ -Real.log (500000000000 / 2336308147863) ∧
    -Real.log (500000000000 / 2336308147863) ≤ (1541719151 / 1000000000) := by
  have h := checkLog_sound (w := (336308147863 / 4336308147863)) (n := 12)
    (lo := (38856197 / 250000000)) (hi := (155424789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2336308147863 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2336308147863 / 2000000000000) = 1/(500000000000 / 2336308147863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15434 : Bounds (385429787 / 250000000) (1541719151 / 1000000000) (Real.log (2336308147863 / 500000000000)) := by
  have h := reflection_log_15434_neg
  have he : Real.log (2336308147863 / 500000000000) = -Real.log (500000000000 / 2336308147863) := by
    rw [show ((2336308147863 / 500000000000) : ℝ) = ((500000000000 / 2336308147863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15435_neg : (5680574049 / 1000000000) ≤ -Real.log (500000000000 / 146558823529411) ∧
    -Real.log (500000000000 / 146558823529411) ≤ (2840287029 / 500000000) := by
  have h := checkLog_sound (w := (18558823529411 / 274558823529411)) (n := 12)
    (lo := (135396609 / 1000000000)) (hi := (13539661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146558823529411 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(146558823529411 / 128000000000000) = 1/(500000000000 / 146558823529411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15435 : Bounds (5680574049 / 1000000000) (2840287029 / 500000000) (Real.log (146558823529411 / 500000000000)) := by
  have h := reflection_log_15435_neg
  have he : Real.log (146558823529411 / 500000000000) = -Real.log (500000000000 / 146558823529411) := by
    rw [show ((146558823529411 / 500000000000) : ℝ) = ((500000000000 / 146558823529411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15436_neg : (5710527349 / 1000000000) ≤ -Real.log (31250000000 / 9438446969697) ∧
    -Real.log (31250000000 / 9438446969697) ≤ (2855263679 / 500000000) := by
  have h := checkLog_sound (w := (1438446969697 / 17438446969697)) (n := 12)
    (lo := (165349909 / 1000000000)) (hi := (16534991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9438446969697 / 8000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(9438446969697 / 8000000000000) = 1/(31250000000 / 9438446969697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15436 : Bounds (5710527349 / 1000000000) (2855263679 / 500000000) (Real.log (9438446969697 / 31250000000)) := by
  have h := reflection_log_15436_neg
  have he : Real.log (9438446969697 / 31250000000) = -Real.log (31250000000 / 9438446969697) := by
    rw [show ((9438446969697 / 31250000000) : ℝ) = ((31250000000 / 9438446969697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15437_neg : (689942049 / 1000000000) ≤ -Real.log (625 / 1246) ∧
    -Real.log (625 / 1246) ≤ (13798841 / 20000000) := by
  have h := checkLog_sound (w := (621 / 1871)) (n := 12)
    (lo := (689942049 / 1000000000)) (hi := (13798841 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246 / 625) = 1/(625 / 1246) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15437 : Bounds (689942049 / 1000000000) (13798841 / 20000000) (Real.log (1246 / 625)) := by
  have h := reflection_log_15437_neg
  have he : Real.log (1246 / 625) = -Real.log (625 / 1246) := by
    rw [show ((1246 / 625) : ℝ) = ((625 / 1246) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15438_neg : (1262864321 / 250000000) ≤ -Real.log (4 / 625) ∧
    -Real.log (4 / 625) ≤ (1262864323 / 250000000) := by
  have h := checkLog_sound (w := (113 / 1137)) (n := 12)
    (lo := (12464189 / 62500000)) (hi := (7977081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 512) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 512) = 1/(4 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15438 : Bounds (-1262864323 / 250000000) (-1262864321 / 250000000) (Real.log (4 / 625)) := by
  have h := reflection_log_15438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15439_neg : (496553 / 500000000) ≤ -Real.log (625000 / 625621) ∧
    -Real.log (625000 / 625621) ≤ (993107 / 1000000000) := by
  have h := checkLog_sound (w := (621 / 1250621)) (n := 12)
    (lo := (496553 / 500000000)) (hi := (993107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625621 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625621 / 625000) = 1/(625000 / 625621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15439 : Bounds (496553 / 500000000) (993107 / 1000000000) (Real.log (625621 / 625000)) := by
  have h := reflection_log_15439_neg
  have he : Real.log (625621 / 625000) = -Real.log (625000 / 625621) := by
    rw [show ((625621 / 625000) : ℝ) = ((625000 / 625621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15440_neg : (994093 / 1000000000) ≤ -Real.log (624379 / 625000) ∧
    -Real.log (624379 / 625000) ≤ (497047 / 500000000) := by
  have h := checkLog_sound (w := (621 / 1249379)) (n := 12)
    (lo := (994093 / 1000000000)) (hi := (497047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624379) = 1/(624379 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15440 : Bounds (-497047 / 500000000) (-994093 / 1000000000) (Real.log (624379 / 625000)) := by
  have h := reflection_log_15440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15441_neg : (19953409 / 40000000) ≤ -Real.log (500000 / 823401) ∧
    -Real.log (500000 / 823401) ≤ (249417613 / 500000000) := by
  have h := checkLog_sound (w := (323401 / 1323401)) (n := 12)
    (lo := (19953409 / 40000000)) (hi := (249417613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823401 / 500000) = 1/(500000 / 823401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15441 : Bounds (19953409 / 40000000) (249417613 / 500000000) (Real.log (823401 / 500000)) := by
  have h := reflection_log_15441_neg
  have he : Real.log (823401 / 500000) = -Real.log (500000 / 823401) := by
    rw [show ((823401 / 500000) : ℝ) = ((500000 / 823401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15442_neg : (130090809 / 125000000) ≤ -Real.log (176599 / 500000) ∧
    -Real.log (176599 / 500000) ≤ (520363237 / 500000000) := by
  have h := checkLog_sound (w := (73401 / 426599)) (n := 12)
    (lo := (86894823 / 250000000)) (hi := (347579293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176599) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 176599) = 1/(176599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15442 : Bounds (-520363237 / 500000000) (-130090809 / 125000000) (Real.log (176599 / 500000)) := by
  have h := reflection_log_15442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15443_neg : (99881173 / 200000000) ≤ -Real.log (500000 / 823871) ∧
    -Real.log (500000 / 823871) ≤ (249702933 / 500000000) := by
  have h := checkLog_sound (w := (323871 / 1323871)) (n := 12)
    (lo := (99881173 / 200000000)) (hi := (249702933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823871 / 500000) = 1/(500000 / 823871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15443 : Bounds (99881173 / 200000000) (249702933 / 500000000) (Real.log (823871 / 500000)) := by
  have h := reflection_log_15443_neg
  have he : Real.log (823871 / 500000) = -Real.log (500000 / 823871) := by
    rw [show ((823871 / 500000) : ℝ) = ((500000 / 823871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15444_neg : (130423927 / 125000000) ≤ -Real.log (176129 / 500000) ∧
    -Real.log (176129 / 500000) ≤ (521695709 / 500000000) := by
  have h := checkLog_sound (w := (73871 / 426129)) (n := 12)
    (lo := (87561059 / 250000000)) (hi := (350244237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176129) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 176129) = 1/(176129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15444 : Bounds (-521695709 / 500000000) (-130423927 / 125000000) (Real.log (176129 / 500000)) := by
  have h := reflection_log_15444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15445_neg : (543985551 / 1000000000) ≤ -Real.log (145107575359 / 250000000000) ∧
    -Real.log (145107575359 / 250000000000) ≤ (33999097 / 62500000) := by
  have h := checkLog_sound (w := (104892424641 / 395107575359)) (n := 12)
    (lo := (543985551 / 1000000000)) (hi := (33999097 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145107575359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145107575359) = 1/(145107575359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15445 : Bounds (-33999097 / 62500000) (-543985551 / 1000000000) (Real.log (145107575359 / 250000000000)) := by
  have h := reflection_log_15445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15446_neg : (541891247 / 1000000000) ≤ -Real.log (145411793199 / 250000000000) ∧
    -Real.log (145411793199 / 250000000000) ≤ (33868203 / 62500000) := by
  have h := checkLog_sound (w := (104588206801 / 395411793199)) (n := 12)
    (lo := (541891247 / 1000000000)) (hi := (33868203 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145411793199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145411793199) = 1/(145411793199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15446 : Bounds (-33868203 / 62500000) (-541891247 / 1000000000) (Real.log (145411793199 / 250000000000)) := by
  have h := reflection_log_15446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15447_neg : (1539561697 / 1000000000) ≤ -Real.log (250000000000 / 1165636555133) ∧
    -Real.log (250000000000 / 1165636555133) ≤ (15395617 / 10000000) := by
  have h := checkLog_sound (w := (165636555133 / 2165636555133)) (n := 12)
    (lo := (153267337 / 1000000000)) (hi := (76633669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1165636555133 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1165636555133 / 1000000000000) = 1/(250000000000 / 1165636555133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15447 : Bounds (1539561697 / 1000000000) (15395617 / 10000000) (Real.log (1165636555133 / 250000000000)) := by
  have h := reflection_log_15447_neg
  have he : Real.log (1165636555133 / 250000000000) = -Real.log (250000000000 / 1165636555133) := by
    rw [show ((1165636555133 / 250000000000) : ℝ) = ((250000000000 / 1165636555133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15448_neg : (771398641 / 500000000) ≤ -Real.log (12500000000 / 58470708969) ∧
    -Real.log (12500000000 / 58470708969) ≤ (308559457 / 200000000) := by
  have h := checkLog_sound (w := (8470708969 / 108470708969)) (n := 12)
    (lo := (78251461 / 500000000)) (hi := (156502923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58470708969 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(58470708969 / 50000000000) = 1/(12500000000 / 58470708969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15448 : Bounds (771398641 / 500000000) (308559457 / 200000000) (Real.log (58470708969 / 12500000000)) := by
  have h := reflection_log_15448_neg
  have he : Real.log (58470708969 / 12500000000) = -Real.log (12500000000 / 58470708969) := by
    rw [show ((58470708969 / 12500000000) : ℝ) = ((12500000000 / 58470708969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15449_neg : (5710527349 / 1000000000) ≤ -Real.log (500000000000 / 151015151515151) ∧
    -Real.log (500000000000 / 151015151515151) ≤ (2855263679 / 500000000) := by
  have h := checkLog_sound (w := (23015151515151 / 279015151515151)) (n := 12)
    (lo := (165349909 / 1000000000)) (hi := (16534991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151015151515151 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(151015151515151 / 128000000000000) = 1/(500000000000 / 151015151515151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15449 : Bounds (5710527349 / 1000000000) (2855263679 / 500000000) (Real.log (151015151515151 / 500000000000)) := by
  have h := reflection_log_15449_neg
  have he : Real.log (151015151515151 / 500000000000) = -Real.log (500000000000 / 151015151515151) := by
    rw [show ((151015151515151 / 500000000000) : ℝ) = ((500000000000 / 151015151515151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15450_neg : (5741399333 / 1000000000) ≤ -Real.log (2 / 623) ∧
    -Real.log (2 / 623) ≤ (2870699671 / 500000000) := by
  have h := checkLog_sound (w := (111 / 1135)) (n := 12)
    (lo := (196221893 / 1000000000)) (hi := (98110947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623 / 512) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(623 / 512) = 1/(2 / 623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15450 : Bounds (5741399333 / 1000000000) (2870699671 / 500000000) (Real.log (623 / 2)) := by
  have h := reflection_log_15450_neg
  have he : Real.log (623 / 2) = -Real.log (2 / 623) := by
    rw [show ((623 / 2) : ℝ) = ((2 / 623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15451_neg : (138008473 / 200000000) ≤ -Real.log (5000 / 9969) ∧
    -Real.log (5000 / 9969) ≤ (345021183 / 500000000) := by
  have h := checkLog_sound (w := (4969 / 14969)) (n := 12)
    (lo := (138008473 / 200000000)) (hi := (345021183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9969 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9969 / 5000) = 1/(5000 / 9969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15451 : Bounds (138008473 / 200000000) (345021183 / 500000000) (Real.log (9969 / 5000)) := by
  have h := reflection_log_15451_neg
  have he : Real.log (9969 / 5000) = -Real.log (5000 / 9969) := by
    rw [show ((9969 / 5000) : ℝ) = ((5000 / 9969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15452_neg : (5083205983 / 1000000000) ≤ -Real.log (31 / 5000) ∧
    -Real.log (31 / 5000) ≤ (5083205991 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 1121)) (n := 12)
    (lo := (231175723 / 1000000000)) (hi := (57793931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 496) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 496) = 1/(31 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15452 : Bounds (-5083205991 / 1000000000) (-5083205983 / 1000000000) (Real.log (31 / 5000)) := by
  have h := reflection_log_15452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15453_neg : (496653 / 500000000) ≤ -Real.log (5000000 / 5004969) ∧
    -Real.log (5000000 / 5004969) ≤ (993307 / 1000000000) := by
  have h := checkLog_sound (w := (4969 / 10004969)) (n := 12)
    (lo := (496653 / 500000000)) (hi := (993307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004969 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004969 / 5000000) = 1/(5000000 / 5004969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15453 : Bounds (496653 / 500000000) (993307 / 1000000000) (Real.log (5004969 / 5000000)) := by
  have h := reflection_log_15453_neg
  have he : Real.log (5004969 / 5000000) = -Real.log (5000000 / 5004969) := by
    rw [show ((5004969 / 5000000) : ℝ) = ((5000000 / 5004969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15454_neg : (497147 / 500000000) ≤ -Real.log (4995031 / 5000000) ∧
    -Real.log (4995031 / 5000000) ≤ (198859 / 200000000) := by
  have h := checkLog_sound (w := (4969 / 9995031)) (n := 12)
    (lo := (497147 / 500000000)) (hi := (198859 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995031) = 1/(4995031 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15454 : Bounds (-198859 / 200000000) (-497147 / 500000000) (Real.log (4995031 / 5000000)) := by
  have h := reflection_log_15454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15455_neg : (499025879 / 1000000000) ≤ -Real.log (250000 / 411779) ∧
    -Real.log (250000 / 411779) ≤ (12475647 / 25000000) := by
  have h := checkLog_sound (w := (161779 / 661779)) (n := 12)
    (lo := (499025879 / 1000000000)) (hi := (12475647 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411779 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411779 / 250000) = 1/(250000 / 411779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15455 : Bounds (499025879 / 1000000000) (12475647 / 25000000) (Real.log (411779 / 250000)) := by
  have h := reflection_log_15455_neg
  have he : Real.log (411779 / 250000) = -Real.log (250000 / 411779) := by
    rw [show ((411779 / 250000) : ℝ) = ((250000 / 411779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15456_neg : (1041615887 / 1000000000) ≤ -Real.log (88221 / 250000) ∧
    -Real.log (88221 / 250000) ≤ (1041615889 / 1000000000) := by
  have h := checkLog_sound (w := (36779 / 213221)) (n := 12)
    (lo := (348468707 / 1000000000)) (hi := (87117177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 88221) = 1/(88221 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15456 : Bounds (-1041615889 / 1000000000) (-1041615887 / 1000000000) (Real.log (88221 / 250000)) := by
  have h := reflection_log_15456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15457_neg : (249798509 / 500000000) ≤ -Real.log (1000000 / 1648057) ∧
    -Real.log (1000000 / 1648057) ≤ (499597019 / 1000000000) := by
  have h := checkLog_sound (w := (648057 / 2648057)) (n := 12)
    (lo := (249798509 / 500000000)) (hi := (499597019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1648057 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1648057 / 1000000) = 1/(1000000 / 1648057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15457 : Bounds (249798509 / 500000000) (499597019 / 1000000000) (Real.log (1648057 / 1000000)) := by
  have h := reflection_log_15457_neg
  have he : Real.log (1648057 / 1000000) = -Real.log (1000000 / 1648057) := by
    rw [show ((1648057 / 1000000) : ℝ) = ((1000000 / 1648057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15458_neg : (1044286047 / 1000000000) ≤ -Real.log (351943 / 1000000) ∧
    -Real.log (351943 / 1000000) ≤ (1044286049 / 1000000000) := by
  have h := checkLog_sound (w := (148057 / 851943)) (n := 12)
    (lo := (351138867 / 1000000000)) (hi := (87784717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351943) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 351943) = 1/(351943 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15458 : Bounds (-1044286049 / 1000000000) (-1044286047 / 1000000000) (Real.log (351943 / 1000000)) := by
  have h := reflection_log_15458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15459_neg : (54468903 / 100000000) ≤ -Real.log (580022124751 / 1000000000000) ∧
    -Real.log (580022124751 / 1000000000000) ≤ (544689031 / 1000000000) := by
  have h := checkLog_sound (w := (419977875249 / 1580022124751)) (n := 12)
    (lo := (54468903 / 100000000)) (hi := (544689031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 580022124751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 580022124751) = 1/(580022124751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15459 : Bounds (-544689031 / 1000000000) (-54468903 / 100000000) (Real.log (580022124751 / 1000000000000)) := by
  have h := reflection_log_15459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15460_neg : (67823751 / 125000000) ≤ -Real.log (36327555159 / 62500000000) ∧
    -Real.log (36327555159 / 62500000000) ≤ (542590009 / 1000000000) := by
  have h := checkLog_sound (w := (26172444841 / 98827555159)) (n := 12)
    (lo := (67823751 / 125000000)) (hi := (542590009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36327555159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36327555159) = 1/(36327555159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15460 : Bounds (-542590009 / 1000000000) (-67823751 / 125000000) (Real.log (36327555159 / 62500000000)) := by
  have h := reflection_log_15460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15461_neg : (770320883 / 500000000) ≤ -Real.log (500000000000 / 2333792407703) ∧
    -Real.log (500000000000 / 2333792407703) ≤ (1540641769 / 1000000000) := by
  have h := checkLog_sound (w := (333792407703 / 4333792407703)) (n := 12)
    (lo := (77173703 / 500000000)) (hi := (154347407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2333792407703 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2333792407703 / 2000000000000) = 1/(500000000000 / 2333792407703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15461 : Bounds (770320883 / 500000000) (1540641769 / 1000000000) (Real.log (2333792407703 / 500000000000)) := by
  have h := reflection_log_15461_neg
  have he : Real.log (2333792407703 / 500000000000) = -Real.log (500000000000 / 2333792407703) := by
    rw [show ((2333792407703 / 500000000000) : ℝ) = ((500000000000 / 2333792407703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15462_neg : (308776613 / 200000000) ≤ -Real.log (50000000000 / 234136919899) ∧
    -Real.log (50000000000 / 234136919899) ≤ (385970767 / 250000000) := by
  have h := checkLog_sound (w := (34136919899 / 434136919899)) (n := 12)
    (lo := (31517741 / 200000000)) (hi := (78794353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234136919899 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(234136919899 / 200000000000) = 1/(50000000000 / 234136919899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15462 : Bounds (308776613 / 200000000) (385970767 / 250000000) (Real.log (234136919899 / 50000000000)) := by
  have h := reflection_log_15462_neg
  have he : Real.log (234136919899 / 50000000000) = -Real.log (50000000000 / 234136919899) := by
    rw [show ((234136919899 / 50000000000) : ℝ) = ((50000000000 / 234136919899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15463_neg : (1443312087 / 250000000) ≤ -Real.log (250000000000 / 80395161290323) ∧
    -Real.log (250000000000 / 80395161290323) ≤ (5773248357 / 1000000000) := by
  have h := checkLog_sound (w := (16395161290323 / 144395161290323)) (n := 12)
    (lo := (57017727 / 250000000)) (hi := (228070909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80395161290323 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(80395161290323 / 64000000000000) = 1/(250000000000 / 80395161290323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15463 : Bounds (1443312087 / 250000000) (5773248357 / 1000000000) (Real.log (80395161290323 / 250000000000)) := by
  have h := reflection_log_15463_neg
  have he : Real.log (80395161290323 / 250000000000) = -Real.log (250000000000 / 80395161290323) := by
    rw [show ((80395161290323 / 250000000000) : ℝ) = ((250000000000 / 80395161290323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15464_neg : (690142671 / 1000000000) ≤ -Real.log (500 / 997) ∧
    -Real.log (500 / 997) ≤ (43133917 / 62500000) := by
  have h := checkLog_sound (w := (497 / 1497)) (n := 12)
    (lo := (690142671 / 1000000000)) (hi := (43133917 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997 / 500) = 1/(500 / 997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15464 : Bounds (690142671 / 1000000000) (43133917 / 62500000) (Real.log (997 / 500)) := by
  have h := reflection_log_15464_neg
  have he : Real.log (997 / 500) = -Real.log (500 / 997) := by
    rw [show ((997 / 500) : ℝ) = ((500 / 997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15465_neg : (1023199161 / 200000000) ≤ -Real.log (3 / 500) ∧
    -Real.log (3 / 500) ≤ (5115995813 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(125 / 96) = 1/(3 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15465 : Bounds (-5115995813 / 1000000000) (-1023199161 / 200000000) (Real.log (3 / 500)) := by
  have h := reflection_log_15465_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15466_neg : (496753 / 500000000) ≤ -Real.log (500000 / 500497) ∧
    -Real.log (500000 / 500497) ≤ (993507 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 1000497)) (n := 12)
    (lo := (496753 / 500000000)) (hi := (993507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500497 / 500000) = 1/(500000 / 500497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15466 : Bounds (496753 / 500000000) (993507 / 1000000000) (Real.log (500497 / 500000)) := by
  have h := reflection_log_15466_neg
  have he : Real.log (500497 / 500000) = -Real.log (500000 / 500497) := by
    rw [show ((500497 / 500000) : ℝ) = ((500000 / 500497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15467_neg : (497247 / 500000000) ≤ -Real.log (499503 / 500000) ∧
    -Real.log (499503 / 500000) ≤ (198899 / 200000000) := by
  have h := checkLog_sound (w := (497 / 999503)) (n := 12)
    (lo := (497247 / 500000000)) (hi := (198899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499503) = 1/(499503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15467 : Bounds (-198899 / 200000000) (-497247 / 500000000) (Real.log (499503 / 500000)) := by
  have h := reflection_log_15467_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15468_neg : (499216497 / 1000000000) ≤ -Real.log (100000 / 164743) ∧
    -Real.log (100000 / 164743) ≤ (249608249 / 500000000) := by
  have h := checkLog_sound (w := (64743 / 264743)) (n := 12)
    (lo := (499216497 / 1000000000)) (hi := (249608249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164743 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164743 / 100000) = 1/(100000 / 164743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15468 : Bounds (499216497 / 1000000000) (249608249 / 500000000) (Real.log (164743 / 100000)) := by
  have h := reflection_log_15468_neg
  have he : Real.log (164743 / 100000) = -Real.log (100000 / 164743) := by
    rw [show ((164743 / 100000) : ℝ) = ((100000 / 164743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15469_neg : (521253047 / 500000000) ≤ -Real.log (35257 / 100000) ∧
    -Real.log (35257 / 100000) ≤ (65156631 / 62500000) := by
  have h := checkLog_sound (w := (14743 / 85257)) (n := 12)
    (lo := (174679457 / 500000000)) (hi := (69871783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35257) = 1/(35257 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15469 : Bounds (-65156631 / 62500000) (-521253047 / 500000000) (Real.log (35257 / 100000)) := by
  have h := reflection_log_15469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15470_neg : (24989437 / 50000000) ≤ -Real.log (1000000 / 1648373) ∧
    -Real.log (1000000 / 1648373) ≤ (499788741 / 1000000000) := by
  have h := checkLog_sound (w := (648373 / 2648373)) (n := 12)
    (lo := (24989437 / 50000000)) (hi := (499788741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1648373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1648373 / 1000000) = 1/(1000000 / 1648373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15470 : Bounds (24989437 / 50000000) (499788741 / 1000000000) (Real.log (1648373 / 1000000)) := by
  have h := reflection_log_15470_neg
  have he : Real.log (1648373 / 1000000) = -Real.log (1000000 / 1648373) := by
    rw [show ((1648373 / 1000000) : ℝ) = ((1000000 / 1648373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15471_neg : (1045184323 / 1000000000) ≤ -Real.log (351627 / 1000000) ∧
    -Real.log (351627 / 1000000) ≤ (41807373 / 40000000) := by
  have h := checkLog_sound (w := (148373 / 851627)) (n := 12)
    (lo := (352037143 / 1000000000)) (hi := (44004643 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 351627) = 1/(351627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15471 : Bounds (-41807373 / 40000000) (-1045184323 / 1000000000) (Real.log (351627 / 1000000)) := by
  have h := reflection_log_15471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15472_neg : (545395583 / 1000000000) ≤ -Real.log (579612452871 / 1000000000000) ∧
    -Real.log (579612452871 / 1000000000000) ≤ (4260903 / 7812500) := by
  have h := checkLog_sound (w := (420387547129 / 1579612452871)) (n := 12)
    (lo := (545395583 / 1000000000)) (hi := (4260903 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 579612452871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 579612452871) = 1/(579612452871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15472 : Bounds (-4260903 / 7812500) (-545395583 / 1000000000) (Real.log (579612452871 / 1000000000000)) := by
  have h := reflection_log_15472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15473_neg : (543289597 / 1000000000) ≤ -Real.log (5808343951 / 10000000000) ∧
    -Real.log (5808343951 / 10000000000) ≤ (271644799 / 500000000) := by
  have h := checkLog_sound (w := (4191656049 / 15808343951)) (n := 12)
    (lo := (543289597 / 1000000000)) (hi := (271644799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5808343951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5808343951) = 1/(5808343951 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15473 : Bounds (-271644799 / 500000000) (-543289597 / 1000000000) (Real.log (5808343951 / 10000000000)) := by
  have h := reflection_log_15473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15474_neg : (1541722591 / 1000000000) ≤ -Real.log (500000000000 / 2336316192529) ∧
    -Real.log (500000000000 / 2336316192529) ≤ (770861297 / 500000000) := by
  have h := checkLog_sound (w := (336316192529 / 4336316192529)) (n := 12)
    (lo := (155428231 / 1000000000)) (hi := (19428529 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2336316192529 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2336316192529 / 2000000000000) = 1/(500000000000 / 2336316192529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15474 : Bounds (1541722591 / 1000000000) (770861297 / 500000000) (Real.log (2336316192529 / 500000000000)) := by
  have h := reflection_log_15474_neg
  have he : Real.log (2336316192529 / 500000000000) = -Real.log (500000000000 / 2336316192529) := by
    rw [show ((2336316192529 / 500000000000) : ℝ) = ((500000000000 / 2336316192529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15475_neg : (193121633 / 125000000) ≤ -Real.log (500000000000 / 2343922679431) ∧
    -Real.log (500000000000 / 2343922679431) ≤ (1544973067 / 1000000000) := by
  have h := checkLog_sound (w := (343922679431 / 4343922679431)) (n := 12)
    (lo := (9917419 / 62500000)) (hi := (31735741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2343922679431 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2343922679431 / 2000000000000) = 1/(500000000000 / 2343922679431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15475 : Bounds (193121633 / 125000000) (1544973067 / 1000000000) (Real.log (2343922679431 / 500000000000)) := by
  have h := reflection_log_15475_neg
  have he : Real.log (2343922679431 / 500000000000) = -Real.log (500000000000 / 2343922679431) := by
    rw [show ((2343922679431 / 500000000000) : ℝ) = ((500000000000 / 2343922679431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15476_neg : (1443312087 / 250000000) ≤ -Real.log (100000000000 / 32158064516129) ∧
    -Real.log (100000000000 / 32158064516129) ≤ (5773248357 / 1000000000) := by
  have h := checkLog_sound (w := (6558064516129 / 57758064516129)) (n := 12)
    (lo := (57017727 / 250000000)) (hi := (228070909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32158064516129 / 25600000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(32158064516129 / 25600000000000) = 1/(100000000000 / 32158064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15476 : Bounds (1443312087 / 250000000) (5773248357 / 1000000000) (Real.log (32158064516129 / 100000000000)) := by
  have h := reflection_log_15476_neg
  have he : Real.log (32158064516129 / 100000000000) = -Real.log (100000000000 / 32158064516129) := by
    rw [show ((32158064516129 / 100000000000) : ℝ) = ((100000000000 / 32158064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15477_neg : (1451534619 / 250000000) ≤ -Real.log (500000000000 / 166166666666667) ∧
    -Real.log (500000000000 / 166166666666667) ≤ (1161227697 / 200000000) := by
  have h := checkLog_sound (w := (38166666666667 / 294166666666667)) (n := 12)
    (lo := (65240259 / 250000000)) (hi := (260961037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166166666666667 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(166166666666667 / 128000000000000) = 1/(500000000000 / 166166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15477 : Bounds (1451534619 / 250000000) (1161227697 / 200000000) (Real.log (166166666666667 / 500000000000)) := by
  have h := reflection_log_15477_neg
  have he : Real.log (166166666666667 / 500000000000) = -Real.log (500000000000 / 166166666666667) := by
    rw [show ((166166666666667 / 500000000000) : ℝ) = ((500000000000 / 166166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15478_neg : (690242967 / 1000000000) ≤ -Real.log (5000 / 9971) ∧
    -Real.log (5000 / 9971) ≤ (86280371 / 125000000) := by
  have h := checkLog_sound (w := (4971 / 14971)) (n := 12)
    (lo := (690242967 / 1000000000)) (hi := (86280371 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9971 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9971 / 5000) = 1/(5000 / 9971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15478 : Bounds (690242967 / 1000000000) (86280371 / 125000000) (Real.log (9971 / 5000)) := by
  have h := reflection_log_15478_neg
  have he : Real.log (9971 / 5000) = -Real.log (5000 / 9971) := by
    rw [show ((9971 / 5000) : ℝ) = ((5000 / 9971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15479_neg : (5149897357 / 1000000000) ≤ -Real.log (29 / 5000) ∧
    -Real.log (29 / 5000) ≤ (1029979473 / 200000000) := by
  have h := checkLog_sound (w := (161 / 1089)) (n := 12)
    (lo := (297867097 / 1000000000)) (hi := (148933549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 464) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 464) = 1/(29 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15479 : Bounds (-1029979473 / 200000000) (-5149897357 / 1000000000) (Real.log (29 / 5000)) := by
  have h := reflection_log_15479_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15480_neg : (496853 / 500000000) ≤ -Real.log (5000000 / 5004971) ∧
    -Real.log (5000000 / 5004971) ≤ (993707 / 1000000000) := by
  have h := checkLog_sound (w := (4971 / 10004971)) (n := 12)
    (lo := (496853 / 500000000)) (hi := (993707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004971 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004971 / 5000000) = 1/(5000000 / 5004971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15480 : Bounds (496853 / 500000000) (993707 / 1000000000) (Real.log (5004971 / 5000000)) := by
  have h := reflection_log_15480_neg
  have he : Real.log (5004971 / 5000000) = -Real.log (5000000 / 5004971) := by
    rw [show ((5004971 / 5000000) : ℝ) = ((5000000 / 5004971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15481_neg : (497347 / 500000000) ≤ -Real.log (4995029 / 5000000) ∧
    -Real.log (4995029 / 5000000) ≤ (198939 / 200000000) := by
  have h := checkLog_sound (w := (4971 / 9995029)) (n := 12)
    (lo := (497347 / 500000000)) (hi := (198939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995029) = 1/(4995029 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15481 : Bounds (-198939 / 200000000) (-497347 / 500000000) (Real.log (4995029 / 5000000)) := by
  have h := reflection_log_15481_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15482_neg : (4994089 / 10000000) ≤ -Real.log (1000000 / 1647747) ∧
    -Real.log (1000000 / 1647747) ≤ (499408901 / 1000000000) := by
  have h := checkLog_sound (w := (647747 / 2647747)) (n := 12)
    (lo := (4994089 / 10000000)) (hi := (499408901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647747 / 1000000) = 1/(1000000 / 1647747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15482 : Bounds (4994089 / 10000000) (499408901 / 1000000000) (Real.log (1647747 / 1000000)) := by
  have h := reflection_log_15482_neg
  have he : Real.log (1647747 / 1000000) = -Real.log (1000000 / 1647747) := by
    rw [show ((1647747 / 1000000) : ℝ) = ((1000000 / 1647747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15483_neg : (1043405611 / 1000000000) ≤ -Real.log (352253 / 1000000) ∧
    -Real.log (352253 / 1000000) ≤ (1043405613 / 1000000000) := by
  have h := checkLog_sound (w := (147747 / 852253)) (n := 12)
    (lo := (350258431 / 1000000000)) (hi := (1368197 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352253) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 352253) = 1/(352253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15483 : Bounds (-1043405613 / 1000000000) (-1043405611 / 1000000000) (Real.log (352253 / 1000000)) := by
  have h := reflection_log_15483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15484_neg : (499981033 / 1000000000) ≤ -Real.log (100000 / 164869) ∧
    -Real.log (100000 / 164869) ≤ (249990517 / 500000000) := by
  have h := checkLog_sound (w := (64869 / 264869)) (n := 12)
    (lo := (499981033 / 1000000000)) (hi := (249990517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164869 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164869 / 100000) = 1/(100000 / 164869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15484 : Bounds (499981033 / 1000000000) (249990517 / 500000000) (Real.log (164869 / 100000)) := by
  have h := reflection_log_15484_neg
  have he : Real.log (164869 / 100000) = -Real.log (100000 / 164869) := by
    rw [show ((164869 / 100000) : ℝ) = ((100000 / 164869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15485_neg : (1046086253 / 1000000000) ≤ -Real.log (35131 / 100000) ∧
    -Real.log (35131 / 100000) ≤ (209217251 / 200000000) := by
  have h := checkLog_sound (w := (14869 / 85131)) (n := 12)
    (lo := (352939073 / 1000000000)) (hi := (176469537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35131) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35131) = 1/(35131 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15485 : Bounds (-209217251 / 200000000) (-1046086253 / 1000000000) (Real.log (35131 / 100000)) := by
  have h := reflection_log_15485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15486_neg : (546105221 / 1000000000) ≤ -Real.log (5792012839 / 10000000000) ∧
    -Real.log (5792012839 / 10000000000) ≤ (273052611 / 500000000) := by
  have h := checkLog_sound (w := (4207987161 / 15792012839)) (n := 12)
    (lo := (546105221 / 1000000000)) (hi := (273052611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5792012839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5792012839) = 1/(5792012839 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15486 : Bounds (-273052611 / 500000000) (-546105221 / 1000000000) (Real.log (5792012839 / 10000000000)) := by
  have h := reflection_log_15486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15487_neg : (543996711 / 1000000000) ≤ -Real.log (580423823991 / 1000000000000) ∧
    -Real.log (580423823991 / 1000000000000) ≤ (67999589 / 125000000) := by
  have h := checkLog_sound (w := (419576176009 / 1580423823991)) (n := 12)
    (lo := (543996711 / 1000000000)) (hi := (67999589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 580423823991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 580423823991) = 1/(580423823991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15487 : Bounds (-67999589 / 125000000) (-543996711 / 1000000000) (Real.log (580423823991 / 1000000000000)) := by
  have h := reflection_log_15487_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0242 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15488_neg : (154281451 / 100000000) ≤ -Real.log (500000000000 / 2338868654063) ∧
    -Real.log (500000000000 / 2338868654063) ≤ (1542814513 / 1000000000) := by
  have h := checkLog_sound (w := (338868654063 / 4338868654063)) (n := 12)
    (lo := (3130403 / 20000000)) (hi := (156520151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2338868654063 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2338868654063 / 2000000000000) = 1/(500000000000 / 2338868654063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15488 : Bounds (154281451 / 100000000) (1542814513 / 1000000000) (Real.log (2338868654063 / 500000000000)) := by
  have h := reflection_log_15488_neg
  have he : Real.log (2338868654063 / 500000000000) = -Real.log (500000000000 / 2338868654063) := by
    rw [show ((2338868654063 / 500000000000) : ℝ) = ((500000000000 / 2338868654063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15489_neg : (773033643 / 500000000) ≤ -Real.log (500000000000 / 2346488855997) ∧
    -Real.log (500000000000 / 2346488855997) ≤ (1546067289 / 1000000000) := by
  have h := checkLog_sound (w := (346488855997 / 4346488855997)) (n := 12)
    (lo := (79886463 / 500000000)) (hi := (159772927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2346488855997 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2346488855997 / 2000000000000) = 1/(500000000000 / 2346488855997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15489 : Bounds (773033643 / 500000000) (1546067289 / 1000000000) (Real.log (2346488855997 / 500000000000)) := by
  have h := reflection_log_15489_neg
  have he : Real.log (2346488855997 / 500000000000) = -Real.log (500000000000 / 2346488855997) := by
    rw [show ((2346488855997 / 500000000000) : ℝ) = ((500000000000 / 2346488855997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15490_neg : (1451534619 / 250000000) ≤ -Real.log (250000000000 / 83083333333333) ∧
    -Real.log (250000000000 / 83083333333333) ≤ (1161227697 / 200000000) := by
  have h := checkLog_sound (w := (19083333333333 / 147083333333333)) (n := 12)
    (lo := (65240259 / 250000000)) (hi := (260961037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83083333333333 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(83083333333333 / 64000000000000) = 1/(250000000000 / 83083333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15490 : Bounds (1451534619 / 250000000) (1161227697 / 200000000) (Real.log (83083333333333 / 250000000000)) := by
  have h := reflection_log_15490_neg
  have he : Real.log (83083333333333 / 250000000000) = -Real.log (250000000000 / 83083333333333) := by
    rw [show ((83083333333333 / 250000000000) : ℝ) = ((250000000000 / 83083333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15491_neg : (1460035081 / 250000000) ≤ -Real.log (500000000000 / 171913793103449) ∧
    -Real.log (500000000000 / 171913793103449) ≤ (5840140333 / 1000000000) := by
  have h := checkLog_sound (w := (43913793103449 / 299913793103449)) (n := 12)
    (lo := (73740721 / 250000000)) (hi := (58992577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171913793103449 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(171913793103449 / 128000000000000) = 1/(500000000000 / 171913793103449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15491 : Bounds (1460035081 / 250000000) (5840140333 / 1000000000) (Real.log (171913793103449 / 500000000000)) := by
  have h := reflection_log_15491_neg
  have he : Real.log (171913793103449 / 500000000000) = -Real.log (500000000000 / 171913793103449) := by
    rw [show ((171913793103449 / 500000000000) : ℝ) = ((500000000000 / 171913793103449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15492_neg : (690343253 / 1000000000) ≤ -Real.log (1250 / 2493) ∧
    -Real.log (1250 / 2493) ≤ (345171627 / 500000000) := by
  have h := checkLog_sound (w := (1243 / 3743)) (n := 12)
    (lo := (690343253 / 1000000000)) (hi := (345171627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2493 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2493 / 1250) = 1/(1250 / 2493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15492 : Bounds (690343253 / 1000000000) (345171627 / 500000000) (Real.log (2493 / 1250)) := by
  have h := reflection_log_15492_neg
  have he : Real.log (2493 / 1250) = -Real.log (1250 / 2493) := by
    rw [show ((2493 / 1250) : ℝ) = ((1250 / 2493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15493_neg : (5184988677 / 1000000000) ≤ -Real.log (7 / 1250) ∧
    -Real.log (7 / 1250) ≤ (1036997737 / 200000000) := by
  have h := checkLog_sound (w := (177 / 1073)) (n := 12)
    (lo := (332958417 / 1000000000)) (hi := (166479209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 448) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 448) = 1/(7 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15493 : Bounds (-1036997737 / 200000000) (-5184988677 / 1000000000) (Real.log (7 / 1250)) := by
  have h := reflection_log_15493_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15494_neg : (198781 / 200000000) ≤ -Real.log (1250000 / 1251243) ∧
    -Real.log (1250000 / 1251243) ≤ (496953 / 500000000) := by
  have h := checkLog_sound (w := (1243 / 2501243)) (n := 12)
    (lo := (198781 / 200000000)) (hi := (496953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251243 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251243 / 1250000) = 1/(1250000 / 1251243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15494 : Bounds (198781 / 200000000) (496953 / 500000000) (Real.log (1251243 / 1250000)) := by
  have h := reflection_log_15494_neg
  have he : Real.log (1251243 / 1250000) = -Real.log (1250000 / 1251243) := by
    rw [show ((1251243 / 1250000) : ℝ) = ((1250000 / 1251243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15495_neg : (497447 / 500000000) ≤ -Real.log (1248757 / 1250000) ∧
    -Real.log (1248757 / 1250000) ≤ (198979 / 200000000) := by
  have h := checkLog_sound (w := (1243 / 2498757)) (n := 12)
    (lo := (497447 / 500000000)) (hi := (198979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1248757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1248757) = 1/(1248757 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15495 : Bounds (-198979 / 200000000) (-497447 / 500000000) (Real.log (1248757 / 1250000)) := by
  have h := reflection_log_15495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15496_neg : (31225117 / 62500000) ≤ -Real.log (200000 / 329613) ∧
    -Real.log (200000 / 329613) ≤ (499601873 / 1000000000) := by
  have h := checkLog_sound (w := (129613 / 529613)) (n := 12)
    (lo := (31225117 / 62500000)) (hi := (499601873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329613 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329613 / 200000) = 1/(200000 / 329613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15496 : Bounds (31225117 / 62500000) (499601873 / 1000000000) (Real.log (329613 / 200000)) := by
  have h := reflection_log_15496_neg
  have he : Real.log (329613 / 200000) = -Real.log (200000 / 329613) := by
    rw [show ((329613 / 200000) : ℝ) = ((200000 / 329613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15497_neg : (522154389 / 500000000) ≤ -Real.log (70387 / 200000) ∧
    -Real.log (70387 / 200000) ≤ (52215439 / 50000000) := by
  have h := checkLog_sound (w := (29613 / 170387)) (n := 12)
    (lo := (175580799 / 500000000)) (hi := (351161599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70387) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 70387) = 1/(70387 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15497 : Bounds (-52215439 / 50000000) (-522154389 / 500000000) (Real.log (70387 / 200000)) := by
  have h := reflection_log_15497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15498_neg : (500174501 / 1000000000) ≤ -Real.log (1000000 / 1649009) ∧
    -Real.log (1000000 / 1649009) ≤ (250087251 / 500000000) := by
  have h := checkLog_sound (w := (649009 / 2649009)) (n := 12)
    (lo := (500174501 / 1000000000)) (hi := (250087251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1649009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1649009 / 1000000) = 1/(1000000 / 1649009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15498 : Bounds (500174501 / 1000000000) (250087251 / 500000000) (Real.log (1649009 / 1000000)) := by
  have h := reflection_log_15498_neg
  have he : Real.log (1649009 / 1000000) = -Real.log (1000000 / 1649009) := by
    rw [show ((1649009 / 1000000) : ℝ) = ((1000000 / 1649009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15499_neg : (130874337 / 125000000) ≤ -Real.log (350991 / 1000000) ∧
    -Real.log (350991 / 1000000) ≤ (523497349 / 500000000) := by
  have h := checkLog_sound (w := (149009 / 850991)) (n := 12)
    (lo := (88461879 / 250000000)) (hi := (353847517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350991) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 350991) = 1/(350991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15499 : Bounds (-523497349 / 500000000) (-130874337 / 125000000) (Real.log (350991 / 1000000)) := by
  have h := reflection_log_15499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15500_neg : (109364039 / 200000000) ≤ -Real.log (578787317919 / 1000000000000) ∧
    -Real.log (578787317919 / 1000000000000) ≤ (136705049 / 250000000) := by
  have h := checkLog_sound (w := (421212682081 / 1578787317919)) (n := 12)
    (lo := (109364039 / 200000000)) (hi := (136705049 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 578787317919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 578787317919) = 1/(578787317919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15500 : Bounds (-136705049 / 250000000) (-109364039 / 200000000) (Real.log (578787317919 / 1000000000000)) := by
  have h := reflection_log_15500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15501_neg : (544706907 / 1000000000) ≤ -Real.log (23200470231 / 40000000000) ∧
    -Real.log (23200470231 / 40000000000) ≤ (136176727 / 250000000) := by
  have h := checkLog_sound (w := (16799529769 / 63200470231)) (n := 12)
    (lo := (544706907 / 1000000000)) (hi := (136176727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23200470231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23200470231) = 1/(23200470231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15501 : Bounds (-136176727 / 250000000) (-544706907 / 1000000000) (Real.log (23200470231 / 40000000000)) := by
  have h := reflection_log_15501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15502_neg : (30878213 / 20000000) ≤ -Real.log (500000000000 / 2341433787489) ∧
    -Real.log (500000000000 / 2341433787489) ≤ (1543910653 / 1000000000) := by
  have h := checkLog_sound (w := (341433787489 / 4341433787489)) (n := 12)
    (lo := (15761629 / 100000000)) (hi := (157616291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2341433787489 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2341433787489 / 2000000000000) = 1/(500000000000 / 2341433787489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15502 : Bounds (30878213 / 20000000) (1543910653 / 1000000000) (Real.log (2341433787489 / 500000000000)) := by
  have h := reflection_log_15502_neg
  have he : Real.log (2341433787489 / 500000000000) = -Real.log (500000000000 / 2341433787489) := by
    rw [show ((2341433787489 / 500000000000) : ℝ) = ((500000000000 / 2341433787489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15503_neg : (1547169197 / 1000000000) ≤ -Real.log (62500000000 / 293634487779) ∧
    -Real.log (62500000000 / 293634487779) ≤ (3867923 / 2500000) := by
  have h := checkLog_sound (w := (43634487779 / 543634487779)) (n := 12)
    (lo := (160874837 / 1000000000)) (hi := (80437419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293634487779 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(293634487779 / 250000000000) = 1/(62500000000 / 293634487779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15503 : Bounds (1547169197 / 1000000000) (3867923 / 2500000) (Real.log (293634487779 / 62500000000)) := by
  have h := reflection_log_15503_neg
  have he : Real.log (293634487779 / 62500000000) = -Real.log (62500000000 / 293634487779) := by
    rw [show ((293634487779 / 62500000000) : ℝ) = ((62500000000 / 293634487779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15504_neg : (1460035081 / 250000000) ≤ -Real.log (62500000000 / 21489224137931) ∧
    -Real.log (62500000000 / 21489224137931) ≤ (5840140333 / 1000000000) := by
  have h := checkLog_sound (w := (5489224137931 / 37489224137931)) (n := 12)
    (lo := (73740721 / 250000000)) (hi := (58992577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21489224137931 / 16000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(21489224137931 / 16000000000000) = 1/(62500000000 / 21489224137931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15504 : Bounds (1460035081 / 250000000) (5840140333 / 1000000000) (Real.log (21489224137931 / 62500000000)) := by
  have h := reflection_log_15504_neg
  have he : Real.log (21489224137931 / 62500000000) = -Real.log (62500000000 / 21489224137931) := by
    rw [show ((21489224137931 / 62500000000) : ℝ) = ((62500000000 / 21489224137931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15505_neg : (5875331929 / 1000000000) ≤ -Real.log (500000000000 / 178071428571429) ∧
    -Real.log (500000000000 / 178071428571429) ≤ (2937665969 / 500000000) := by
  have h := checkLog_sound (w := (50071428571429 / 306071428571429)) (n := 12)
    (lo := (330154489 / 1000000000)) (hi := (33015449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178071428571429 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(178071428571429 / 128000000000000) = 1/(500000000000 / 178071428571429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15505 : Bounds (5875331929 / 1000000000) (2937665969 / 500000000) (Real.log (178071428571429 / 500000000000)) := by
  have h := reflection_log_15505_neg
  have he : Real.log (178071428571429 / 500000000000) = -Real.log (500000000000 / 178071428571429) := by
    rw [show ((178071428571429 / 500000000000) : ℝ) = ((500000000000 / 178071428571429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15506_neg : (86305441 / 125000000) ≤ -Real.log (5000 / 9973) ∧
    -Real.log (5000 / 9973) ≤ (690443529 / 1000000000) := by
  have h := checkLog_sound (w := (4973 / 14973)) (n := 12)
    (lo := (86305441 / 125000000)) (hi := (690443529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9973 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9973 / 5000) = 1/(5000 / 9973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15506 : Bounds (86305441 / 125000000) (690443529 / 1000000000) (Real.log (9973 / 5000)) := by
  have h := reflection_log_15506_neg
  have he : Real.log (9973 / 5000) = -Real.log (5000 / 9973) := by
    rw [show ((9973 / 5000) : ℝ) = ((5000 / 9973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15507_neg : (5221356321 / 1000000000) ≤ -Real.log (27 / 5000) ∧
    -Real.log (27 / 5000) ≤ (5221356329 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1057)) (n := 12)
    (lo := (369326061 / 1000000000)) (hi := (184663031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 432) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 432) = 1/(27 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15507 : Bounds (-5221356329 / 1000000000) (-5221356321 / 1000000000) (Real.log (27 / 5000)) := by
  have h := reflection_log_15507_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15508_neg : (198821 / 200000000) ≤ -Real.log (5000000 / 5004973) ∧
    -Real.log (5000000 / 5004973) ≤ (497053 / 500000000) := by
  have h := checkLog_sound (w := (4973 / 10004973)) (n := 12)
    (lo := (198821 / 200000000)) (hi := (497053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004973 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004973 / 5000000) = 1/(5000000 / 5004973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15508 : Bounds (198821 / 200000000) (497053 / 500000000) (Real.log (5004973 / 5000000)) := by
  have h := reflection_log_15508_neg
  have he : Real.log (5004973 / 5000000) = -Real.log (5000000 / 5004973) := by
    rw [show ((5004973 / 5000000) : ℝ) = ((5000000 / 5004973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15509_neg : (497547 / 500000000) ≤ -Real.log (4995027 / 5000000) ∧
    -Real.log (4995027 / 5000000) ≤ (199019 / 200000000) := by
  have h := checkLog_sound (w := (4973 / 9995027)) (n := 12)
    (lo := (497547 / 500000000)) (hi := (199019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995027) = 1/(4995027 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15509 : Bounds (-199019 / 200000000) (-497547 / 500000000) (Real.log (4995027 / 5000000)) := by
  have h := reflection_log_15509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15510_neg : (249897707 / 500000000) ≤ -Real.log (15625 / 25756) ∧
    -Real.log (15625 / 25756) ≤ (99959083 / 200000000) := by
  have h := checkLog_sound (w := (10131 / 41381)) (n := 12)
    (lo := (249897707 / 500000000)) (hi := (99959083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25756 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25756 / 15625) = 1/(15625 / 25756) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15510 : Bounds (249897707 / 500000000) (99959083 / 200000000) (Real.log (25756 / 15625)) := by
  have h := reflection_log_15510_neg
  have he : Real.log (25756 / 15625) = -Real.log (15625 / 25756) := by
    rw [show ((25756 / 15625) : ℝ) = ((15625 / 25756) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15511_neg : (1045215607 / 1000000000) ≤ -Real.log (5494 / 15625) ∧
    -Real.log (5494 / 15625) ≤ (1045215609 / 1000000000) := by
  have h := checkLog_sound (w := (4637 / 26613)) (n := 12)
    (lo := (352068427 / 1000000000)) (hi := (88017107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10988) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 10988) = 1/(5494 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15511 : Bounds (-1045215609 / 1000000000) (-1045215607 / 1000000000) (Real.log (5494 / 15625)) := by
  have h := reflection_log_15511_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15512_neg : (62546143 / 125000000) ≤ -Real.log (100000 / 164933) ∧
    -Real.log (100000 / 164933) ≤ (100073829 / 200000000) := by
  have h := checkLog_sound (w := (64933 / 264933)) (n := 12)
    (lo := (62546143 / 125000000)) (hi := (100073829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164933 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164933 / 100000) = 1/(100000 / 164933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15512 : Bounds (62546143 / 125000000) (100073829 / 200000000) (Real.log (164933 / 100000)) := by
  have h := reflection_log_15512_neg
  have he : Real.log (164933 / 100000) = -Real.log (100000 / 164933) := by
    rw [show ((164933 / 100000) : ℝ) = ((100000 / 164933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15513_neg : (261977417 / 250000000) ≤ -Real.log (35067 / 100000) ∧
    -Real.log (35067 / 100000) ≤ (104790967 / 100000000) := by
  have h := checkLog_sound (w := (14933 / 85067)) (n := 12)
    (lo := (44345311 / 125000000)) (hi := (354762489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35067) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35067) = 1/(35067 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15513 : Bounds (-104790967 / 100000000) (-261977417 / 250000000) (Real.log (35067 / 100000)) := by
  have h := reflection_log_15513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15514_neg : (547540523 / 1000000000) ≤ -Real.log (5783705511 / 10000000000) ∧
    -Real.log (5783705511 / 10000000000) ≤ (136885131 / 250000000) := by
  have h := checkLog_sound (w := (4216294489 / 15783705511)) (n := 12)
    (lo := (547540523 / 1000000000)) (hi := (136885131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5783705511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5783705511) = 1/(5783705511 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15514 : Bounds (-136885131 / 250000000) (-547540523 / 1000000000) (Real.log (5783705511 / 10000000000)) := by
  have h := reflection_log_15514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15515_neg : (545420193 / 1000000000) ≤ -Real.log (141503464 / 244140625) ∧
    -Real.log (141503464 / 244140625) ≤ (272710097 / 500000000) := by
  have h := checkLog_sound (w := (102637161 / 385644089)) (n := 12)
    (lo := (545420193 / 1000000000)) (hi := (272710097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 141503464) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 141503464) = 1/(141503464 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15515 : Bounds (-272710097 / 500000000) (-545420193 / 1000000000) (Real.log (141503464 / 244140625)) := by
  have h := reflection_log_15515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15516_neg : (77250551 / 50000000) ≤ -Real.log (500000000000 / 2344011649071) ∧
    -Real.log (500000000000 / 2344011649071) ≤ (1545011023 / 1000000000) := by
  have h := checkLog_sound (w := (344011649071 / 4344011649071)) (n := 12)
    (lo := (7935833 / 50000000)) (hi := (158716661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2344011649071 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2344011649071 / 2000000000000) = 1/(500000000000 / 2344011649071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15516 : Bounds (77250551 / 50000000) (1545011023 / 1000000000) (Real.log (2344011649071 / 500000000000)) := by
  have h := reflection_log_15516_neg
  have he : Real.log (2344011649071 / 500000000000) = -Real.log (500000000000 / 2344011649071) := by
    rw [show ((2344011649071 / 500000000000) : ℝ) = ((500000000000 / 2344011649071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15517_neg : (387069703 / 250000000) ≤ -Real.log (100000000000 / 470336783871) ∧
    -Real.log (100000000000 / 470336783871) ≤ (309655763 / 200000000) := by
  have h := checkLog_sound (w := (70336783871 / 870336783871)) (n := 12)
    (lo := (40496113 / 250000000)) (hi := (161984453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470336783871 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(470336783871 / 400000000000) = 1/(100000000000 / 470336783871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15517 : Bounds (387069703 / 250000000) (309655763 / 200000000) (Real.log (470336783871 / 100000000000)) := by
  have h := reflection_log_15517_neg
  have he : Real.log (470336783871 / 100000000000) = -Real.log (100000000000 / 470336783871) := by
    rw [show ((470336783871 / 100000000000) : ℝ) = ((100000000000 / 470336783871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15518_neg : (5875331929 / 1000000000) ≤ -Real.log (125000000000 / 44517857142857) ∧
    -Real.log (125000000000 / 44517857142857) ≤ (2937665969 / 500000000) := by
  have h := checkLog_sound (w := (12517857142857 / 76517857142857)) (n := 12)
    (lo := (330154489 / 1000000000)) (hi := (33015449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44517857142857 / 32000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(44517857142857 / 32000000000000) = 1/(125000000000 / 44517857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15518 : Bounds (5875331929 / 1000000000) (2937665969 / 500000000) (Real.log (44517857142857 / 125000000000)) := by
  have h := reflection_log_15518_neg
  have he : Real.log (44517857142857 / 125000000000) = -Real.log (125000000000 / 44517857142857) := by
    rw [show ((44517857142857 / 125000000000) : ℝ) = ((125000000000 / 44517857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15519_neg : (5911799849 / 1000000000) ≤ -Real.log (250000000000 / 92342592592593) ∧
    -Real.log (250000000000 / 92342592592593) ≤ (2955899929 / 500000000) := by
  have h := checkLog_sound (w := (28342592592593 / 156342592592593)) (n := 12)
    (lo := (366622409 / 1000000000)) (hi := (36662241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92342592592593 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(92342592592593 / 64000000000000) = 1/(250000000000 / 92342592592593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15519 : Bounds (5911799849 / 1000000000) (2955899929 / 500000000) (Real.log (92342592592593 / 250000000000)) := by
  have h := reflection_log_15519_neg
  have he : Real.log (92342592592593 / 250000000000) = -Real.log (250000000000 / 92342592592593) := by
    rw [show ((92342592592593 / 250000000000) : ℝ) = ((250000000000 / 92342592592593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15520_neg : (345271897 / 500000000) ≤ -Real.log (2500 / 4987) ∧
    -Real.log (2500 / 4987) ≤ (138108759 / 200000000) := by
  have h := checkLog_sound (w := (2487 / 7487)) (n := 12)
    (lo := (345271897 / 500000000)) (hi := (138108759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4987 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4987 / 2500) = 1/(2500 / 4987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15520 : Bounds (345271897 / 500000000) (138108759 / 200000000) (Real.log (4987 / 2500)) := by
  have h := reflection_log_15520_neg
  have he : Real.log (4987 / 2500) = -Real.log (2500 / 4987) := by
    rw [show ((4987 / 2500) : ℝ) = ((2500 / 4987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15521_neg : (5259096649 / 1000000000) ≤ -Real.log (13 / 2500) ∧
    -Real.log (13 / 2500) ≤ (5259096657 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1041)) (n := 12)
    (lo := (407066389 / 1000000000)) (hi := (40706639 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 416) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 416) = 1/(13 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15521 : Bounds (-5259096657 / 1000000000) (-5259096649 / 1000000000) (Real.log (13 / 2500)) := by
  have h := reflection_log_15521_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15522_neg : (198861 / 200000000) ≤ -Real.log (2500000 / 2502487) ∧
    -Real.log (2500000 / 2502487) ≤ (497153 / 500000000) := by
  have h := checkLog_sound (w := (2487 / 5002487)) (n := 12)
    (lo := (198861 / 200000000)) (hi := (497153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502487 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502487 / 2500000) = 1/(2500000 / 2502487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15522 : Bounds (198861 / 200000000) (497153 / 500000000) (Real.log (2502487 / 2500000)) := by
  have h := reflection_log_15522_neg
  have he : Real.log (2502487 / 2500000) = -Real.log (2500000 / 2502487) := by
    rw [show ((2502487 / 2500000) : ℝ) = ((2500000 / 2502487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15523_neg : (199059 / 200000000) ≤ -Real.log (2497513 / 2500000) ∧
    -Real.log (2497513 / 2500000) ≤ (31103 / 31250000) := by
  have h := checkLog_sound (w := (2487 / 4997513)) (n := 12)
    (lo := (199059 / 200000000)) (hi := (31103 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497513) = 1/(2497513 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15523 : Bounds (-31103 / 31250000) (-199059 / 200000000) (Real.log (2497513 / 2500000)) := by
  have h := reflection_log_15523_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15524_neg : (499990131 / 1000000000) ≤ -Real.log (200000 / 329741) ∧
    -Real.log (200000 / 329741) ≤ (124997533 / 250000000) := by
  have h := checkLog_sound (w := (129741 / 529741)) (n := 12)
    (lo := (499990131 / 1000000000)) (hi := (124997533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329741 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329741 / 200000) = 1/(200000 / 329741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15524 : Bounds (499990131 / 1000000000) (124997533 / 250000000) (Real.log (329741 / 200000)) := by
  have h := reflection_log_15524_neg
  have he : Real.log (329741 / 200000) = -Real.log (200000 / 329741) := by
    rw [show ((329741 / 200000) : ℝ) = ((200000 / 329741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15525_neg : (130766119 / 125000000) ≤ -Real.log (70259 / 200000) ∧
    -Real.log (70259 / 200000) ≤ (523064477 / 500000000) := by
  have h := checkLog_sound (w := (29741 / 170259)) (n := 12)
    (lo := (88245443 / 250000000)) (hi := (352981773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70259) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 70259) = 1/(70259 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15525 : Bounds (-523064477 / 500000000) (-130766119 / 125000000) (Real.log (70259 / 200000)) := by
  have h := reflection_log_15525_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15526_neg : (250282481 / 500000000) ≤ -Real.log (1000000 / 1649653) ∧
    -Real.log (1000000 / 1649653) ≤ (500564963 / 1000000000) := by
  have h := checkLog_sound (w := (649653 / 2649653)) (n := 12)
    (lo := (250282481 / 500000000)) (hi := (500564963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1649653 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1649653 / 1000000) = 1/(1000000 / 1649653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15526 : Bounds (250282481 / 500000000) (500564963 / 1000000000) (Real.log (1649653 / 1000000)) := by
  have h := reflection_log_15526_neg
  have he : Real.log (1649653 / 1000000) = -Real.log (1000000 / 1649653) := by
    rw [show ((1649653 / 1000000) : ℝ) = ((1000000 / 1649653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15527_neg : (524415593 / 500000000) ≤ -Real.log (350347 / 1000000) ∧
    -Real.log (350347 / 1000000) ≤ (262207797 / 250000000) := by
  have h := checkLog_sound (w := (149653 / 850347)) (n := 12)
    (lo := (177842003 / 500000000)) (hi := (355684007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350347) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 350347) = 1/(350347 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15527 : Bounds (-262207797 / 250000000) (-524415593 / 500000000) (Real.log (350347 / 1000000)) := by
  have h := reflection_log_15527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15528_neg : (34266639 / 62500000) ≤ -Real.log (577950979591 / 1000000000000) ∧
    -Real.log (577950979591 / 1000000000000) ≤ (21930649 / 40000000) := by
  have h := checkLog_sound (w := (422049020409 / 1577950979591)) (n := 12)
    (lo := (34266639 / 62500000)) (hi := (21930649 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577950979591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577950979591) = 1/(577950979591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15528 : Bounds (-21930649 / 40000000) (-34266639 / 62500000) (Real.log (577950979591 / 1000000000000)) := by
  have h := reflection_log_15528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15529_neg : (546138821 / 1000000000) ≤ -Real.log (23167272919 / 40000000000) ∧
    -Real.log (23167272919 / 40000000000) ≤ (273069411 / 500000000) := by
  have h := checkLog_sound (w := (16832727081 / 63167272919)) (n := 12)
    (lo := (546138821 / 1000000000)) (hi := (273069411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23167272919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23167272919) = 1/(23167272919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15529 : Bounds (-273069411 / 500000000) (-546138821 / 1000000000) (Real.log (23167272919 / 40000000000)) := by
  have h := reflection_log_15529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15530_neg : (773059541 / 500000000) ≤ -Real.log (500000000000 / 2346610398667) ∧
    -Real.log (500000000000 / 2346610398667) ≤ (309223817 / 200000000) := by
  have h := checkLog_sound (w := (346610398667 / 4346610398667)) (n := 12)
    (lo := (79912361 / 500000000)) (hi := (159824723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2346610398667 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2346610398667 / 2000000000000) = 1/(500000000000 / 2346610398667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15530 : Bounds (773059541 / 500000000) (309223817 / 200000000) (Real.log (2346610398667 / 500000000000)) := by
  have h := reflection_log_15530_neg
  have he : Real.log (2346610398667 / 500000000000) = -Real.log (500000000000 / 2346610398667) := by
    rw [show ((2346610398667 / 500000000000) : ℝ) = ((500000000000 / 2346610398667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15531_neg : (387349037 / 250000000) ≤ -Real.log (250000000000 / 1177156504837) ∧
    -Real.log (250000000000 / 1177156504837) ≤ (1549396151 / 1000000000) := by
  have h := checkLog_sound (w := (177156504837 / 2177156504837)) (n := 12)
    (lo := (40775447 / 250000000)) (hi := (163101789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177156504837 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1177156504837 / 1000000000000) = 1/(250000000000 / 1177156504837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15531 : Bounds (387349037 / 250000000) (1549396151 / 1000000000) (Real.log (1177156504837 / 250000000000)) := by
  have h := reflection_log_15531_neg
  have he : Real.log (1177156504837 / 250000000000) = -Real.log (250000000000 / 1177156504837) := by
    rw [show ((1177156504837 / 250000000000) : ℝ) = ((250000000000 / 1177156504837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15532_neg : (5911799849 / 1000000000) ≤ -Real.log (100000000000 / 36937037037037) ∧
    -Real.log (100000000000 / 36937037037037) ≤ (2955899929 / 500000000) := by
  have h := checkLog_sound (w := (11337037037037 / 62537037037037)) (n := 12)
    (lo := (366622409 / 1000000000)) (hi := (36662241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36937037037037 / 25600000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(36937037037037 / 25600000000000) = 1/(100000000000 / 36937037037037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15532 : Bounds (5911799849 / 1000000000) (2955899929 / 500000000) (Real.log (36937037037037 / 100000000000)) := by
  have h := reflection_log_15532_neg
  have he : Real.log (36937037037037 / 100000000000) = -Real.log (100000000000 / 36937037037037) := by
    rw [show ((36937037037037 / 100000000000) : ℝ) = ((100000000000 / 36937037037037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15533_neg : (5949640443 / 1000000000) ≤ -Real.log (500000000000 / 191807692307693) ∧
    -Real.log (500000000000 / 191807692307693) ≤ (1487410113 / 250000000) := by
  have h := checkLog_sound (w := (63807692307693 / 319807692307693)) (n := 12)
    (lo := (404463003 / 1000000000)) (hi := (101115751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191807692307693 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(191807692307693 / 128000000000000) = 1/(500000000000 / 191807692307693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15533 : Bounds (5949640443 / 1000000000) (1487410113 / 250000000) (Real.log (191807692307693 / 500000000000)) := by
  have h := reflection_log_15533_neg
  have he : Real.log (191807692307693 / 500000000000) = -Real.log (500000000000 / 191807692307693) := by
    rw [show ((191807692307693 / 500000000000) : ℝ) = ((500000000000 / 191807692307693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15534_neg : (13812881 / 20000000) ≤ -Real.log (200 / 399) ∧
    -Real.log (200 / 399) ≤ (690644051 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 599)) (n := 12)
    (lo := (13812881 / 20000000)) (hi := (690644051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399 / 200) = 1/(200 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15534 : Bounds (13812881 / 20000000) (690644051 / 1000000000) (Real.log (399 / 200)) := by
  have h := reflection_log_15534_neg
  have he : Real.log (399 / 200) = -Real.log (200 / 399) := by
    rw [show ((399 / 200) : ℝ) = ((200 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15535_neg : (2649158681 / 500000000) ≤ -Real.log (1 / 200) ∧
    -Real.log (1 / 200) ≤ (529831737 / 100000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(25 / 16) = 1/(1 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15535 : Bounds (-529831737 / 100000000) (-2649158681 / 500000000) (Real.log (1 / 200)) := by
  have h := reflection_log_15535_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15536_neg : (198901 / 200000000) ≤ -Real.log (200000 / 200199) ∧
    -Real.log (200000 / 200199) ≤ (497253 / 500000000) := by
  have h := checkLog_sound (w := (199 / 400199)) (n := 12)
    (lo := (198901 / 200000000)) (hi := (497253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200199 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200199 / 200000) = 1/(200000 / 200199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15536 : Bounds (198901 / 200000000) (497253 / 500000000) (Real.log (200199 / 200000)) := by
  have h := reflection_log_15536_neg
  have he : Real.log (200199 / 200000) = -Real.log (200000 / 200199) := by
    rw [show ((200199 / 200000) : ℝ) = ((200000 / 200199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15537_neg : (199099 / 200000000) ≤ -Real.log (199801 / 200000) ∧
    -Real.log (199801 / 200000) ≤ (124437 / 125000000) := by
  have h := checkLog_sound (w := (199 / 399801)) (n := 12)
    (lo := (199099 / 200000000)) (hi := (124437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199801) = 1/(199801 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15537 : Bounds (-124437 / 125000000) (-199099 / 200000000) (Real.log (199801 / 200000)) := by
  have h := reflection_log_15537_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15538_neg : (500186023 / 1000000000) ≤ -Real.log (250000 / 412257) ∧
    -Real.log (250000 / 412257) ≤ (62523253 / 125000000) := by
  have h := checkLog_sound (w := (162257 / 662257)) (n := 12)
    (lo := (500186023 / 1000000000)) (hi := (62523253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412257 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412257 / 250000) = 1/(250000 / 412257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15538 : Bounds (500186023 / 1000000000) (62523253 / 125000000) (Real.log (412257 / 250000)) := by
  have h := reflection_log_15538_neg
  have he : Real.log (412257 / 250000) = -Real.log (250000 / 412257) := by
    rw [show ((412257 / 250000) : ℝ) = ((250000 / 412257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15539_neg : (104704883 / 100000000) ≤ -Real.log (87743 / 250000) ∧
    -Real.log (87743 / 250000) ≤ (8180069 / 7812500) := by
  have h := checkLog_sound (w := (37257 / 212743)) (n := 12)
    (lo := (7078033 / 20000000)) (hi := (353901651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87743) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 87743) = 1/(87743 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15539 : Bounds (-8180069 / 7812500) (-104704883 / 100000000) (Real.log (87743 / 250000)) := by
  have h := reflection_log_15539_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15540_neg : (125190337 / 250000000) ≤ -Real.log (1000000 / 1649977) ∧
    -Real.log (1000000 / 1649977) ≤ (500761349 / 1000000000) := by
  have h := checkLog_sound (w := (649977 / 2649977)) (n := 12)
    (lo := (125190337 / 250000000)) (hi := (500761349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1649977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1649977 / 1000000) = 1/(1000000 / 1649977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15540 : Bounds (125190337 / 250000000) (500761349 / 1000000000) (Real.log (1649977 / 1000000)) := by
  have h := reflection_log_15540_neg
  have he : Real.log (1649977 / 1000000) = -Real.log (1000000 / 1649977) := by
    rw [show ((1649977 / 1000000) : ℝ) = ((1000000 / 1649977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15541_neg : (1049756411 / 1000000000) ≤ -Real.log (350023 / 1000000) ∧
    -Real.log (350023 / 1000000) ≤ (1049756413 / 1000000000) := by
  have h := checkLog_sound (w := (149977 / 850023)) (n := 12)
    (lo := (356609231 / 1000000000)) (hi := (22288077 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 350023) = 1/(350023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15541 : Bounds (-1049756413 / 1000000000) (-1049756411 / 1000000000) (Real.log (350023 / 1000000)) := by
  have h := reflection_log_15541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15542_neg : (548995063 / 1000000000) ≤ -Real.log (577529899471 / 1000000000000) ∧
    -Real.log (577529899471 / 1000000000000) ≤ (68624383 / 125000000) := by
  have h := checkLog_sound (w := (422470100529 / 1577529899471)) (n := 12)
    (lo := (548995063 / 1000000000)) (hi := (68624383 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577529899471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577529899471) = 1/(577529899471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15542 : Bounds (-68624383 / 125000000) (-548995063 / 1000000000) (Real.log (577529899471 / 1000000000000)) := by
  have h := reflection_log_15542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15543_neg : (546862807 / 1000000000) ≤ -Real.log (36172665951 / 62500000000) ∧
    -Real.log (36172665951 / 62500000000) ≤ (68357851 / 125000000) := by
  have h := checkLog_sound (w := (26327334049 / 98672665951)) (n := 12)
    (lo := (546862807 / 1000000000)) (hi := (68357851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36172665951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36172665951) = 1/(36172665951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15543 : Bounds (-68357851 / 125000000) (-546862807 / 1000000000) (Real.log (36172665951 / 62500000000)) := by
  have h := reflection_log_15543_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15544_neg : (1547234853 / 1000000000) ≤ -Real.log (15625000000 / 73413441813) ∧
    -Real.log (15625000000 / 73413441813) ≤ (193404357 / 125000000) := by
  have h := checkLog_sound (w := (10913441813 / 135913441813)) (n := 12)
    (lo := (160940493 / 1000000000)) (hi := (80470247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73413441813 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(73413441813 / 62500000000) = 1/(15625000000 / 73413441813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15544 : Bounds (1547234853 / 1000000000) (193404357 / 125000000) (Real.log (73413441813 / 15625000000)) := by
  have h := reflection_log_15544_neg
  have he : Real.log (73413441813 / 15625000000) = -Real.log (15625000000 / 73413441813) := by
    rw [show ((73413441813 / 15625000000) : ℝ) = ((15625000000 / 73413441813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15545_neg : (1550517759 / 1000000000) ≤ -Real.log (500000000000 / 2356955114379) ∧
    -Real.log (500000000000 / 2356955114379) ≤ (775258881 / 500000000) := by
  have h := checkLog_sound (w := (356955114379 / 4356955114379)) (n := 12)
    (lo := (164223399 / 1000000000)) (hi := (821117 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2356955114379 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2356955114379 / 2000000000000) = 1/(500000000000 / 2356955114379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15545 : Bounds (1550517759 / 1000000000) (775258881 / 500000000) (Real.log (2356955114379 / 500000000000)) := by
  have h := reflection_log_15545_neg
  have he : Real.log (2356955114379 / 500000000000) = -Real.log (500000000000 / 2356955114379) := by
    rw [show ((2356955114379 / 500000000000) : ℝ) = ((500000000000 / 2356955114379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15546_neg : (5949640443 / 1000000000) ≤ -Real.log (125000000000 / 47951923076923) ∧
    -Real.log (125000000000 / 47951923076923) ≤ (1487410113 / 250000000) := by
  have h := checkLog_sound (w := (15951923076923 / 79951923076923)) (n := 12)
    (lo := (404463003 / 1000000000)) (hi := (101115751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47951923076923 / 32000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(47951923076923 / 32000000000000) = 1/(125000000000 / 47951923076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15546 : Bounds (5949640443 / 1000000000) (1487410113 / 250000000) (Real.log (47951923076923 / 125000000000)) := by
  have h := reflection_log_15546_neg
  have he : Real.log (47951923076923 / 125000000000) = -Real.log (125000000000 / 47951923076923) := by
    rw [show ((47951923076923 / 125000000000) : ℝ) = ((125000000000 / 47951923076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15547_neg : (1497240353 / 250000000) ≤ -Real.log (1 / 399) ∧
    -Real.log (1 / 399) ≤ (5988961421 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 655)) (n := 12)
    (lo := (110945993 / 250000000)) (hi := (443783973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 256) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(399 / 256) = 1/(1 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15547 : Bounds (1497240353 / 250000000) (5988961421 / 1000000000) (Real.log (399 / 1)) := by
  have h := reflection_log_15547_neg
  have he : Real.log (399 / 1) = -Real.log (1 / 399) := by
    rw [show ((399 / 1) : ℝ) = ((1 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15548_neg : (138148859 / 200000000) ≤ -Real.log (625 / 1247) ∧
    -Real.log (625 / 1247) ≤ (86343037 / 125000000) := by
  have h := checkLog_sound (w := (311 / 936)) (n := 12)
    (lo := (138148859 / 200000000)) (hi := (86343037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247 / 625) = 1/(625 / 1247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15548 : Bounds (138148859 / 200000000) (86343037 / 125000000) (Real.log (1247 / 625)) := by
  have h := reflection_log_15548_neg
  have he : Real.log (1247 / 625) = -Real.log (625 / 1247) := by
    rw [show ((1247 / 625) : ℝ) = ((625 / 1247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15549_neg : (5339139357 / 1000000000) ≤ -Real.log (3 / 625) ∧
    -Real.log (3 / 625) ≤ (1067827873 / 200000000) := by
  have h := checkLog_sound (w := (241 / 1009)) (n := 12)
    (lo := (487109097 / 1000000000)) (hi := (243554549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 384) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 384) = 1/(3 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15549 : Bounds (-1067827873 / 200000000) (-5339139357 / 1000000000) (Real.log (3 / 625)) := by
  have h := reflection_log_15549_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15550_neg : (198941 / 200000000) ≤ -Real.log (312500 / 312811) ∧
    -Real.log (312500 / 312811) ≤ (497353 / 500000000) := by
  have h := checkLog_sound (w := (311 / 625311)) (n := 12)
    (lo := (198941 / 200000000)) (hi := (497353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312811 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312811 / 312500) = 1/(312500 / 312811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15550 : Bounds (198941 / 200000000) (497353 / 500000000) (Real.log (312811 / 312500)) := by
  have h := reflection_log_15550_neg
  have he : Real.log (312811 / 312500) = -Real.log (312500 / 312811) := by
    rw [show ((312811 / 312500) : ℝ) = ((312500 / 312811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15551_neg : (199139 / 200000000) ≤ -Real.log (312189 / 312500) ∧
    -Real.log (312189 / 312500) ≤ (62231 / 62500000) := by
  have h := checkLog_sound (w := (311 / 624689)) (n := 12)
    (lo := (199139 / 200000000)) (hi := (62231 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312189) = 1/(312189 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15551 : Bounds (-62231 / 62500000) (-199139 / 200000000) (Real.log (312189 / 312500)) := by
  have h := reflection_log_15551_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0243 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15552_neg : (500382483 / 1000000000) ≤ -Real.log (125000 / 206169) ∧
    -Real.log (125000 / 206169) ≤ (125095621 / 250000000) := by
  have h := checkLog_sound (w := (81169 / 331169)) (n := 12)
    (lo := (500382483 / 1000000000)) (hi := (125095621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206169 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206169 / 125000) = 1/(125000 / 206169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15552 : Bounds (500382483 / 1000000000) (125095621 / 250000000) (Real.log (206169 / 125000)) := by
  have h := reflection_log_15552_neg
  have he : Real.log (206169 / 125000) = -Real.log (125000 / 206169) := by
    rw [show ((206169 / 125000) : ℝ) = ((125000 / 206169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15553_neg : (1047972407 / 1000000000) ≤ -Real.log (43831 / 125000) ∧
    -Real.log (43831 / 125000) ≤ (1047972409 / 1000000000) := by
  have h := checkLog_sound (w := (18669 / 106331)) (n := 12)
    (lo := (354825227 / 1000000000)) (hi := (88706307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43831) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 43831) = 1/(43831 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15553 : Bounds (-1047972409 / 1000000000) (-1047972407 / 1000000000) (Real.log (43831 / 125000)) := by
  have h := reflection_log_15553_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15554_neg : (500958907 / 1000000000) ≤ -Real.log (1000000 / 1650303) ∧
    -Real.log (1000000 / 1650303) ≤ (125239727 / 250000000) := by
  have h := checkLog_sound (w := (650303 / 2650303)) (n := 12)
    (lo := (500958907 / 1000000000)) (hi := (125239727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650303 / 1000000) = 1/(1000000 / 1650303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15554 : Bounds (500958907 / 1000000000) (125239727 / 250000000) (Real.log (1650303 / 1000000)) := by
  have h := reflection_log_15554_neg
  have he : Real.log (1650303 / 1000000) = -Real.log (1000000 / 1650303) := by
    rw [show ((1650303 / 1000000) : ℝ) = ((1000000 / 1650303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15555_neg : (1050688213 / 1000000000) ≤ -Real.log (349697 / 1000000) ∧
    -Real.log (349697 / 1000000) ≤ (210137643 / 200000000) := by
  have h := checkLog_sound (w := (150303 / 849697)) (n := 12)
    (lo := (357541033 / 1000000000)) (hi := (178770517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349697) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349697) = 1/(349697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15555 : Bounds (-210137643 / 200000000) (-1050688213 / 1000000000) (Real.log (349697 / 1000000)) := by
  have h := reflection_log_15555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15556_neg : (274864653 / 500000000) ≤ -Real.log (577106008191 / 1000000000000) ∧
    -Real.log (577106008191 / 1000000000000) ≤ (549729307 / 1000000000) := by
  have h := checkLog_sound (w := (422893991809 / 1577106008191)) (n := 12)
    (lo := (274864653 / 500000000)) (hi := (549729307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577106008191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577106008191) = 1/(577106008191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15556 : Bounds (-549729307 / 1000000000) (-274864653 / 500000000) (Real.log (577106008191 / 1000000000000)) := by
  have h := reflection_log_15556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15557_neg : (136897481 / 250000000) ≤ -Real.log (9036593439 / 15625000000) ∧
    -Real.log (9036593439 / 15625000000) ≤ (21903597 / 40000000) := by
  have h := checkLog_sound (w := (6588406561 / 24661593439)) (n := 12)
    (lo := (136897481 / 250000000)) (hi := (21903597 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9036593439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9036593439) = 1/(9036593439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15557 : Bounds (-21903597 / 40000000) (-136897481 / 250000000) (Real.log (9036593439 / 15625000000)) := by
  have h := reflection_log_15557_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15558_neg : (154835489 / 100000000) ≤ -Real.log (100000000000 / 470372567361) ∧
    -Real.log (100000000000 / 470372567361) ≤ (1548354893 / 1000000000) := by
  have h := checkLog_sound (w := (70372567361 / 870372567361)) (n := 12)
    (lo := (16206053 / 100000000)) (hi := (162060531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470372567361 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(470372567361 / 400000000000) = 1/(100000000000 / 470372567361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15558 : Bounds (154835489 / 100000000) (1548354893 / 1000000000) (Real.log (470372567361 / 100000000000)) := by
  have h := reflection_log_15558_neg
  have he : Real.log (470372567361 / 100000000000) = -Real.log (100000000000 / 470372567361) := by
    rw [show ((470372567361 / 100000000000) : ℝ) = ((100000000000 / 470372567361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15559_neg : (19395589 / 12500000) ≤ -Real.log (62500000000 / 294952308713) ∧
    -Real.log (62500000000 / 294952308713) ≤ (1551647123 / 1000000000) := by
  have h := checkLog_sound (w := (44952308713 / 544952308713)) (n := 12)
    (lo := (4133819 / 25000000)) (hi := (165352761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294952308713 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(294952308713 / 250000000000) = 1/(62500000000 / 294952308713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15559 : Bounds (19395589 / 12500000) (1551647123 / 1000000000) (Real.log (294952308713 / 62500000000)) := by
  have h := reflection_log_15559_neg
  have he : Real.log (294952308713 / 62500000000) = -Real.log (62500000000 / 294952308713) := by
    rw [show ((294952308713 / 62500000000) : ℝ) = ((62500000000 / 294952308713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15560_neg : (1507470913 / 250000000) ≤ -Real.log (250000000000 / 103916666666667) ∧
    -Real.log (250000000000 / 103916666666667) ≤ (6029883661 / 1000000000) := by
  have h := checkLog_sound (w := (39916666666667 / 167916666666667)) (n := 12)
    (lo := (121176553 / 250000000)) (hi := (484706213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103916666666667 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(103916666666667 / 64000000000000) = 1/(250000000000 / 103916666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15560 : Bounds (1507470913 / 250000000) (6029883661 / 1000000000) (Real.log (103916666666667 / 250000000000)) := by
  have h := reflection_log_15560_neg
  have he : Real.log (103916666666667 / 250000000000) = -Real.log (250000000000 / 103916666666667) := by
    rw [show ((103916666666667 / 250000000000) : ℝ) = ((250000000000 / 103916666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15561_neg : (690844531 / 1000000000) ≤ -Real.log (5000 / 9977) ∧
    -Real.log (5000 / 9977) ≤ (172711133 / 250000000) := by
  have h := checkLog_sound (w := (4977 / 14977)) (n := 12)
    (lo := (690844531 / 1000000000)) (hi := (172711133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9977 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9977 / 5000) = 1/(5000 / 9977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15561 : Bounds (690844531 / 1000000000) (172711133 / 250000000) (Real.log (9977 / 5000)) := by
  have h := reflection_log_15561_neg
  have he : Real.log (9977 / 5000) = -Real.log (5000 / 9977) := by
    rw [show ((9977 / 5000) : ℝ) = ((5000 / 9977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15562_neg : (5381698971 / 1000000000) ≤ -Real.log (23 / 5000) ∧
    -Real.log (23 / 5000) ≤ (5381698979 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 993)) (n := 12)
    (lo := (529668711 / 1000000000)) (hi := (66208589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 368) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 368) = 1/(23 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15562 : Bounds (-5381698979 / 1000000000) (-5381698971 / 1000000000) (Real.log (23 / 5000)) := by
  have h := reflection_log_15562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15563_neg : (124363 / 125000000) ≤ -Real.log (5000000 / 5004977) ∧
    -Real.log (5000000 / 5004977) ≤ (198981 / 200000000) := by
  have h := checkLog_sound (w := (4977 / 10004977)) (n := 12)
    (lo := (124363 / 125000000)) (hi := (198981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004977 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004977 / 5000000) = 1/(5000000 / 5004977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15563 : Bounds (124363 / 125000000) (198981 / 200000000) (Real.log (5004977 / 5000000)) := by
  have h := reflection_log_15563_neg
  have he : Real.log (5004977 / 5000000) = -Real.log (5000000 / 5004977) := by
    rw [show ((5004977 / 5000000) : ℝ) = ((5000000 / 5004977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15564_neg : (199179 / 200000000) ≤ -Real.log (4995023 / 5000000) ∧
    -Real.log (4995023 / 5000000) ≤ (124487 / 125000000) := by
  have h := checkLog_sound (w := (4977 / 9995023)) (n := 12)
    (lo := (199179 / 200000000)) (hi := (124487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995023) = 1/(4995023 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15564 : Bounds (-124487 / 125000000) (-199179 / 200000000) (Real.log (4995023 / 5000000)) := by
  have h := reflection_log_15564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15565_neg : (500580723 / 1000000000) ≤ -Real.log (1000000 / 1649679) ∧
    -Real.log (1000000 / 1649679) ≤ (125145181 / 250000000) := by
  have h := checkLog_sound (w := (649679 / 2649679)) (n := 12)
    (lo := (500580723 / 1000000000)) (hi := (125145181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1649679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1649679 / 1000000) = 1/(1000000 / 1649679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15565 : Bounds (500580723 / 1000000000) (125145181 / 250000000) (Real.log (1649679 / 1000000)) := by
  have h := reflection_log_15565_neg
  have he : Real.log (1649679 / 1000000) = -Real.log (1000000 / 1649679) := by
    rw [show ((1649679 / 1000000) : ℝ) = ((1000000 / 1649679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15566_neg : (1048905401 / 1000000000) ≤ -Real.log (350321 / 1000000) ∧
    -Real.log (350321 / 1000000) ≤ (1048905403 / 1000000000) := by
  have h := checkLog_sound (w := (149679 / 850321)) (n := 12)
    (lo := (355758221 / 1000000000)) (hi := (177879111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 350321) = 1/(350321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15566 : Bounds (-1048905403 / 1000000000) (-1048905401 / 1000000000) (Real.log (350321 / 1000000)) := by
  have h := reflection_log_15566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15567_neg : (501157639 / 1000000000) ≤ -Real.log (1000000 / 1650631) ∧
    -Real.log (1000000 / 1650631) ≤ (12528941 / 25000000) := by
  have h := checkLog_sound (w := (650631 / 2650631)) (n := 12)
    (lo := (501157639 / 1000000000)) (hi := (12528941 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650631 / 1000000) = 1/(1000000 / 1650631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15567 : Bounds (501157639 / 1000000000) (12528941 / 25000000) (Real.log (1650631 / 1000000)) := by
  have h := reflection_log_15567_neg
  have he : Real.log (1650631 / 1000000) = -Real.log (1000000 / 1650631) := by
    rw [show ((1650631 / 1000000) : ℝ) = ((1000000 / 1650631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15568_neg : (65726663 / 62500000) ≤ -Real.log (349369 / 1000000) ∧
    -Real.log (349369 / 1000000) ≤ (105162661 / 100000000) := by
  have h := checkLog_sound (w := (150631 / 849369)) (n := 12)
    (lo := (89619857 / 250000000)) (hi := (358479429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349369) = 1/(349369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15568 : Bounds (-105162661 / 100000000) (-65726663 / 62500000) (Real.log (349369 / 1000000)) := by
  have h := reflection_log_15568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15569_neg : (550468969 / 1000000000) ≤ -Real.log (576679301839 / 1000000000000) ∧
    -Real.log (576679301839 / 1000000000000) ≤ (55046897 / 100000000) := by
  have h := checkLog_sound (w := (423320698161 / 1576679301839)) (n := 12)
    (lo := (550468969 / 1000000000)) (hi := (55046897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 576679301839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 576679301839) = 1/(576679301839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15569 : Bounds (-55046897 / 100000000) (-550468969 / 1000000000) (Real.log (576679301839 / 1000000000000)) := by
  have h := reflection_log_15569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15570_neg : (274162339 / 500000000) ≤ -Real.log (577917196959 / 1000000000000) ∧
    -Real.log (577917196959 / 1000000000000) ≤ (548324679 / 1000000000) := by
  have h := checkLog_sound (w := (422082803041 / 1577917196959)) (n := 12)
    (lo := (274162339 / 500000000)) (hi := (548324679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577917196959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577917196959) = 1/(577917196959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15570 : Bounds (-548324679 / 1000000000) (-274162339 / 500000000) (Real.log (577917196959 / 1000000000000)) := by
  have h := reflection_log_15570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15571_neg : (387371531 / 250000000) ≤ -Real.log (250000000000 / 1177262425033) ∧
    -Real.log (250000000000 / 1177262425033) ≤ (1549486127 / 1000000000) := by
  have h := checkLog_sound (w := (177262425033 / 2177262425033)) (n := 12)
    (lo := (40797941 / 250000000)) (hi := (32638353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177262425033 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1177262425033 / 1000000000000) = 1/(250000000000 / 1177262425033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15571 : Bounds (387371531 / 250000000) (1549486127 / 1000000000) (Real.log (1177262425033 / 250000000000)) := by
  have h := reflection_log_15571_neg
  have he : Real.log (1177262425033 / 250000000000) = -Real.log (250000000000 / 1177262425033) := by
    rw [show ((1177262425033 / 250000000000) : ℝ) = ((250000000000 / 1177262425033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15572_neg : (776392123 / 500000000) ≤ -Real.log (250000000000 / 1181151590439) ∧
    -Real.log (250000000000 / 1181151590439) ≤ (1552784249 / 1000000000) := by
  have h := checkLog_sound (w := (181151590439 / 2181151590439)) (n := 12)
    (lo := (83244943 / 500000000)) (hi := (166489887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181151590439 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1181151590439 / 1000000000000) = 1/(250000000000 / 1181151590439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15572 : Bounds (776392123 / 500000000) (1552784249 / 1000000000) (Real.log (1181151590439 / 250000000000)) := by
  have h := reflection_log_15572_neg
  have he : Real.log (1181151590439 / 250000000000) = -Real.log (250000000000 / 1181151590439) := by
    rw [show ((1181151590439 / 250000000000) : ℝ) = ((250000000000 / 1181151590439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15573_neg : (1507470913 / 250000000) ≤ -Real.log (500000000000 / 207833333333333) ∧
    -Real.log (500000000000 / 207833333333333) ≤ (6029883661 / 1000000000) := by
  have h := checkLog_sound (w := (79833333333333 / 335833333333333)) (n := 12)
    (lo := (121176553 / 250000000)) (hi := (484706213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207833333333333 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(207833333333333 / 128000000000000) = 1/(500000000000 / 207833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15573 : Bounds (1507470913 / 250000000) (6029883661 / 1000000000) (Real.log (207833333333333 / 500000000000)) := by
  have h := reflection_log_15573_neg
  have he : Real.log (207833333333333 / 500000000000) = -Real.log (500000000000 / 207833333333333) := by
    rw [show ((207833333333333 / 500000000000) : ℝ) = ((500000000000 / 207833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15574_neg : (3036271751 / 500000000) ≤ -Real.log (500000000000 / 216891304347827) ∧
    -Real.log (500000000000 / 216891304347827) ≤ (6072543511 / 1000000000) := by
  have h := checkLog_sound (w := (88891304347827 / 344891304347827)) (n := 12)
    (lo := (263683031 / 500000000)) (hi := (527366063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216891304347827 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(216891304347827 / 128000000000000) = 1/(500000000000 / 216891304347827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15574 : Bounds (3036271751 / 500000000) (6072543511 / 1000000000) (Real.log (216891304347827 / 500000000000)) := by
  have h := reflection_log_15574_neg
  have he : Real.log (216891304347827 / 500000000000) = -Real.log (500000000000 / 216891304347827) := by
    rw [show ((216891304347827 / 500000000000) : ℝ) = ((500000000000 / 216891304347827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15575_neg : (690944757 / 1000000000) ≤ -Real.log (2500 / 4989) ∧
    -Real.log (2500 / 4989) ≤ (345472379 / 500000000) := by
  have h := checkLog_sound (w := (2489 / 7489)) (n := 12)
    (lo := (690944757 / 1000000000)) (hi := (345472379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4989 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4989 / 2500) = 1/(2500 / 4989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15575 : Bounds (690944757 / 1000000000) (345472379 / 500000000) (Real.log (4989 / 2500)) := by
  have h := reflection_log_15575_neg
  have he : Real.log (4989 / 2500) = -Real.log (2500 / 4989) := by
    rw [show ((4989 / 2500) : ℝ) = ((2500 / 4989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15576_neg : (2713075367 / 500000000) ≤ -Real.log (11 / 2500) ∧
    -Real.log (11 / 2500) ≤ (2713075371 / 500000000) := by
  have h := checkLog_sound (w := (273 / 977)) (n := 12)
    (lo := (287060237 / 500000000)) (hi := (22964819 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 352) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 352) = 1/(11 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15576 : Bounds (-2713075371 / 500000000) (-2713075367 / 500000000) (Real.log (11 / 2500)) := by
  have h := reflection_log_15576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15577_neg : (31097 / 31250000) ≤ -Real.log (2500000 / 2502489) ∧
    -Real.log (2500000 / 2502489) ≤ (199021 / 200000000) := by
  have h := checkLog_sound (w := (2489 / 5002489)) (n := 12)
    (lo := (31097 / 31250000)) (hi := (199021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502489 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502489 / 2500000) = 1/(2500000 / 2502489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15577 : Bounds (31097 / 31250000) (199021 / 200000000) (Real.log (2502489 / 2500000)) := by
  have h := reflection_log_15577_neg
  have he : Real.log (2502489 / 2500000) = -Real.log (2500000 / 2502489) := by
    rw [show ((2502489 / 2500000) : ℝ) = ((2500000 / 2502489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15578_neg : (199219 / 200000000) ≤ -Real.log (2497511 / 2500000) ∧
    -Real.log (2497511 / 2500000) ≤ (3891 / 3906250) := by
  have h := checkLog_sound (w := (2489 / 4997511)) (n := 12)
    (lo := (199219 / 200000000)) (hi := (3891 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497511) = 1/(2497511 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15578 : Bounds (-3891 / 3906250) (-199219 / 200000000) (Real.log (2497511 / 2500000)) := by
  have h := reflection_log_15578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15579_neg : (50077953 / 100000000) ≤ -Real.log (1000000 / 1650007) ∧
    -Real.log (1000000 / 1650007) ≤ (500779531 / 1000000000) := by
  have h := checkLog_sound (w := (650007 / 2650007)) (n := 12)
    (lo := (50077953 / 100000000)) (hi := (500779531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650007 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650007 / 1000000) = 1/(1000000 / 1650007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15579 : Bounds (50077953 / 100000000) (500779531 / 1000000000) (Real.log (1650007 / 1000000)) := by
  have h := reflection_log_15579_neg
  have he : Real.log (1650007 / 1000000) = -Real.log (1000000 / 1650007) := by
    rw [show ((1650007 / 1000000) : ℝ) = ((1000000 / 1650007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15580_neg : (262460531 / 250000000) ≤ -Real.log (349993 / 1000000) ∧
    -Real.log (349993 / 1000000) ≤ (524921063 / 500000000) := by
  have h := checkLog_sound (w := (150007 / 849993)) (n := 12)
    (lo := (11146717 / 31250000)) (hi := (71338989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349993) = 1/(349993 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15580 : Bounds (-524921063 / 500000000) (-262460531 / 250000000) (Real.log (349993 / 1000000)) := by
  have h := reflection_log_15580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15581_neg : (250678771 / 500000000) ≤ -Real.log (1000000 / 1650961) ∧
    -Real.log (1000000 / 1650961) ≤ (501357543 / 1000000000) := by
  have h := checkLog_sound (w := (650961 / 2650961)) (n := 12)
    (lo := (250678771 / 500000000)) (hi := (501357543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650961 / 1000000) = 1/(1000000 / 1650961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15581 : Bounds (250678771 / 500000000) (501357543 / 1000000000) (Real.log (1650961 / 1000000)) := by
  have h := reflection_log_15581_neg
  have he : Real.log (1650961 / 1000000) = -Real.log (1000000 / 1650961) := by
    rw [show ((1650961 / 1000000) : ℝ) = ((1000000 / 1650961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15582_neg : (526285807 / 500000000) ≤ -Real.log (349039 / 1000000) ∧
    -Real.log (349039 / 1000000) ≤ (32892863 / 31250000) := by
  have h := checkLog_sound (w := (150961 / 849039)) (n := 12)
    (lo := (179712217 / 500000000)) (hi := (71884887 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349039) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349039) = 1/(349039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15582 : Bounds (-32892863 / 31250000) (-526285807 / 500000000) (Real.log (349039 / 1000000)) := by
  have h := reflection_log_15582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15583_neg : (68901759 / 125000000) ≤ -Real.log (576249776479 / 1000000000000) ∧
    -Real.log (576249776479 / 1000000000000) ≤ (551214073 / 1000000000) := by
  have h := checkLog_sound (w := (423750223521 / 1576249776479)) (n := 12)
    (lo := (68901759 / 125000000)) (hi := (551214073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 576249776479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 576249776479) = 1/(576249776479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15583 : Bounds (-551214073 / 1000000000) (-68901759 / 125000000) (Real.log (576249776479 / 1000000000000)) := by
  have h := reflection_log_15583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15584_neg : (274531297 / 500000000) ≤ -Real.log (577490899951 / 1000000000000) ∧
    -Real.log (577490899951 / 1000000000000) ≤ (109812519 / 200000000) := by
  have h := checkLog_sound (w := (422509100049 / 1577490899951)) (n := 12)
    (lo := (274531297 / 500000000)) (hi := (109812519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577490899951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577490899951) = 1/(577490899951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15584 : Bounds (-109812519 / 200000000) (-274531297 / 500000000) (Real.log (577490899951 / 1000000000000)) := by
  have h := reflection_log_15584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15585_neg : (1550621653 / 1000000000) ≤ -Real.log (250000000000 / 1178600000571) ∧
    -Real.log (250000000000 / 1178600000571) ≤ (193827707 / 125000000) := by
  have h := checkLog_sound (w := (178600000571 / 2178600000571)) (n := 12)
    (lo := (164327293 / 1000000000)) (hi := (82163647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178600000571 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1178600000571 / 1000000000000) = 1/(250000000000 / 1178600000571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15585 : Bounds (1550621653 / 1000000000) (193827707 / 125000000) (Real.log (1178600000571 / 250000000000)) := by
  have h := reflection_log_15585_neg
  have he : Real.log (1178600000571 / 250000000000) = -Real.log (250000000000 / 1178600000571) := by
    rw [show ((1178600000571 / 250000000000) : ℝ) = ((250000000000 / 1178600000571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15586_neg : (388482289 / 250000000) ≤ -Real.log (31250000000 / 147813084641) ∧
    -Real.log (31250000000 / 147813084641) ≤ (1553929159 / 1000000000) := by
  have h := checkLog_sound (w := (22813084641 / 272813084641)) (n := 12)
    (lo := (41908699 / 250000000)) (hi := (167634797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147813084641 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(147813084641 / 125000000000) = 1/(31250000000 / 147813084641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15586 : Bounds (388482289 / 250000000) (1553929159 / 1000000000) (Real.log (147813084641 / 31250000000)) := by
  have h := reflection_log_15586_neg
  have he : Real.log (147813084641 / 31250000000) = -Real.log (31250000000 / 147813084641) := by
    rw [show ((147813084641 / 31250000000) : ℝ) = ((31250000000 / 147813084641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15587_neg : (3036271751 / 500000000) ≤ -Real.log (250000000000 / 108445652173913) ∧
    -Real.log (250000000000 / 108445652173913) ≤ (6072543511 / 1000000000) := by
  have h := checkLog_sound (w := (44445652173913 / 172445652173913)) (n := 12)
    (lo := (263683031 / 500000000)) (hi := (527366063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108445652173913 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(108445652173913 / 64000000000000) = 1/(250000000000 / 108445652173913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15587 : Bounds (3036271751 / 500000000) (6072543511 / 1000000000) (Real.log (108445652173913 / 250000000000)) := by
  have h := reflection_log_15587_neg
  have he : Real.log (108445652173913 / 250000000000) = -Real.log (250000000000 / 108445652173913) := by
    rw [show ((108445652173913 / 250000000000) : ℝ) = ((250000000000 / 108445652173913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15588_neg : (611709549 / 100000000) ≤ -Real.log (62500000000 / 28346590909091) ∧
    -Real.log (62500000000 / 28346590909091) ≤ (6117095499 / 1000000000) := by
  have h := checkLog_sound (w := (12346590909091 / 44346590909091)) (n := 12)
    (lo := (11438361 / 20000000)) (hi := (571918051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28346590909091 / 16000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(28346590909091 / 16000000000000) = 1/(62500000000 / 28346590909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15588 : Bounds (611709549 / 100000000) (6117095499 / 1000000000) (Real.log (28346590909091 / 62500000000)) := by
  have h := reflection_log_15588_neg
  have he : Real.log (28346590909091 / 62500000000) = -Real.log (62500000000 / 28346590909091) := by
    rw [show ((28346590909091 / 62500000000) : ℝ) = ((62500000000 / 28346590909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15589_neg : (172761243 / 250000000) ≤ -Real.log (5000 / 9979) ∧
    -Real.log (5000 / 9979) ≤ (691044973 / 1000000000) := by
  have h := checkLog_sound (w := (4979 / 14979)) (n := 12)
    (lo := (172761243 / 250000000)) (hi := (691044973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9979 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9979 / 5000) = 1/(5000 / 9979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15589 : Bounds (172761243 / 250000000) (691044973 / 1000000000) (Real.log (9979 / 5000)) := by
  have h := reflection_log_15589_neg
  have he : Real.log (9979 / 5000) = -Real.log (5000 / 9979) := by
    rw [show ((9979 / 5000) : ℝ) = ((5000 / 9979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15590_neg : (5472670749 / 1000000000) ≤ -Real.log (21 / 5000) ∧
    -Real.log (21 / 5000) ≤ (5472670757 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 961)) (n := 12)
    (lo := (620640489 / 1000000000)) (hi := (62064049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 336) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 336) = 1/(21 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15590 : Bounds (-5472670757 / 1000000000) (-5472670749 / 1000000000) (Real.log (21 / 5000)) := by
  have h := reflection_log_15590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15591_neg : (124413 / 125000000) ≤ -Real.log (5000000 / 5004979) ∧
    -Real.log (5000000 / 5004979) ≤ (199061 / 200000000) := by
  have h := checkLog_sound (w := (4979 / 10004979)) (n := 12)
    (lo := (124413 / 125000000)) (hi := (199061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004979 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004979 / 5000000) = 1/(5000000 / 5004979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15591 : Bounds (124413 / 125000000) (199061 / 200000000) (Real.log (5004979 / 5000000)) := by
  have h := reflection_log_15591_neg
  have he : Real.log (5004979 / 5000000) = -Real.log (5000000 / 5004979) := by
    rw [show ((5004979 / 5000000) : ℝ) = ((5000000 / 5004979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15592_neg : (124537 / 125000000) ≤ -Real.log (4995021 / 5000000) ∧
    -Real.log (4995021 / 5000000) ≤ (996297 / 1000000000) := by
  have h := checkLog_sound (w := (4979 / 9995021)) (n := 12)
    (lo := (124537 / 125000000)) (hi := (996297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995021) = 1/(4995021 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15592 : Bounds (-996297 / 1000000000) (-124537 / 125000000) (Real.log (4995021 / 5000000)) := by
  have h := reflection_log_15592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15593_neg : (500979509 / 1000000000) ≤ -Real.log (1000000 / 1650337) ∧
    -Real.log (1000000 / 1650337) ≤ (50097951 / 100000000) := by
  have h := checkLog_sound (w := (650337 / 2650337)) (n := 12)
    (lo := (500979509 / 1000000000)) (hi := (50097951 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650337 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650337 / 1000000) = 1/(1000000 / 1650337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15593 : Bounds (500979509 / 1000000000) (50097951 / 100000000) (Real.log (1650337 / 1000000)) := by
  have h := reflection_log_15593_neg
  have he : Real.log (1650337 / 1000000) = -Real.log (1000000 / 1650337) := by
    rw [show ((1650337 / 1000000) : ℝ) = ((1000000 / 1650337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15594_neg : (262696361 / 250000000) ≤ -Real.log (349663 / 1000000) ∧
    -Real.log (349663 / 1000000) ≤ (525392723 / 500000000) := by
  have h := checkLog_sound (w := (150337 / 849663)) (n := 12)
    (lo := (44704783 / 125000000)) (hi := (71527653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349663) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349663) = 1/(349663 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15594 : Bounds (-525392723 / 500000000) (-262696361 / 250000000) (Real.log (349663 / 1000000)) := by
  have h := reflection_log_15594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15595_neg : (501558617 / 1000000000) ≤ -Real.log (1000000 / 1651293) ∧
    -Real.log (1000000 / 1651293) ≤ (250779309 / 500000000) := by
  have h := checkLog_sound (w := (651293 / 2651293)) (n := 12)
    (lo := (501558617 / 1000000000)) (hi := (250779309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651293 / 1000000) = 1/(1000000 / 1651293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15595 : Bounds (501558617 / 1000000000) (250779309 / 500000000) (Real.log (1651293 / 1000000)) := by
  have h := reflection_log_15595_neg
  have he : Real.log (1651293 / 1000000) = -Real.log (1000000 / 1651293) := by
    rw [show ((1651293 / 1000000) : ℝ) = ((1000000 / 1651293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15596_neg : (4214093 / 4000000) ≤ -Real.log (348707 / 1000000) ∧
    -Real.log (348707 / 1000000) ≤ (263380813 / 250000000) := by
  have h := checkLog_sound (w := (151293 / 848707)) (n := 12)
    (lo := (36037607 / 100000000)) (hi := (360376071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348707) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348707) = 1/(348707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15596 : Bounds (-263380813 / 250000000) (-4214093 / 4000000) (Real.log (348707 / 1000000)) := by
  have h := reflection_log_15596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15597_neg : (551964633 / 1000000000) ≤ -Real.log (575817428151 / 1000000000000) ∧
    -Real.log (575817428151 / 1000000000000) ≤ (275982317 / 500000000) := by
  have h := checkLog_sound (w := (424182571849 / 1575817428151)) (n := 12)
    (lo := (551964633 / 1000000000)) (hi := (275982317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 575817428151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 575817428151) = 1/(575817428151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15597 : Bounds (-275982317 / 500000000) (-551964633 / 1000000000) (Real.log (575817428151 / 1000000000000)) := by
  have h := reflection_log_15597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15598_neg : (34362871 / 62500000) ≤ -Real.log (577061786431 / 1000000000000) ∧
    -Real.log (577061786431 / 1000000000000) ≤ (549805937 / 1000000000) := by
  have h := checkLog_sound (w := (422938213569 / 1577061786431)) (n := 12)
    (lo := (34362871 / 62500000)) (hi := (549805937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577061786431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577061786431) = 1/(577061786431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15598 : Bounds (-549805937 / 1000000000) (-34362871 / 62500000) (Real.log (577061786431 / 1000000000000)) := by
  have h := reflection_log_15598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15599_neg : (1551764953 / 1000000000) ≤ -Real.log (500000000000 / 2359896528943) ∧
    -Real.log (500000000000 / 2359896528943) ≤ (387941239 / 250000000) := by
  have h := checkLog_sound (w := (359896528943 / 4359896528943)) (n := 12)
    (lo := (165470593 / 1000000000)) (hi := (82735297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2359896528943 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2359896528943 / 2000000000000) = 1/(500000000000 / 2359896528943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15599 : Bounds (1551764953 / 1000000000) (387941239 / 250000000) (Real.log (2359896528943 / 500000000000)) := by
  have h := reflection_log_15599_neg
  have he : Real.log (2359896528943 / 500000000000) = -Real.log (500000000000 / 2359896528943) := by
    rw [show ((2359896528943 / 500000000000) : ℝ) = ((500000000000 / 2359896528943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15600_neg : (1555081867 / 1000000000) ≤ -Real.log (250000000000 / 1183868548667) ∧
    -Real.log (250000000000 / 1183868548667) ≤ (155508187 / 100000000) := by
  have h := checkLog_sound (w := (183868548667 / 2183868548667)) (n := 12)
    (lo := (168787507 / 1000000000)) (hi := (42196877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183868548667 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1183868548667 / 1000000000000) = 1/(250000000000 / 1183868548667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15600 : Bounds (1555081867 / 1000000000) (155508187 / 100000000) (Real.log (1183868548667 / 250000000000)) := by
  have h := reflection_log_15600_neg
  have he : Real.log (1183868548667 / 250000000000) = -Real.log (250000000000 / 1183868548667) := by
    rw [show ((1183868548667 / 250000000000) : ℝ) = ((250000000000 / 1183868548667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15601_neg : (611709549 / 100000000) ≤ -Real.log (500000000000 / 226772727272727) ∧
    -Real.log (500000000000 / 226772727272727) ≤ (6117095499 / 1000000000) := by
  have h := checkLog_sound (w := (98772727272727 / 354772727272727)) (n := 12)
    (lo := (11438361 / 20000000)) (hi := (571918051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226772727272727 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(226772727272727 / 128000000000000) = 1/(500000000000 / 226772727272727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15601 : Bounds (611709549 / 100000000) (6117095499 / 1000000000) (Real.log (226772727272727 / 500000000000)) := by
  have h := reflection_log_15601_neg
  have he : Real.log (226772727272727 / 500000000000) = -Real.log (500000000000 / 226772727272727) := by
    rw [show ((226772727272727 / 500000000000) : ℝ) = ((500000000000 / 226772727272727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15602_neg : (6163715721 / 1000000000) ≤ -Real.log (500000000000 / 237595238095239) ∧
    -Real.log (500000000000 / 237595238095239) ≤ (616371573 / 100000000) := by
  have h := checkLog_sound (w := (109595238095239 / 365595238095239)) (n := 12)
    (lo := (618538281 / 1000000000)) (hi := (309269141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237595238095239 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(237595238095239 / 128000000000000) = 1/(500000000000 / 237595238095239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15602 : Bounds (6163715721 / 1000000000) (616371573 / 100000000) (Real.log (237595238095239 / 500000000000)) := by
  have h := reflection_log_15602_neg
  have he : Real.log (237595238095239 / 500000000000) = -Real.log (500000000000 / 237595238095239) := by
    rw [show ((237595238095239 / 500000000000) : ℝ) = ((500000000000 / 237595238095239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15603_neg : (691145177 / 1000000000) ≤ -Real.log (250 / 499) ∧
    -Real.log (250 / 499) ≤ (345572589 / 500000000) := by
  have h := checkLog_sound (w := (249 / 749)) (n := 12)
    (lo := (691145177 / 1000000000)) (hi := (345572589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 250) = 1/(250 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15603 : Bounds (691145177 / 1000000000) (345572589 / 500000000) (Real.log (499 / 250)) := by
  have h := reflection_log_15603_neg
  have he : Real.log (499 / 250) = -Real.log (250 / 499) := by
    rw [show ((499 / 250) : ℝ) = ((250 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15604_neg : (5521460913 / 1000000000) ≤ -Real.log (1 / 250) ∧
    -Real.log (1 / 250) ≤ (5521460921 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(125 / 64) = 1/(1 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15604 : Bounds (-5521460921 / 1000000000) (-5521460913 / 1000000000) (Real.log (1 / 250)) := by
  have h := reflection_log_15604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15605_neg : (62219 / 62500000) ≤ -Real.log (250000 / 250249) ∧
    -Real.log (250000 / 250249) ≤ (199101 / 200000000) := by
  have h := checkLog_sound (w := (249 / 500249)) (n := 12)
    (lo := (62219 / 62500000)) (hi := (199101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250249 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250249 / 250000) = 1/(250000 / 250249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15605 : Bounds (62219 / 62500000) (199101 / 200000000) (Real.log (250249 / 250000)) := by
  have h := reflection_log_15605_neg
  have he : Real.log (250249 / 250000) = -Real.log (250000 / 250249) := by
    rw [show ((250249 / 250000) : ℝ) = ((250000 / 250249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15606_neg : (62281 / 62500000) ≤ -Real.log (249751 / 250000) ∧
    -Real.log (249751 / 250000) ≤ (996497 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 499751)) (n := 12)
    (lo := (62281 / 62500000)) (hi := (996497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249751) = 1/(249751 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15606 : Bounds (-996497 / 1000000000) (-62281 / 62500000) (Real.log (249751 / 250000)) := by
  have h := reflection_log_15606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15607_neg : (25059033 / 50000000) ≤ -Real.log (1000000 / 1650669) ∧
    -Real.log (1000000 / 1650669) ≤ (501180661 / 1000000000) := by
  have h := checkLog_sound (w := (650669 / 2650669)) (n := 12)
    (lo := (25059033 / 50000000)) (hi := (501180661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1650669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1650669 / 1000000) = 1/(1000000 / 1650669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15607 : Bounds (25059033 / 50000000) (501180661 / 1000000000) (Real.log (1650669 / 1000000)) := by
  have h := reflection_log_15607_neg
  have he : Real.log (1650669 / 1000000) = -Real.log (1000000 / 1650669) := by
    rw [show ((1650669 / 1000000) : ℝ) = ((1000000 / 1650669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15608_neg : (1051735381 / 1000000000) ≤ -Real.log (349331 / 1000000) ∧
    -Real.log (349331 / 1000000) ≤ (1051735383 / 1000000000) := by
  have h := checkLog_sound (w := (150669 / 849331)) (n := 12)
    (lo := (358588201 / 1000000000)) (hi := (179294101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349331) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 349331) = 1/(349331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15608 : Bounds (-1051735383 / 1000000000) (-1051735381 / 1000000000) (Real.log (349331 / 1000000)) := by
  have h := reflection_log_15608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15609_neg : (250880431 / 500000000) ≤ -Real.log (1000000 / 1651627) ∧
    -Real.log (1000000 / 1651627) ≤ (501760863 / 1000000000) := by
  have h := checkLog_sound (w := (651627 / 2651627)) (n := 12)
    (lo := (250880431 / 500000000)) (hi := (501760863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651627 / 1000000) = 1/(1000000 / 1651627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15609 : Bounds (250880431 / 500000000) (501760863 / 1000000000) (Real.log (1651627 / 1000000)) := by
  have h := reflection_log_15609_neg
  have he : Real.log (1651627 / 1000000) = -Real.log (1000000 / 1651627) := by
    rw [show ((1651627 / 1000000) : ℝ) = ((1000000 / 1651627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15610_neg : (1054481533 / 1000000000) ≤ -Real.log (348373 / 1000000) ∧
    -Real.log (348373 / 1000000) ≤ (210896307 / 200000000) := by
  have h := checkLog_sound (w := (151627 / 848373)) (n := 12)
    (lo := (361334353 / 1000000000)) (hi := (180667177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348373) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348373) = 1/(348373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15610 : Bounds (-210896307 / 200000000) (-1054481533 / 1000000000) (Real.log (348373 / 1000000)) := by
  have h := reflection_log_15610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15611_neg : (552720671 / 1000000000) ≤ -Real.log (575382252871 / 1000000000000) ∧
    -Real.log (575382252871 / 1000000000000) ≤ (17272521 / 31250000) := by
  have h := checkLog_sound (w := (424617747129 / 1575382252871)) (n := 12)
    (lo := (552720671 / 1000000000)) (hi := (17272521 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 575382252871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 575382252871) = 1/(575382252871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15611 : Bounds (-17272521 / 31250000) (-552720671 / 1000000000) (Real.log (575382252871 / 1000000000000)) := by
  have h := reflection_log_15611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15612_neg : (550554721 / 1000000000) ≤ -Real.log (576629852439 / 1000000000000) ∧
    -Real.log (576629852439 / 1000000000000) ≤ (275277361 / 500000000) := by
  have h := checkLog_sound (w := (423370147561 / 1576629852439)) (n := 12)
    (lo := (550554721 / 1000000000)) (hi := (275277361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 576629852439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 576629852439) = 1/(576629852439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15612 : Bounds (-275277361 / 500000000) (-550554721 / 1000000000) (Real.log (576629852439 / 1000000000000)) := by
  have h := reflection_log_15612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15613_neg : (1552916041 / 1000000000) ≤ -Real.log (125000000000 / 590653635091) ∧
    -Real.log (125000000000 / 590653635091) ≤ (388229011 / 250000000) := by
  have h := checkLog_sound (w := (90653635091 / 1090653635091)) (n := 12)
    (lo := (166621681 / 1000000000)) (hi := (83310841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590653635091 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(590653635091 / 500000000000) = 1/(125000000000 / 590653635091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15613 : Bounds (1552916041 / 1000000000) (388229011 / 250000000) (Real.log (590653635091 / 125000000000)) := by
  have h := reflection_log_15613_neg
  have he : Real.log (590653635091 / 125000000000) = -Real.log (125000000000 / 590653635091) := by
    rw [show ((590653635091 / 125000000000) : ℝ) = ((125000000000 / 590653635091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15614_neg : (311248479 / 200000000) ≤ -Real.log (500000000000 / 2370486518761) ∧
    -Real.log (500000000000 / 2370486518761) ≤ (778121199 / 500000000) := by
  have h := checkLog_sound (w := (370486518761 / 4370486518761)) (n := 12)
    (lo := (33989607 / 200000000)) (hi := (42487009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2370486518761 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2370486518761 / 2000000000000) = 1/(500000000000 / 2370486518761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15614 : Bounds (311248479 / 200000000) (778121199 / 500000000) (Real.log (2370486518761 / 500000000000)) := by
  have h := reflection_log_15614_neg
  have he : Real.log (2370486518761 / 500000000000) = -Real.log (500000000000 / 2370486518761) := by
    rw [show ((2370486518761 / 500000000000) : ℝ) = ((500000000000 / 2370486518761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15615_neg : (6163715721 / 1000000000) ≤ -Real.log (250000000000 / 118797619047619) ∧
    -Real.log (250000000000 / 118797619047619) ≤ (616371573 / 100000000) := by
  have h := checkLog_sound (w := (54797619047619 / 182797619047619)) (n := 12)
    (lo := (618538281 / 1000000000)) (hi := (309269141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118797619047619 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(118797619047619 / 64000000000000) = 1/(250000000000 / 118797619047619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15615 : Bounds (6163715721 / 1000000000) (616371573 / 100000000) (Real.log (118797619047619 / 250000000000)) := by
  have h := reflection_log_15615_neg
  have he : Real.log (118797619047619 / 250000000000) = -Real.log (250000000000 / 118797619047619) := by
    rw [show ((118797619047619 / 250000000000) : ℝ) = ((250000000000 / 118797619047619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


