-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4_q00
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0141__4_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:48:52.076634+00:00
-- url     : https://prove2.me/theorems/7a7636ce-14f4-45b1-86fe-04412bb06135
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 (+3 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0142, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0143, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0144) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0141 (+3 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0142, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0143, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0144) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0141 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9024_neg : (274037 / 1000000000) ≤ -Real.log (499863 / 500000) ∧
    -Real.log (499863 / 500000) ≤ (137019 / 500000000) := by
  have h := checkLog_sound (w := (137 / 999863)) (n := 12)
    (lo := (274037 / 1000000000)) (hi := (137019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499863) = 1/(499863 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9024 : Bounds (-137019 / 500000000) (-274037 / 1000000000) (Real.log (499863 / 500000)) := by
  have h := reflection_log_9024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9025_neg : (32428121 / 250000000) ≤ -Real.log (1000000 / 1138501) ∧
    -Real.log (1000000 / 1138501) ≤ (25942497 / 200000000) := by
  have h := checkLog_sound (w := (138501 / 2138501)) (n := 12)
    (lo := (32428121 / 250000000)) (hi := (25942497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138501 / 1000000) = 1/(1000000 / 1138501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9025 : Bounds (32428121 / 250000000) (25942497 / 200000000) (Real.log (1138501 / 1000000)) := by
  have h := reflection_log_9025_neg
  have he : Real.log (1138501 / 1000000) = -Real.log (1000000 / 1138501) := by
    rw [show ((1138501 / 1000000) : ℝ) = ((1000000 / 1138501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9026_neg : (149081383 / 1000000000) ≤ -Real.log (861499 / 1000000) ∧
    -Real.log (861499 / 1000000) ≤ (18635173 / 125000000) := by
  have h := checkLog_sound (w := (138501 / 1861499)) (n := 12)
    (lo := (149081383 / 1000000000)) (hi := (18635173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861499) = 1/(861499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9026 : Bounds (-18635173 / 125000000) (-149081383 / 1000000000) (Real.log (861499 / 1000000)) := by
  have h := reflection_log_9026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9027_neg : (65089389 / 500000000) ≤ -Real.log (125000 / 142379) ∧
    -Real.log (125000 / 142379) ≤ (130178779 / 1000000000) := by
  have h := checkLog_sound (w := (17379 / 267379)) (n := 12)
    (lo := (65089389 / 500000000)) (hi := (130178779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142379 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142379 / 125000) = 1/(125000 / 142379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9027 : Bounds (65089389 / 500000000) (130178779 / 1000000000) (Real.log (142379 / 125000)) := by
  have h := reflection_log_9027_neg
  have he : Real.log (142379 / 125000) = -Real.log (125000 / 142379) := by
    rw [show ((142379 / 125000) : ℝ) = ((125000 / 142379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9028_neg : (149697941 / 1000000000) ≤ -Real.log (107621 / 125000) ∧
    -Real.log (107621 / 125000) ≤ (74848971 / 500000000) := by
  have h := checkLog_sound (w := (17379 / 232621)) (n := 12)
    (lo := (149697941 / 1000000000)) (hi := (74848971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107621) = 1/(107621 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9028 : Bounds (-74848971 / 500000000) (-149697941 / 1000000000) (Real.log (107621 / 125000)) := by
  have h := reflection_log_9028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9029_neg : (9759581 / 500000000) ≤ -Real.log (15322970359 / 15625000000) ∧
    -Real.log (15322970359 / 15625000000) ≤ (19519163 / 1000000000) := by
  have h := checkLog_sound (w := (302029641 / 30947970359)) (n := 12)
    (lo := (9759581 / 500000000)) (hi := (19519163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15322970359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15322970359) = 1/(15322970359 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9029 : Bounds (-19519163 / 1000000000) (-9759581 / 500000000) (Real.log (15322970359 / 15625000000)) := by
  have h := reflection_log_9029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9030_neg : (9684449 / 500000000) ≤ -Real.log (980817472999 / 1000000000000) ∧
    -Real.log (980817472999 / 1000000000000) ≤ (19368899 / 1000000000) := by
  have h := checkLog_sound (w := (19182527001 / 1980817472999)) (n := 12)
    (lo := (9684449 / 500000000)) (hi := (19368899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980817472999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980817472999) = 1/(980817472999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9030 : Bounds (-19368899 / 1000000000) (-9684449 / 500000000) (Real.log (980817472999 / 1000000000000)) := by
  have h := reflection_log_9030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9031_neg : (69698467 / 250000000) ≤ -Real.log (500000000000 / 660767453009) ∧
    -Real.log (500000000000 / 660767453009) ≤ (278793869 / 1000000000) := by
  have h := checkLog_sound (w := (160767453009 / 1160767453009)) (n := 12)
    (lo := (69698467 / 250000000)) (hi := (278793869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660767453009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660767453009 / 500000000000) = 1/(500000000000 / 660767453009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9031 : Bounds (69698467 / 250000000) (278793869 / 1000000000) (Real.log (660767453009 / 500000000000)) := by
  have h := reflection_log_9031_neg
  have he : Real.log (660767453009 / 500000000000) = -Real.log (500000000000 / 660767453009) := by
    rw [show ((660767453009 / 500000000000) : ℝ) = ((500000000000 / 660767453009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9032_neg : (3498459 / 12500000) ≤ -Real.log (500000000000 / 661483353621) ∧
    -Real.log (500000000000 / 661483353621) ≤ (279876721 / 1000000000) := by
  have h := checkLog_sound (w := (161483353621 / 1161483353621)) (n := 12)
    (lo := (3498459 / 12500000)) (hi := (279876721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661483353621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661483353621 / 500000000000) = 1/(500000000000 / 661483353621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9032 : Bounds (3498459 / 12500000) (279876721 / 1000000000) (Real.log (661483353621 / 500000000000)) := by
  have h := reflection_log_9032_neg
  have he : Real.log (661483353621 / 500000000000) = -Real.log (500000000000 / 661483353621) := by
    rw [show ((661483353621 / 500000000000) : ℝ) = ((500000000000 / 661483353621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9033_neg : (561285811 / 1000000000) ≤ -Real.log (500000000000 / 876462491397) ∧
    -Real.log (500000000000 / 876462491397) ≤ (140321453 / 250000000) := by
  have h := checkLog_sound (w := (376462491397 / 1376462491397)) (n := 12)
    (lo := (561285811 / 1000000000)) (hi := (140321453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((876462491397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(876462491397 / 500000000000) = 1/(500000000000 / 876462491397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9033 : Bounds (561285811 / 1000000000) (140321453 / 250000000) (Real.log (876462491397 / 500000000000)) := by
  have h := reflection_log_9033_neg
  have he : Real.log (876462491397 / 500000000000) = -Real.log (500000000000 / 876462491397) := by
    rw [show ((876462491397 / 500000000000) : ℝ) = ((500000000000 / 876462491397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9034_neg : (562366821 / 1000000000) ≤ -Real.log (3125000000 / 5483815427) ∧
    -Real.log (3125000000 / 5483815427) ≤ (281183411 / 500000000) := by
  have h := checkLog_sound (w := (2358815427 / 8608815427)) (n := 12)
    (lo := (562366821 / 1000000000)) (hi := (281183411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5483815427 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5483815427 / 3125000000) = 1/(3125000000 / 5483815427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9034 : Bounds (562366821 / 1000000000) (281183411 / 500000000) (Real.log (5483815427 / 3125000000)) := by
  have h := reflection_log_9034_neg
  have he : Real.log (5483815427 / 3125000000) = -Real.log (3125000000 / 5483815427) := by
    rw [show ((5483815427 / 3125000000) : ℝ) = ((3125000000 / 5483815427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9035_neg : (30319243 / 125000000) ≤ -Real.log (2000 / 2549) ∧
    -Real.log (2000 / 2549) ≤ (48510789 / 200000000) := by
  have h := checkLog_sound (w := (549 / 4549)) (n := 12)
    (lo := (30319243 / 125000000)) (hi := (48510789 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2549 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2549 / 2000) = 1/(2000 / 2549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9035 : Bounds (30319243 / 125000000) (48510789 / 200000000) (Real.log (2549 / 2000)) := by
  have h := reflection_log_9035_neg
  have he : Real.log (2549 / 2000) = -Real.log (2000 / 2549) := by
    rw [show ((2549 / 2000) : ℝ) = ((2000 / 2549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9036_neg : (160447103 / 500000000) ≤ -Real.log (1451 / 2000) ∧
    -Real.log (1451 / 2000) ≤ (320894207 / 1000000000) := by
  have h := checkLog_sound (w := (549 / 3451)) (n := 12)
    (lo := (160447103 / 500000000)) (hi := (320894207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1451) = 1/(1451 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9036 : Bounds (-320894207 / 1000000000) (-160447103 / 500000000) (Real.log (1451 / 2000)) := by
  have h := reflection_log_9036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9037_neg : (137231 / 500000000) ≤ -Real.log (2000000 / 2000549) ∧
    -Real.log (2000000 / 2000549) ≤ (274463 / 1000000000) := by
  have h := checkLog_sound (w := (549 / 4000549)) (n := 12)
    (lo := (137231 / 500000000)) (hi := (274463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000549 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000549 / 2000000) = 1/(2000000 / 2000549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9037 : Bounds (137231 / 500000000) (274463 / 1000000000) (Real.log (2000549 / 2000000)) := by
  have h := reflection_log_9037_neg
  have he : Real.log (2000549 / 2000000) = -Real.log (2000000 / 2000549) := by
    rw [show ((2000549 / 2000000) : ℝ) = ((2000000 / 2000549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9038_neg : (274537 / 1000000000) ≤ -Real.log (1999451 / 2000000) ∧
    -Real.log (1999451 / 2000000) ≤ (137269 / 500000000) := by
  have h := checkLog_sound (w := (549 / 3999451)) (n := 12)
    (lo := (274537 / 1000000000)) (hi := (137269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999451) = 1/(1999451 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9038 : Bounds (-137269 / 500000000) (-274537 / 1000000000) (Real.log (1999451 / 2000000)) := by
  have h := reflection_log_9038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9039_neg : (129940829 / 1000000000) ≤ -Real.log (1000000 / 1138761) ∧
    -Real.log (1000000 / 1138761) ≤ (12994083 / 100000000) := by
  have h := checkLog_sound (w := (138761 / 2138761)) (n := 12)
    (lo := (129940829 / 1000000000)) (hi := (12994083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138761 / 1000000) = 1/(1000000 / 1138761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9039 : Bounds (129940829 / 1000000000) (12994083 / 100000000) (Real.log (1138761 / 1000000)) := by
  have h := reflection_log_9039_neg
  have he : Real.log (1138761 / 1000000) = -Real.log (1000000 / 1138761) := by
    rw [show ((1138761 / 1000000) : ℝ) = ((1000000 / 1138761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9040_neg : (37345807 / 250000000) ≤ -Real.log (861239 / 1000000) ∧
    -Real.log (861239 / 1000000) ≤ (149383229 / 1000000000) := by
  have h := checkLog_sound (w := (138761 / 1861239)) (n := 12)
    (lo := (37345807 / 250000000)) (hi := (149383229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861239) = 1/(861239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9040 : Bounds (-149383229 / 1000000000) (-37345807 / 250000000) (Real.log (861239 / 1000000)) := by
  have h := reflection_log_9040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9041_neg : (65203947 / 500000000) ≤ -Real.log (1000000 / 1139293) ∧
    -Real.log (1000000 / 1139293) ≤ (26081579 / 200000000) := by
  have h := checkLog_sound (w := (139293 / 2139293)) (n := 12)
    (lo := (65203947 / 500000000)) (hi := (26081579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1139293 / 1000000) = 1/(1000000 / 1139293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9041 : Bounds (65203947 / 500000000) (26081579 / 200000000) (Real.log (1139293 / 1000000)) := by
  have h := reflection_log_9041_neg
  have he : Real.log (1139293 / 1000000) = -Real.log (1000000 / 1139293) := by
    rw [show ((1139293 / 1000000) : ℝ) = ((1000000 / 1139293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9042_neg : (75000567 / 500000000) ≤ -Real.log (860707 / 1000000) ∧
    -Real.log (860707 / 1000000) ≤ (30000227 / 200000000) := by
  have h := checkLog_sound (w := (139293 / 1860707)) (n := 12)
    (lo := (75000567 / 500000000)) (hi := (30000227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 860707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 860707) = 1/(860707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9042 : Bounds (-30000227 / 200000000) (-75000567 / 500000000) (Real.log (860707 / 1000000)) := by
  have h := reflection_log_9042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9043_neg : (19593239 / 1000000000) ≤ -Real.log (980597460151 / 1000000000000) ∧
    -Real.log (980597460151 / 1000000000000) ≤ (489831 / 25000000) := by
  have h := checkLog_sound (w := (19402539849 / 1980597460151)) (n := 12)
    (lo := (19593239 / 1000000000)) (hi := (489831 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980597460151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980597460151) = 1/(980597460151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9043 : Bounds (-489831 / 25000000) (-19593239 / 1000000000) (Real.log (980597460151 / 1000000000000)) := by
  have h := reflection_log_9043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9044_neg : (19442399 / 1000000000) ≤ -Real.log (980745384879 / 1000000000000) ∧
    -Real.log (980745384879 / 1000000000000) ≤ (24303 / 1250000) := by
  have h := checkLog_sound (w := (19254615121 / 1980745384879)) (n := 12)
    (lo := (19442399 / 1000000000)) (hi := (24303 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980745384879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980745384879) = 1/(980745384879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9044 : Bounds (-24303 / 1250000) (-19442399 / 1000000000) (Real.log (980745384879 / 1000000000000)) := by
  have h := reflection_log_9044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9045_neg : (139662029 / 500000000) ≤ -Real.log (62500000000 / 82639734731) ∧
    -Real.log (62500000000 / 82639734731) ≤ (279324059 / 1000000000) := by
  have h := checkLog_sound (w := (20139734731 / 145139734731)) (n := 12)
    (lo := (139662029 / 500000000)) (hi := (279324059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82639734731 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82639734731 / 62500000000) = 1/(62500000000 / 82639734731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9045 : Bounds (139662029 / 500000000) (279324059 / 1000000000) (Real.log (82639734731 / 62500000000)) := by
  have h := reflection_log_9045_neg
  have he : Real.log (82639734731 / 62500000000) = -Real.log (62500000000 / 82639734731) := by
    rw [show ((82639734731 / 62500000000) : ℝ) = ((62500000000 / 82639734731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9046_neg : (280409029 / 1000000000) ≤ -Real.log (250000000000 / 330917780383) ∧
    -Real.log (250000000000 / 330917780383) ≤ (28040903 / 100000000) := by
  have h := checkLog_sound (w := (80917780383 / 580917780383)) (n := 12)
    (lo := (280409029 / 1000000000)) (hi := (28040903 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330917780383 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330917780383 / 250000000000) = 1/(250000000000 / 330917780383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9046 : Bounds (280409029 / 1000000000) (28040903 / 100000000) (Real.log (330917780383 / 250000000000)) := by
  have h := reflection_log_9046_neg
  have he : Real.log (330917780383 / 250000000000) = -Real.log (250000000000 / 330917780383) := by
    rw [show ((330917780383 / 250000000000) : ℝ) = ((250000000000 / 330917780383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9047_neg : (562366821 / 1000000000) ≤ -Real.log (500000000000 / 877410468319) ∧
    -Real.log (500000000000 / 877410468319) ≤ (281183411 / 500000000) := by
  have h := checkLog_sound (w := (377410468319 / 1377410468319)) (n := 12)
    (lo := (562366821 / 1000000000)) (hi := (281183411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((877410468319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(877410468319 / 500000000000) = 1/(500000000000 / 877410468319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9047 : Bounds (562366821 / 1000000000) (281183411 / 500000000) (Real.log (877410468319 / 500000000000)) := by
  have h := reflection_log_9047_neg
  have he : Real.log (877410468319 / 500000000000) = -Real.log (500000000000 / 877410468319) := by
    rw [show ((877410468319 / 500000000000) : ℝ) = ((500000000000 / 877410468319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9048_neg : (563448151 / 1000000000) ≤ -Real.log (62500000000 / 109794968987) ∧
    -Real.log (62500000000 / 109794968987) ≤ (70431019 / 125000000) := by
  have h := checkLog_sound (w := (47294968987 / 172294968987)) (n := 12)
    (lo := (563448151 / 1000000000)) (hi := (70431019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109794968987 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109794968987 / 62500000000) = 1/(62500000000 / 109794968987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9048 : Bounds (563448151 / 1000000000) (70431019 / 125000000) (Real.log (109794968987 / 62500000000)) := by
  have h := reflection_log_9048_neg
  have he : Real.log (109794968987 / 62500000000) = -Real.log (62500000000 / 109794968987) := by
    rw [show ((109794968987 / 62500000000) : ℝ) = ((62500000000 / 109794968987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9049_neg : (121473089 / 500000000) ≤ -Real.log (40 / 51) ∧
    -Real.log (40 / 51) ≤ (242946179 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 91)) (n := 12)
    (lo := (121473089 / 500000000)) (hi := (242946179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51 / 40) = 1/(40 / 51) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9049 : Bounds (121473089 / 500000000) (242946179 / 1000000000) (Real.log (51 / 40)) := by
  have h := reflection_log_9049_neg
  have he : Real.log (51 / 40) = -Real.log (40 / 51) := by
    rw [show ((51 / 40) : ℝ) = ((40 / 51) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9050_neg : (40197953 / 125000000) ≤ -Real.log (29 / 40) ∧
    -Real.log (29 / 40) ≤ (2572669 / 8000000) := by
  have h := checkLog_sound (w := (11 / 69)) (n := 12)
    (lo := (40197953 / 125000000)) (hi := (2572669 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 29) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 29) = 1/(29 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9050 : Bounds (-2572669 / 8000000) (-40197953 / 125000000) (Real.log (29 / 40)) := by
  have h := reflection_log_9050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9051_neg : (137481 / 500000000) ≤ -Real.log (40000 / 40011) ∧
    -Real.log (40000 / 40011) ≤ (274963 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 80011)) (n := 12)
    (lo := (137481 / 500000000)) (hi := (274963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40011 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40011 / 40000) = 1/(40000 / 40011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9051 : Bounds (137481 / 500000000) (274963 / 1000000000) (Real.log (40011 / 40000)) := by
  have h := reflection_log_9051_neg
  have he : Real.log (40011 / 40000) = -Real.log (40000 / 40011) := by
    rw [show ((40011 / 40000) : ℝ) = ((40000 / 40011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9052_neg : (275037 / 1000000000) ≤ -Real.log (39989 / 40000) ∧
    -Real.log (39989 / 40000) ≤ (137519 / 500000000) := by
  have h := checkLog_sound (w := (11 / 79989)) (n := 12)
    (lo := (275037 / 1000000000)) (hi := (137519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39989) = 1/(39989 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9052 : Bounds (-137519 / 500000000) (-275037 / 1000000000) (Real.log (39989 / 40000)) := by
  have h := reflection_log_9052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9053_neg : (130169999 / 1000000000) ≤ -Real.log (500000 / 569511) ∧
    -Real.log (500000 / 569511) ≤ (13017 / 100000) := by
  have h := checkLog_sound (w := (69511 / 1069511)) (n := 12)
    (lo := (130169999 / 1000000000)) (hi := (13017 / 100000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569511 / 500000) = 1/(500000 / 569511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9053 : Bounds (130169999 / 1000000000) (13017 / 100000) (Real.log (569511 / 500000)) := by
  have h := reflection_log_9053_neg
  have he : Real.log (569511 / 500000) = -Real.log (500000 / 569511) := by
    rw [show ((569511 / 500000) : ℝ) = ((500000 / 569511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9054_neg : (74843163 / 500000000) ≤ -Real.log (430489 / 500000) ∧
    -Real.log (430489 / 500000) ≤ (149686327 / 1000000000) := by
  have h := checkLog_sound (w := (69511 / 930489)) (n := 12)
    (lo := (74843163 / 500000000)) (hi := (149686327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430489) = 1/(430489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9054 : Bounds (-149686327 / 1000000000) (-74843163 / 500000000) (Real.log (430489 / 500000)) := by
  have h := reflection_log_9054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9055_neg : (130636957 / 1000000000) ≤ -Real.log (500000 / 569777) ∧
    -Real.log (500000 / 569777) ≤ (65318479 / 500000000) := by
  have h := checkLog_sound (w := (69777 / 1069777)) (n := 12)
    (lo := (130636957 / 1000000000)) (hi := (65318479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569777 / 500000) = 1/(500000 / 569777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9055 : Bounds (130636957 / 1000000000) (65318479 / 500000000) (Real.log (569777 / 500000)) := by
  have h := reflection_log_9055_neg
  have he : Real.log (569777 / 500000) = -Real.log (500000 / 569777) := by
    rw [show ((569777 / 500000) : ℝ) = ((500000 / 569777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9056_neg : (150304419 / 1000000000) ≤ -Real.log (430223 / 500000) ∧
    -Real.log (430223 / 500000) ≤ (7515221 / 50000000) := by
  have h := checkLog_sound (w := (69777 / 930223)) (n := 12)
    (lo := (150304419 / 1000000000)) (hi := (7515221 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430223) = 1/(430223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9056 : Bounds (-7515221 / 50000000) (-150304419 / 1000000000) (Real.log (430223 / 500000)) := by
  have h := reflection_log_9056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9057_neg : (19667461 / 1000000000) ≤ -Real.log (245131170271 / 250000000000) ∧
    -Real.log (245131170271 / 250000000000) ≤ (9833731 / 500000000) := by
  have h := checkLog_sound (w := (4868829729 / 495131170271)) (n := 12)
    (lo := (19667461 / 1000000000)) (hi := (9833731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245131170271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245131170271) = 1/(245131170271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9057 : Bounds (-9833731 / 500000000) (-19667461 / 1000000000) (Real.log (245131170271 / 250000000000)) := by
  have h := reflection_log_9057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9058_neg : (19516327 / 1000000000) ≤ -Real.log (245168220879 / 250000000000) ∧
    -Real.log (245168220879 / 250000000000) ≤ (2439541 / 125000000) := by
  have h := checkLog_sound (w := (4831779121 / 495168220879)) (n := 12)
    (lo := (19516327 / 1000000000)) (hi := (2439541 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245168220879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245168220879) = 1/(245168220879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9058 : Bounds (-2439541 / 125000000) (-19516327 / 1000000000) (Real.log (245168220879 / 250000000000)) := by
  have h := reflection_log_9058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9059_neg : (139928163 / 500000000) ≤ -Real.log (500000000000 / 661469863341) ∧
    -Real.log (500000000000 / 661469863341) ≤ (279856327 / 1000000000) := by
  have h := checkLog_sound (w := (161469863341 / 1161469863341)) (n := 12)
    (lo := (139928163 / 500000000)) (hi := (279856327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661469863341 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661469863341 / 500000000000) = 1/(500000000000 / 661469863341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9059 : Bounds (139928163 / 500000000) (279856327 / 1000000000) (Real.log (661469863341 / 500000000000)) := by
  have h := reflection_log_9059_neg
  have he : Real.log (661469863341 / 500000000000) = -Real.log (500000000000 / 661469863341) := by
    rw [show ((661469863341 / 500000000000) : ℝ) = ((500000000000 / 661469863341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9060_neg : (280941377 / 1000000000) ≤ -Real.log (250000000000 / 331093990791) ∧
    -Real.log (250000000000 / 331093990791) ≤ (140470689 / 500000000) := by
  have h := checkLog_sound (w := (81093990791 / 581093990791)) (n := 12)
    (lo := (280941377 / 1000000000)) (hi := (140470689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331093990791 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331093990791 / 250000000000) = 1/(250000000000 / 331093990791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9060 : Bounds (280941377 / 1000000000) (140470689 / 500000000) (Real.log (331093990791 / 250000000000)) := by
  have h := reflection_log_9060_neg
  have he : Real.log (331093990791 / 250000000000) = -Real.log (250000000000 / 331093990791) := by
    rw [show ((331093990791 / 250000000000) : ℝ) = ((250000000000 / 331093990791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9061_neg : (563448151 / 1000000000) ≤ -Real.log (100000000000 / 175671950379) ∧
    -Real.log (100000000000 / 175671950379) ≤ (70431019 / 125000000) := by
  have h := checkLog_sound (w := (75671950379 / 275671950379)) (n := 12)
    (lo := (563448151 / 1000000000)) (hi := (70431019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175671950379 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175671950379 / 100000000000) = 1/(100000000000 / 175671950379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9061 : Bounds (563448151 / 1000000000) (70431019 / 125000000) (Real.log (175671950379 / 100000000000)) := by
  have h := reflection_log_9061_neg
  have he : Real.log (175671950379 / 100000000000) = -Real.log (100000000000 / 175671950379) := by
    rw [show ((175671950379 / 100000000000) : ℝ) = ((100000000000 / 175671950379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9062_neg : (282264901 / 500000000) ≤ -Real.log (125000000000 / 219827586207) ∧
    -Real.log (125000000000 / 219827586207) ≤ (564529803 / 1000000000) := by
  have h := checkLog_sound (w := (94827586207 / 344827586207)) (n := 12)
    (lo := (282264901 / 500000000)) (hi := (564529803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219827586207 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219827586207 / 125000000000) = 1/(125000000000 / 219827586207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9062 : Bounds (282264901 / 500000000) (564529803 / 1000000000) (Real.log (219827586207 / 125000000000)) := by
  have h := reflection_log_9062_neg
  have he : Real.log (219827586207 / 125000000000) = -Real.log (125000000000 / 219827586207) := by
    rw [show ((219827586207 / 125000000000) : ℝ) = ((125000000000 / 219827586207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9063_neg : (121669129 / 500000000) ≤ -Real.log (2000 / 2551) ∧
    -Real.log (2000 / 2551) ≤ (243338259 / 1000000000) := by
  have h := checkLog_sound (w := (551 / 4551)) (n := 12)
    (lo := (121669129 / 500000000)) (hi := (243338259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2551 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2551 / 2000) = 1/(2000 / 2551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9063 : Bounds (121669129 / 500000000) (243338259 / 1000000000) (Real.log (2551 / 2000)) := by
  have h := reflection_log_9063_neg
  have he : Real.log (2551 / 2000) = -Real.log (2000 / 2551) := by
    rw [show ((2551 / 2000) : ℝ) = ((2000 / 2551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9064_neg : (322273517 / 1000000000) ≤ -Real.log (1449 / 2000) ∧
    -Real.log (1449 / 2000) ≤ (161136759 / 500000000) := by
  have h := checkLog_sound (w := (551 / 3449)) (n := 12)
    (lo := (322273517 / 1000000000)) (hi := (161136759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1449) = 1/(1449 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9064 : Bounds (-161136759 / 500000000) (-322273517 / 1000000000) (Real.log (1449 / 2000)) := by
  have h := reflection_log_9064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9065_neg : (137731 / 500000000) ≤ -Real.log (2000000 / 2000551) ∧
    -Real.log (2000000 / 2000551) ≤ (275463 / 1000000000) := by
  have h := checkLog_sound (w := (551 / 4000551)) (n := 12)
    (lo := (137731 / 500000000)) (hi := (275463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000551 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000551 / 2000000) = 1/(2000000 / 2000551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9065 : Bounds (137731 / 500000000) (275463 / 1000000000) (Real.log (2000551 / 2000000)) := by
  have h := reflection_log_9065_neg
  have he : Real.log (2000551 / 2000000) = -Real.log (2000000 / 2000551) := by
    rw [show ((2000551 / 2000000) : ℝ) = ((2000000 / 2000551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9066_neg : (275537 / 1000000000) ≤ -Real.log (1999449 / 2000000) ∧
    -Real.log (1999449 / 2000000) ≤ (137769 / 500000000) := by
  have h := checkLog_sound (w := (551 / 3999449)) (n := 12)
    (lo := (275537 / 1000000000)) (hi := (137769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999449) = 1/(1999449 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9066 : Bounds (-137769 / 500000000) (-275537 / 1000000000) (Real.log (1999449 / 2000000)) := by
  have h := reflection_log_9066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9067_neg : (130398239 / 1000000000) ≤ -Real.log (500000 / 569641) ∧
    -Real.log (500000 / 569641) ≤ (814989 / 6250000) := by
  have h := checkLog_sound (w := (69641 / 1069641)) (n := 12)
    (lo := (130398239 / 1000000000)) (hi := (814989 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569641 / 500000) = 1/(500000 / 569641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9067 : Bounds (130398239 / 1000000000) (814989 / 6250000) (Real.log (569641 / 500000)) := by
  have h := reflection_log_9067_neg
  have he : Real.log (569641 / 500000) = -Real.log (500000 / 569641) := by
    rw [show ((569641 / 500000) : ℝ) = ((500000 / 569641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9068_neg : (74994177 / 500000000) ≤ -Real.log (430359 / 500000) ∧
    -Real.log (430359 / 500000) ≤ (29997671 / 200000000) := by
  have h := checkLog_sound (w := (69641 / 930359)) (n := 12)
    (lo := (74994177 / 500000000)) (hi := (29997671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430359) = 1/(430359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9068 : Bounds (-29997671 / 200000000) (-74994177 / 500000000) (Real.log (430359 / 500000)) := by
  have h := reflection_log_9068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9069_neg : (8179123 / 62500000) ≤ -Real.log (200000 / 227963) ∧
    -Real.log (200000 / 227963) ≤ (130865969 / 1000000000) := by
  have h := checkLog_sound (w := (27963 / 427963)) (n := 12)
    (lo := (8179123 / 62500000)) (hi := (130865969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227963 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227963 / 200000) = 1/(200000 / 227963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9069 : Bounds (8179123 / 62500000) (130865969 / 1000000000) (Real.log (227963 / 200000)) := by
  have h := reflection_log_9069_neg
  have he : Real.log (227963 / 200000) = -Real.log (200000 / 227963) := by
    rw [show ((227963 / 200000) : ℝ) = ((200000 / 227963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9070_neg : (37651949 / 250000000) ≤ -Real.log (172037 / 200000) ∧
    -Real.log (172037 / 200000) ≤ (150607797 / 1000000000) := by
  have h := checkLog_sound (w := (27963 / 372037)) (n := 12)
    (lo := (37651949 / 250000000)) (hi := (150607797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 172037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 172037) = 1/(172037 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9070 : Bounds (-150607797 / 1000000000) (-37651949 / 250000000) (Real.log (172037 / 200000)) := by
  have h := reflection_log_9070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9071_neg : (4935457 / 250000000) ≤ -Real.log (39218070631 / 40000000000) ∧
    -Real.log (39218070631 / 40000000000) ≤ (19741829 / 1000000000) := by
  have h := checkLog_sound (w := (781929369 / 79218070631)) (n := 12)
    (lo := (4935457 / 250000000)) (hi := (19741829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39218070631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39218070631) = 1/(39218070631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9071 : Bounds (-19741829 / 1000000000) (-4935457 / 250000000) (Real.log (39218070631 / 40000000000)) := by
  have h := reflection_log_9071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9072_neg : (9795057 / 500000000) ≤ -Real.log (245150131119 / 250000000000) ∧
    -Real.log (245150131119 / 250000000000) ≤ (3918023 / 200000000) := by
  have h := checkLog_sound (w := (4849868881 / 495150131119)) (n := 12)
    (lo := (9795057 / 500000000)) (hi := (3918023 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245150131119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245150131119) = 1/(245150131119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9072 : Bounds (-3918023 / 200000000) (-9795057 / 500000000) (Real.log (245150131119 / 250000000000)) := by
  have h := reflection_log_9072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9073_neg : (280386593 / 1000000000) ≤ -Real.log (250000000000 / 330910356237) ∧
    -Real.log (250000000000 / 330910356237) ≤ (140193297 / 500000000) := by
  have h := checkLog_sound (w := (80910356237 / 580910356237)) (n := 12)
    (lo := (280386593 / 1000000000)) (hi := (140193297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330910356237 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330910356237 / 250000000000) = 1/(250000000000 / 330910356237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9073 : Bounds (280386593 / 1000000000) (140193297 / 500000000) (Real.log (330910356237 / 250000000000)) := by
  have h := reflection_log_9073_neg
  have he : Real.log (330910356237 / 250000000000) = -Real.log (250000000000 / 330910356237) := by
    rw [show ((330910356237 / 250000000000) : ℝ) = ((250000000000 / 330910356237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9074_neg : (56294753 / 200000000) ≤ -Real.log (500000000000 / 662540616263) ∧
    -Real.log (500000000000 / 662540616263) ≤ (140736883 / 500000000) := by
  have h := checkLog_sound (w := (162540616263 / 1162540616263)) (n := 12)
    (lo := (56294753 / 200000000)) (hi := (140736883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662540616263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(662540616263 / 500000000000) = 1/(500000000000 / 662540616263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9074 : Bounds (56294753 / 200000000) (140736883 / 500000000) (Real.log (662540616263 / 500000000000)) := by
  have h := reflection_log_9074_neg
  have he : Real.log (662540616263 / 500000000000) = -Real.log (500000000000 / 662540616263) := by
    rw [show ((662540616263 / 500000000000) : ℝ) = ((500000000000 / 662540616263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9075_neg : (282264901 / 500000000) ≤ -Real.log (500000000000 / 879310344827) ∧
    -Real.log (500000000000 / 879310344827) ≤ (564529803 / 1000000000) := by
  have h := checkLog_sound (w := (379310344827 / 1379310344827)) (n := 12)
    (lo := (282264901 / 500000000)) (hi := (564529803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879310344827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879310344827 / 500000000000) = 1/(500000000000 / 879310344827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9075 : Bounds (282264901 / 500000000) (564529803 / 1000000000) (Real.log (879310344827 / 500000000000)) := by
  have h := reflection_log_9075_neg
  have he : Real.log (879310344827 / 500000000000) = -Real.log (500000000000 / 879310344827) := by
    rw [show ((879310344827 / 500000000000) : ℝ) = ((500000000000 / 879310344827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9076_neg : (22624471 / 40000000) ≤ -Real.log (125000000000 / 220065562457) ∧
    -Real.log (125000000000 / 220065562457) ≤ (2209421 / 3906250) := by
  have h := checkLog_sound (w := (95065562457 / 345065562457)) (n := 12)
    (lo := (22624471 / 40000000)) (hi := (2209421 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220065562457 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220065562457 / 125000000000) = 1/(125000000000 / 220065562457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9076 : Bounds (22624471 / 40000000) (2209421 / 3906250) (Real.log (220065562457 / 125000000000)) := by
  have h := reflection_log_9076_neg
  have he : Real.log (220065562457 / 125000000000) = -Real.log (125000000000 / 220065562457) := by
    rw [show ((220065562457 / 125000000000) : ℝ) = ((125000000000 / 220065562457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9077_neg : (30466273 / 125000000) ≤ -Real.log (250 / 319) ∧
    -Real.log (250 / 319) ≤ (48746037 / 200000000) := by
  have h := checkLog_sound (w := (69 / 569)) (n := 12)
    (lo := (30466273 / 125000000)) (hi := (48746037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319 / 250) = 1/(250 / 319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9077 : Bounds (30466273 / 125000000) (48746037 / 200000000) (Real.log (319 / 250)) := by
  have h := reflection_log_9077_neg
  have he : Real.log (319 / 250) = -Real.log (250 / 319) := by
    rw [show ((319 / 250) : ℝ) = ((250 / 319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9078_neg : (161481943 / 500000000) ≤ -Real.log (181 / 250) ∧
    -Real.log (181 / 250) ≤ (322963887 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 431)) (n := 12)
    (lo := (161481943 / 500000000)) (hi := (322963887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 181) = 1/(181 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9078 : Bounds (-322963887 / 1000000000) (-161481943 / 500000000) (Real.log (181 / 250)) := by
  have h := reflection_log_9078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9079_neg : (275961 / 1000000000) ≤ -Real.log (250000 / 250069) ∧
    -Real.log (250000 / 250069) ≤ (137981 / 500000000) := by
  have h := checkLog_sound (w := (69 / 500069)) (n := 12)
    (lo := (275961 / 1000000000)) (hi := (137981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250069 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250069 / 250000) = 1/(250000 / 250069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9079 : Bounds (275961 / 1000000000) (137981 / 500000000) (Real.log (250069 / 250000)) := by
  have h := reflection_log_9079_neg
  have he : Real.log (250069 / 250000) = -Real.log (250000 / 250069) := by
    rw [show ((250069 / 250000) : ℝ) = ((250000 / 250069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9080_neg : (138019 / 500000000) ≤ -Real.log (249931 / 250000) ∧
    -Real.log (249931 / 250000) ≤ (276039 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 499931)) (n := 12)
    (lo := (138019 / 500000000)) (hi := (276039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249931) = 1/(249931 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9080 : Bounds (-276039 / 1000000000) (-138019 / 500000000) (Real.log (249931 / 250000)) := by
  have h := reflection_log_9080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9081_neg : (130626427 / 1000000000) ≤ -Real.log (500000 / 569771) ∧
    -Real.log (500000 / 569771) ≤ (32656607 / 250000000) := by
  have h := checkLog_sound (w := (69771 / 1069771)) (n := 12)
    (lo := (130626427 / 1000000000)) (hi := (32656607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569771 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569771 / 500000) = 1/(500000 / 569771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9081 : Bounds (130626427 / 1000000000) (32656607 / 250000000) (Real.log (569771 / 500000)) := by
  have h := reflection_log_9081_neg
  have he : Real.log (569771 / 500000) = -Real.log (500000 / 569771) := by
    rw [show ((569771 / 500000) : ℝ) = ((500000 / 569771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9082_neg : (150290473 / 1000000000) ≤ -Real.log (430229 / 500000) ∧
    -Real.log (430229 / 500000) ≤ (75145237 / 500000000) := by
  have h := checkLog_sound (w := (69771 / 930229)) (n := 12)
    (lo := (150290473 / 1000000000)) (hi := (75145237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430229) = 1/(430229 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9082 : Bounds (-75145237 / 500000000) (-150290473 / 1000000000) (Real.log (430229 / 500000)) := by
  have h := reflection_log_9082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9083_neg : (65547463 / 500000000) ≤ -Real.log (250000 / 285019) ∧
    -Real.log (250000 / 285019) ≤ (131094927 / 1000000000) := by
  have h := checkLog_sound (w := (35019 / 535019)) (n := 12)
    (lo := (65547463 / 500000000)) (hi := (131094927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285019 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285019 / 250000) = 1/(250000 / 285019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9083 : Bounds (65547463 / 500000000) (131094927 / 1000000000) (Real.log (285019 / 250000)) := by
  have h := reflection_log_9083_neg
  have he : Real.log (285019 / 250000) = -Real.log (250000 / 285019) := by
    rw [show ((285019 / 250000) : ℝ) = ((250000 / 285019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9084_neg : (30182253 / 200000000) ≤ -Real.log (214981 / 250000) ∧
    -Real.log (214981 / 250000) ≤ (75455633 / 500000000) := by
  have h := checkLog_sound (w := (35019 / 464981)) (n := 12)
    (lo := (30182253 / 200000000)) (hi := (75455633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 214981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 214981) = 1/(214981 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9084 : Bounds (-75455633 / 500000000) (-30182253 / 200000000) (Real.log (214981 / 250000)) := by
  have h := reflection_log_9084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9085_neg : (9908169 / 500000000) ≤ -Real.log (61273669639 / 62500000000) ∧
    -Real.log (61273669639 / 62500000000) ≤ (19816339 / 1000000000) := by
  have h := checkLog_sound (w := (1226330361 / 123773669639)) (n := 12)
    (lo := (9908169 / 500000000)) (hi := (19816339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61273669639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61273669639) = 1/(61273669639 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9085 : Bounds (-19816339 / 1000000000) (-9908169 / 500000000) (Real.log (61273669639 / 62500000000)) := by
  have h := reflection_log_9085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9086_neg : (9832023 / 500000000) ≤ -Real.log (245132007559 / 250000000000) ∧
    -Real.log (245132007559 / 250000000000) ≤ (19664047 / 1000000000) := by
  have h := checkLog_sound (w := (4867992441 / 495132007559)) (n := 12)
    (lo := (9832023 / 500000000)) (hi := (19664047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245132007559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245132007559) = 1/(245132007559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9086 : Bounds (-19664047 / 1000000000) (-9832023 / 500000000) (Real.log (245132007559 / 250000000000)) := by
  have h := reflection_log_9086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9087_neg : (2809169 / 10000000) ≤ -Real.log (125000000000 / 165542943409) ∧
    -Real.log (125000000000 / 165542943409) ≤ (280916901 / 1000000000) := by
  have h := checkLog_sound (w := (40542943409 / 290542943409)) (n := 12)
    (lo := (2809169 / 10000000)) (hi := (280916901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165542943409 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165542943409 / 125000000000) = 1/(125000000000 / 165542943409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9087 : Bounds (2809169 / 10000000) (280916901 / 1000000000) (Real.log (165542943409 / 125000000000)) := by
  have h := reflection_log_9087_neg
  have he : Real.log (165542943409 / 125000000000) = -Real.log (125000000000 / 165542943409) := by
    rw [show ((165542943409 / 125000000000) : ℝ) = ((125000000000 / 165542943409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


