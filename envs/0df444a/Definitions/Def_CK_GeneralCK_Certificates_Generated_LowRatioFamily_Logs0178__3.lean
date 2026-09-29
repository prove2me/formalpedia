-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0178__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0178__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T03:51:08.777827+00:00
-- url     : https://prove2.me/theorems/37244f4b-fa36-444f-a0da-ff2e55d44fa6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0178 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0179, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0178 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0179, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0180)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0178 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0179, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0180)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0178 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0179, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0180) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0178 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0179, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0180).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0178 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11392_neg : (222027513 / 250000000) ≤ -Real.log (50000000000 / 121526586621) ∧
    -Real.log (50000000000 / 121526586621) ≤ (444055027 / 500000000) := by
  have h := checkLog_sound (w := (21526586621 / 221526586621)) (n := 12)
    (lo := (24370359 / 125000000)) (hi := (194962873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121526586621 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(121526586621 / 100000000000) = 1/(50000000000 / 121526586621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11392 : Bounds (222027513 / 250000000) (444055027 / 500000000) (Real.log (121526586621 / 50000000000)) := by
  have h := reflection_log_11392_neg
  have he : Real.log (121526586621 / 50000000000) = -Real.log (50000000000 / 121526586621) := by
    rw [show ((121526586621 / 50000000000) : ℝ) = ((50000000000 / 121526586621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11393_neg : (87311857 / 250000000) ≤ -Real.log (500 / 709) ∧
    -Real.log (500 / 709) ≤ (349247429 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1209)) (n := 12)
    (lo := (87311857 / 250000000)) (hi := (349247429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709 / 500) = 1/(500 / 709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11393 : Bounds (87311857 / 250000000) (349247429 / 1000000000) (Real.log (709 / 500)) := by
  have h := reflection_log_11393_neg
  have he : Real.log (709 / 500) = -Real.log (500 / 709) := by
    rw [show ((709 / 500) : ℝ) = ((500 / 709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11394_neg : (541284831 / 1000000000) ≤ -Real.log (291 / 500) ∧
    -Real.log (291 / 500) ≤ (16915151 / 31250000) := by
  have h := checkLog_sound (w := (209 / 791)) (n := 12)
    (lo := (541284831 / 1000000000)) (hi := (16915151 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 291) = 1/(291 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11394 : Bounds (-16915151 / 31250000) (-541284831 / 1000000000) (Real.log (291 / 500)) := by
  have h := reflection_log_11394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11395_neg : (52239 / 125000000) ≤ -Real.log (500000 / 500209) ∧
    -Real.log (500000 / 500209) ≤ (417913 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1000209)) (n := 12)
    (lo := (52239 / 125000000)) (hi := (417913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500209 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500209 / 500000) = 1/(500000 / 500209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11395 : Bounds (52239 / 125000000) (417913 / 1000000000) (Real.log (500209 / 500000)) := by
  have h := reflection_log_11395_neg
  have he : Real.log (500209 / 500000) = -Real.log (500000 / 500209) := by
    rw [show ((500209 / 500000) : ℝ) = ((500000 / 500209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11396_neg : (418087 / 1000000000) ≤ -Real.log (499791 / 500000) ∧
    -Real.log (499791 / 500000) ≤ (52261 / 125000000) := by
  have h := checkLog_sound (w := (209 / 999791)) (n := 12)
    (lo := (418087 / 1000000000)) (hi := (52261 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499791) = 1/(499791 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11396 : Bounds (-52261 / 125000000) (-418087 / 1000000000) (Real.log (499791 / 500000)) := by
  have h := reflection_log_11396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11397_neg : (9745269 / 50000000) ≤ -Real.log (250000 / 303799) ∧
    -Real.log (250000 / 303799) ≤ (194905381 / 1000000000) := by
  have h := checkLog_sound (w := (53799 / 553799)) (n := 12)
    (lo := (9745269 / 50000000)) (hi := (194905381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303799 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303799 / 250000) = 1/(250000 / 303799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11397 : Bounds (9745269 / 50000000) (194905381 / 1000000000) (Real.log (303799 / 250000)) := by
  have h := reflection_log_11397_neg
  have he : Real.log (303799 / 250000) = -Real.log (250000 / 303799) := by
    rw [show ((303799 / 250000) : ℝ) = ((250000 / 303799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11398_neg : (242321273 / 1000000000) ≤ -Real.log (196201 / 250000) ∧
    -Real.log (196201 / 250000) ≤ (121160637 / 500000000) := by
  have h := checkLog_sound (w := (53799 / 446201)) (n := 12)
    (lo := (242321273 / 1000000000)) (hi := (121160637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196201) = 1/(196201 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11398 : Bounds (-121160637 / 500000000) (-242321273 / 1000000000) (Real.log (196201 / 250000)) := by
  have h := reflection_log_11398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11399_neg : (7827671 / 40000000) ≤ -Real.log (125000 / 152019) ∧
    -Real.log (125000 / 152019) ≤ (764421 / 3906250) := by
  have h := checkLog_sound (w := (27019 / 277019)) (n := 12)
    (lo := (7827671 / 40000000)) (hi := (764421 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152019 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152019 / 125000) = 1/(125000 / 152019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11399 : Bounds (7827671 / 40000000) (764421 / 3906250) (Real.log (152019 / 125000)) := by
  have h := reflection_log_11399_neg
  have he : Real.log (152019 / 125000) = -Real.log (125000 / 152019) := by
    rw [show ((152019 / 125000) : ℝ) = ((125000 / 152019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11400_neg : (121770077 / 500000000) ≤ -Real.log (97981 / 125000) ∧
    -Real.log (97981 / 125000) ≤ (48708031 / 200000000) := by
  have h := checkLog_sound (w := (27019 / 222981)) (n := 12)
    (lo := (121770077 / 500000000)) (hi := (48708031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97981) = 1/(97981 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11400 : Bounds (-48708031 / 200000000) (-121770077 / 500000000) (Real.log (97981 / 125000)) := by
  have h := reflection_log_11400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11401_neg : (47848379 / 1000000000) ≤ -Real.log (14894973639 / 15625000000) ∧
    -Real.log (14894973639 / 15625000000) ≤ (2392419 / 50000000) := by
  have h := checkLog_sound (w := (730026361 / 30519973639)) (n := 12)
    (lo := (47848379 / 1000000000)) (hi := (2392419 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14894973639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14894973639) = 1/(14894973639 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11401 : Bounds (-2392419 / 50000000) (-47848379 / 1000000000) (Real.log (14894973639 / 15625000000)) := by
  have h := reflection_log_11401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11402_neg : (47415893 / 1000000000) ≤ -Real.log (59605667599 / 62500000000) ∧
    -Real.log (59605667599 / 62500000000) ≤ (23707947 / 500000000) := by
  have h := checkLog_sound (w := (2894332401 / 122105667599)) (n := 12)
    (lo := (47415893 / 1000000000)) (hi := (23707947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59605667599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59605667599) = 1/(59605667599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11402 : Bounds (-23707947 / 500000000) (-47415893 / 1000000000) (Real.log (59605667599 / 62500000000)) := by
  have h := reflection_log_11402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11403_neg : (218613327 / 500000000) ≤ -Real.log (100000000000 / 154840699079) ∧
    -Real.log (100000000000 / 154840699079) ≤ (87445331 / 200000000) := by
  have h := checkLog_sound (w := (54840699079 / 254840699079)) (n := 12)
    (lo := (218613327 / 500000000)) (hi := (87445331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154840699079 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154840699079 / 100000000000) = 1/(100000000000 / 154840699079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11403 : Bounds (218613327 / 500000000) (87445331 / 200000000) (Real.log (154840699079 / 100000000000)) := by
  have h := reflection_log_11403_neg
  have he : Real.log (154840699079 / 100000000000) = -Real.log (100000000000 / 154840699079) := by
    rw [show ((154840699079 / 100000000000) : ℝ) = ((100000000000 / 154840699079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11404_neg : (43923193 / 100000000) ≤ -Real.log (500000000000 / 775757544831) ∧
    -Real.log (500000000000 / 775757544831) ≤ (439231931 / 1000000000) := by
  have h := checkLog_sound (w := (275757544831 / 1275757544831)) (n := 12)
    (lo := (43923193 / 100000000)) (hi := (439231931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775757544831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775757544831 / 500000000000) = 1/(500000000000 / 775757544831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11404 : Bounds (43923193 / 100000000) (439231931 / 1000000000) (Real.log (775757544831 / 500000000000)) := by
  have h := reflection_log_11404_neg
  have he : Real.log (775757544831 / 500000000000) = -Real.log (500000000000 / 775757544831) := by
    rw [show ((775757544831 / 500000000000) : ℝ) = ((500000000000 / 775757544831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11405_neg : (222027513 / 250000000) ≤ -Real.log (500000000000 / 1215265866209) ∧
    -Real.log (500000000000 / 1215265866209) ≤ (444055027 / 500000000) := by
  have h := checkLog_sound (w := (215265866209 / 2215265866209)) (n := 12)
    (lo := (24370359 / 125000000)) (hi := (194962873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215265866209 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1215265866209 / 1000000000000) = 1/(500000000000 / 1215265866209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11405 : Bounds (222027513 / 250000000) (444055027 / 500000000) (Real.log (1215265866209 / 500000000000)) := by
  have h := reflection_log_11405_neg
  have he : Real.log (1215265866209 / 500000000000) = -Real.log (500000000000 / 1215265866209) := by
    rw [show ((1215265866209 / 500000000000) : ℝ) = ((500000000000 / 1215265866209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11406_neg : (445266129 / 500000000) ≤ -Real.log (25000000000 / 60910652921) ∧
    -Real.log (25000000000 / 60910652921) ≤ (44526613 / 50000000) := by
  have h := checkLog_sound (w := (10910652921 / 110910652921)) (n := 12)
    (lo := (98692539 / 500000000)) (hi := (197385079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60910652921 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(60910652921 / 50000000000) = 1/(25000000000 / 60910652921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11406 : Bounds (445266129 / 500000000) (44526613 / 50000000) (Real.log (60910652921 / 25000000000)) := by
  have h := reflection_log_11406_neg
  have he : Real.log (60910652921 / 25000000000) = -Real.log (25000000000 / 60910652921) := by
    rw [show ((60910652921 / 25000000000) : ℝ) = ((25000000000 / 60910652921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11407_neg : (174976199 / 500000000) ≤ -Real.log (1000 / 1419) ∧
    -Real.log (1000 / 1419) ≤ (349952399 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2419)) (n := 12)
    (lo := (174976199 / 500000000)) (hi := (349952399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1419 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1419 / 1000) = 1/(1000 / 1419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11407 : Bounds (174976199 / 500000000) (349952399 / 1000000000) (Real.log (1419 / 1000)) := by
  have h := reflection_log_11407_neg
  have he : Real.log (1419 / 1000) = -Real.log (1000 / 1419) := by
    rw [show ((1419 / 1000) : ℝ) = ((1000 / 1419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11408_neg : (271502261 / 500000000) ≤ -Real.log (581 / 1000) ∧
    -Real.log (581 / 1000) ≤ (543004523 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 1581)) (n := 12)
    (lo := (271502261 / 500000000)) (hi := (543004523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 581) = 1/(581 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11408 : Bounds (-543004523 / 1000000000) (-271502261 / 500000000) (Real.log (581 / 1000)) := by
  have h := reflection_log_11408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11409_neg : (13091 / 31250000) ≤ -Real.log (1000000 / 1000419) ∧
    -Real.log (1000000 / 1000419) ≤ (418913 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2000419)) (n := 12)
    (lo := (13091 / 31250000)) (hi := (418913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000419 / 1000000) = 1/(1000000 / 1000419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11409 : Bounds (13091 / 31250000) (418913 / 1000000000) (Real.log (1000419 / 1000000)) := by
  have h := reflection_log_11409_neg
  have he : Real.log (1000419 / 1000000) = -Real.log (1000000 / 1000419) := by
    rw [show ((1000419 / 1000000) : ℝ) = ((1000000 / 1000419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11410_neg : (419087 / 1000000000) ≤ -Real.log (999581 / 1000000) ∧
    -Real.log (999581 / 1000000) ≤ (26193 / 62500000) := by
  have h := checkLog_sound (w := (419 / 1999581)) (n := 12)
    (lo := (419087 / 1000000000)) (hi := (26193 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999581) = 1/(999581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11410 : Bounds (-26193 / 62500000) (-419087 / 1000000000) (Real.log (999581 / 1000000)) := by
  have h := reflection_log_11410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11411_neg : (97679351 / 500000000) ≤ -Real.log (1000000 / 1215747) ∧
    -Real.log (1000000 / 1215747) ≤ (195358703 / 1000000000) := by
  have h := checkLog_sound (w := (215747 / 2215747)) (n := 12)
    (lo := (97679351 / 500000000)) (hi := (195358703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215747 / 1000000) = 1/(1000000 / 1215747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11411 : Bounds (97679351 / 500000000) (195358703 / 1000000000) (Real.log (1215747 / 1000000)) := by
  have h := reflection_log_11411_neg
  have he : Real.log (1215747 / 1000000) = -Real.log (1000000 / 1215747) := by
    rw [show ((1215747 / 1000000) : ℝ) = ((1000000 / 1215747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11412_neg : (121511803 / 500000000) ≤ -Real.log (784253 / 1000000) ∧
    -Real.log (784253 / 1000000) ≤ (243023607 / 1000000000) := by
  have h := checkLog_sound (w := (215747 / 1784253)) (n := 12)
    (lo := (121511803 / 500000000)) (hi := (243023607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784253) = 1/(784253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11412 : Bounds (-243023607 / 1000000000) (-121511803 / 500000000) (Real.log (784253 / 1000000)) := by
  have h := reflection_log_11412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11413_neg : (196145563 / 1000000000) ≤ -Real.log (15625 / 19011) ∧
    -Real.log (15625 / 19011) ≤ (49036391 / 250000000) := by
  have h := checkLog_sound (w := (1693 / 17318)) (n := 12)
    (lo := (196145563 / 1000000000)) (hi := (49036391 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19011 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19011 / 15625) = 1/(15625 / 19011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11413 : Bounds (196145563 / 1000000000) (49036391 / 250000000) (Real.log (19011 / 15625)) := by
  have h := reflection_log_11413_neg
  have he : Real.log (19011 / 15625) = -Real.log (15625 / 19011) := by
    rw [show ((19011 / 15625) : ℝ) = ((15625 / 19011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11414_neg : (244244621 / 1000000000) ≤ -Real.log (12239 / 15625) ∧
    -Real.log (12239 / 15625) ≤ (122122311 / 500000000) := by
  have h := checkLog_sound (w := (1693 / 13932)) (n := 12)
    (lo := (244244621 / 1000000000)) (hi := (122122311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12239) = 1/(12239 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11414 : Bounds (-122122311 / 500000000) (-244244621 / 1000000000) (Real.log (12239 / 15625)) := by
  have h := reflection_log_11414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11415_neg : (48099057 / 1000000000) ≤ -Real.log (232675629 / 244140625) ∧
    -Real.log (232675629 / 244140625) ≤ (24049529 / 500000000) := by
  have h := checkLog_sound (w := (5732498 / 238408127)) (n := 12)
    (lo := (48099057 / 1000000000)) (hi := (24049529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 232675629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 232675629) = 1/(232675629 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11415 : Bounds (-24049529 / 500000000) (-48099057 / 1000000000) (Real.log (232675629 / 244140625)) := by
  have h := reflection_log_11415_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11416_neg : (47664903 / 1000000000) ≤ -Real.log (953453231991 / 1000000000000) ∧
    -Real.log (953453231991 / 1000000000000) ≤ (5958113 / 125000000) := by
  have h := checkLog_sound (w := (46546768009 / 1953453231991)) (n := 12)
    (lo := (47664903 / 1000000000)) (hi := (5958113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 953453231991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 953453231991) = 1/(953453231991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11416 : Bounds (-5958113 / 125000000) (-47664903 / 1000000000) (Real.log (953453231991 / 1000000000000)) := by
  have h := reflection_log_11416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11417_neg : (438382309 / 1000000000) ≤ -Real.log (250000000000 / 387549362259) ∧
    -Real.log (250000000000 / 387549362259) ≤ (43838231 / 100000000) := by
  have h := checkLog_sound (w := (137549362259 / 637549362259)) (n := 12)
    (lo := (438382309 / 1000000000)) (hi := (43838231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387549362259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387549362259 / 250000000000) = 1/(250000000000 / 387549362259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11417 : Bounds (438382309 / 1000000000) (43838231 / 100000000) (Real.log (387549362259 / 250000000000)) := by
  have h := reflection_log_11417_neg
  have he : Real.log (387549362259 / 250000000000) = -Real.log (250000000000 / 387549362259) := by
    rw [show ((387549362259 / 250000000000) : ℝ) = ((250000000000 / 387549362259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11418_neg : (55048773 / 125000000) ≤ -Real.log (500000000000 / 776656589591) ∧
    -Real.log (500000000000 / 776656589591) ≤ (88078037 / 200000000) := by
  have h := checkLog_sound (w := (276656589591 / 1276656589591)) (n := 12)
    (lo := (55048773 / 125000000)) (hi := (88078037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776656589591 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776656589591 / 500000000000) = 1/(500000000000 / 776656589591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11418 : Bounds (55048773 / 125000000) (88078037 / 200000000) (Real.log (776656589591 / 500000000000)) := by
  have h := reflection_log_11418_neg
  have he : Real.log (776656589591 / 500000000000) = -Real.log (500000000000 / 776656589591) := by
    rw [show ((776656589591 / 500000000000) : ℝ) = ((500000000000 / 776656589591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11419_neg : (445266129 / 500000000) ≤ -Real.log (500000000000 / 1218213058419) ∧
    -Real.log (500000000000 / 1218213058419) ≤ (44526613 / 50000000) := by
  have h := checkLog_sound (w := (218213058419 / 2218213058419)) (n := 12)
    (lo := (98692539 / 500000000)) (hi := (197385079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218213058419 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1218213058419 / 1000000000000) = 1/(500000000000 / 1218213058419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11419 : Bounds (445266129 / 500000000) (44526613 / 50000000) (Real.log (1218213058419 / 500000000000)) := by
  have h := reflection_log_11419_neg
  have he : Real.log (1218213058419 / 500000000000) = -Real.log (500000000000 / 1218213058419) := by
    rw [show ((1218213058419 / 500000000000) : ℝ) = ((500000000000 / 1218213058419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11420_neg : (892956919 / 1000000000) ≤ -Real.log (50000000000 / 122117039587) ∧
    -Real.log (50000000000 / 122117039587) ≤ (892956921 / 1000000000) := by
  have h := checkLog_sound (w := (22117039587 / 222117039587)) (n := 12)
    (lo := (199809739 / 1000000000)) (hi := (9990487 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122117039587 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(122117039587 / 100000000000) = 1/(50000000000 / 122117039587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11420 : Bounds (892956919 / 1000000000) (892956921 / 1000000000) (Real.log (122117039587 / 50000000000)) := by
  have h := reflection_log_11420_neg
  have he : Real.log (122117039587 / 50000000000) = -Real.log (50000000000 / 122117039587) := by
    rw [show ((122117039587 / 50000000000) : ℝ) = ((50000000000 / 122117039587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11421_neg : (350656871 / 1000000000) ≤ -Real.log (50 / 71) ∧
    -Real.log (50 / 71) ≤ (43832109 / 125000000) := by
  have h := checkLog_sound (w := (21 / 121)) (n := 12)
    (lo := (350656871 / 1000000000)) (hi := (43832109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71 / 50) = 1/(50 / 71) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11421 : Bounds (350656871 / 1000000000) (43832109 / 125000000) (Real.log (71 / 50)) := by
  have h := reflection_log_11421_neg
  have he : Real.log (71 / 50) = -Real.log (50 / 71) := by
    rw [show ((71 / 50) : ℝ) = ((50 / 71) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11422_neg : (21789087 / 40000000) ≤ -Real.log (29 / 50) ∧
    -Real.log (29 / 50) ≤ (68090897 / 125000000) := by
  have h := checkLog_sound (w := (21 / 79)) (n := 12)
    (lo := (21789087 / 40000000)) (hi := (68090897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 29) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 29) = 1/(29 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11422 : Bounds (-68090897 / 125000000) (-21789087 / 40000000) (Real.log (29 / 50)) := by
  have h := reflection_log_11422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11423_neg : (419911 / 1000000000) ≤ -Real.log (50000 / 50021) ∧
    -Real.log (50000 / 50021) ≤ (52489 / 125000000) := by
  have h := checkLog_sound (w := (21 / 100021)) (n := 12)
    (lo := (419911 / 1000000000)) (hi := (52489 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50021 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50021 / 50000) = 1/(50000 / 50021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11423 : Bounds (419911 / 1000000000) (52489 / 125000000) (Real.log (50021 / 50000)) := by
  have h := reflection_log_11423_neg
  have he : Real.log (50021 / 50000) = -Real.log (50000 / 50021) := by
    rw [show ((50021 / 50000) : ℝ) = ((50000 / 50021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11424_neg : (52511 / 125000000) ≤ -Real.log (49979 / 50000) ∧
    -Real.log (49979 / 50000) ≤ (420089 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 99979)) (n := 12)
    (lo := (52511 / 125000000)) (hi := (420089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49979) = 1/(49979 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11424 : Bounds (-420089 / 1000000000) (-52511 / 125000000) (Real.log (49979 / 50000)) := by
  have h := reflection_log_11424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11425_neg : (195812641 / 1000000000) ≤ -Real.log (1000000 / 1216299) ∧
    -Real.log (1000000 / 1216299) ≤ (97906321 / 500000000) := by
  have h := checkLog_sound (w := (216299 / 2216299)) (n := 12)
    (lo := (195812641 / 1000000000)) (hi := (97906321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1216299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1216299 / 1000000) = 1/(1000000 / 1216299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11425 : Bounds (195812641 / 1000000000) (97906321 / 500000000) (Real.log (1216299 / 1000000)) := by
  have h := reflection_log_11425_neg
  have he : Real.log (1216299 / 1000000) = -Real.log (1000000 / 1216299) := by
    rw [show ((1216299 / 1000000) : ℝ) = ((1000000 / 1216299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11426_neg : (60931927 / 250000000) ≤ -Real.log (783701 / 1000000) ∧
    -Real.log (783701 / 1000000) ≤ (243727709 / 1000000000) := by
  have h := checkLog_sound (w := (216299 / 1783701)) (n := 12)
    (lo := (60931927 / 250000000)) (hi := (243727709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 783701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 783701) = 1/(783701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11426 : Bounds (-243727709 / 1000000000) (-60931927 / 250000000) (Real.log (783701 / 1000000)) := by
  have h := reflection_log_11426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11427_neg : (39319829 / 200000000) ≤ -Real.log (125000 / 152157) ∧
    -Real.log (125000 / 152157) ≤ (98299573 / 500000000) := by
  have h := checkLog_sound (w := (27157 / 277157)) (n := 12)
    (lo := (39319829 / 200000000)) (hi := (98299573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152157 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152157 / 125000) = 1/(125000 / 152157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11427 : Bounds (39319829 / 200000000) (98299573 / 500000000) (Real.log (152157 / 125000)) := by
  have h := reflection_log_11427_neg
  have he : Real.log (152157 / 125000) = -Real.log (125000 / 152157) := by
    rw [show ((152157 / 125000) : ℝ) = ((125000 / 152157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11428_neg : (15309349 / 62500000) ≤ -Real.log (97843 / 125000) ∧
    -Real.log (97843 / 125000) ≤ (48989917 / 200000000) := by
  have h := checkLog_sound (w := (27157 / 222843)) (n := 12)
    (lo := (15309349 / 62500000)) (hi := (48989917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97843) = 1/(97843 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11428 : Bounds (-48989917 / 200000000) (-15309349 / 62500000) (Real.log (97843 / 125000)) := by
  have h := reflection_log_11428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11429_neg : (24175219 / 500000000) ≤ -Real.log (14887497351 / 15625000000) ∧
    -Real.log (14887497351 / 15625000000) ≤ (48350439 / 1000000000) := by
  have h := checkLog_sound (w := (737502649 / 30512497351)) (n := 12)
    (lo := (24175219 / 500000000)) (hi := (48350439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14887497351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14887497351) = 1/(14887497351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11429 : Bounds (-48350439 / 1000000000) (-24175219 / 500000000) (Real.log (14887497351 / 15625000000)) := by
  have h := reflection_log_11429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11430_neg : (47915067 / 1000000000) ≤ -Real.log (953214742599 / 1000000000000) ∧
    -Real.log (953214742599 / 1000000000000) ≤ (11978767 / 250000000) := by
  have h := checkLog_sound (w := (46785257401 / 1953214742599)) (n := 12)
    (lo := (47915067 / 1000000000)) (hi := (11978767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 953214742599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 953214742599) = 1/(953214742599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11430 : Bounds (-11978767 / 250000000) (-47915067 / 1000000000) (Real.log (953214742599 / 1000000000000)) := by
  have h := reflection_log_11430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11431_neg : (8790807 / 20000000) ≤ -Real.log (500000000000 / 775996840631) ∧
    -Real.log (500000000000 / 775996840631) ≤ (439540351 / 1000000000) := by
  have h := checkLog_sound (w := (275996840631 / 1275996840631)) (n := 12)
    (lo := (8790807 / 20000000)) (hi := (439540351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775996840631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775996840631 / 500000000000) = 1/(500000000000 / 775996840631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11431 : Bounds (8790807 / 20000000) (439540351 / 1000000000) (Real.log (775996840631 / 500000000000)) := by
  have h := reflection_log_11431_neg
  have he : Real.log (775996840631 / 500000000000) = -Real.log (500000000000 / 775996840631) := by
    rw [show ((775996840631 / 500000000000) : ℝ) = ((500000000000 / 775996840631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11432_neg : (441548729 / 1000000000) ≤ -Real.log (100000000000 / 155511380477) ∧
    -Real.log (100000000000 / 155511380477) ≤ (44154873 / 100000000) := by
  have h := checkLog_sound (w := (55511380477 / 255511380477)) (n := 12)
    (lo := (441548729 / 1000000000)) (hi := (44154873 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155511380477 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155511380477 / 100000000000) = 1/(100000000000 / 155511380477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11432 : Bounds (441548729 / 1000000000) (44154873 / 100000000) (Real.log (155511380477 / 100000000000)) := by
  have h := reflection_log_11432_neg
  have he : Real.log (155511380477 / 100000000000) = -Real.log (100000000000 / 155511380477) := by
    rw [show ((155511380477 / 100000000000) : ℝ) = ((100000000000 / 155511380477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11433_neg : (892956919 / 1000000000) ≤ -Real.log (500000000000 / 1221170395869) ∧
    -Real.log (500000000000 / 1221170395869) ≤ (892956921 / 1000000000) := by
  have h := checkLog_sound (w := (221170395869 / 2221170395869)) (n := 12)
    (lo := (199809739 / 1000000000)) (hi := (9990487 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221170395869 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1221170395869 / 1000000000000) = 1/(500000000000 / 1221170395869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11433 : Bounds (892956919 / 1000000000) (892956921 / 1000000000) (Real.log (1221170395869 / 500000000000)) := by
  have h := reflection_log_11433_neg
  have he : Real.log (1221170395869 / 500000000000) = -Real.log (500000000000 / 1221170395869) := by
    rw [show ((1221170395869 / 500000000000) : ℝ) = ((500000000000 / 1221170395869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11434_neg : (447692023 / 500000000) ≤ -Real.log (100000000000 / 244827586207) ∧
    -Real.log (100000000000 / 244827586207) ≤ (55961503 / 62500000) := by
  have h := checkLog_sound (w := (44827586207 / 444827586207)) (n := 12)
    (lo := (101118433 / 500000000)) (hi := (202236867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244827586207 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(244827586207 / 200000000000) = 1/(100000000000 / 244827586207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11434 : Bounds (447692023 / 500000000) (55961503 / 62500000) (Real.log (244827586207 / 100000000000)) := by
  have h := reflection_log_11434_neg
  have he : Real.log (244827586207 / 100000000000) = -Real.log (100000000000 / 244827586207) := by
    rw [show ((244827586207 / 100000000000) : ℝ) = ((100000000000 / 244827586207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11435_neg : (351360849 / 1000000000) ≤ -Real.log (1000 / 1421) ∧
    -Real.log (1000 / 1421) ≤ (7027217 / 20000000) := by
  have h := checkLog_sound (w := (421 / 2421)) (n := 12)
    (lo := (351360849 / 1000000000)) (hi := (7027217 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421 / 1000) = 1/(1000 / 1421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11435 : Bounds (351360849 / 1000000000) (7027217 / 20000000) (Real.log (1421 / 1000)) := by
  have h := reflection_log_11435_neg
  have he : Real.log (1421 / 1000) = -Real.log (1000 / 1421) := by
    rw [show ((1421 / 1000) : ℝ) = ((1000 / 1421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11436_neg : (546452801 / 1000000000) ≤ -Real.log (579 / 1000) ∧
    -Real.log (579 / 1000) ≤ (273226401 / 500000000) := by
  have h := checkLog_sound (w := (421 / 1579)) (n := 12)
    (lo := (546452801 / 1000000000)) (hi := (273226401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 579) = 1/(579 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11436 : Bounds (-273226401 / 500000000) (-546452801 / 1000000000) (Real.log (579 / 1000)) := by
  have h := reflection_log_11436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11437_neg : (420911 / 1000000000) ≤ -Real.log (1000000 / 1000421) ∧
    -Real.log (1000000 / 1000421) ≤ (26307 / 62500000) := by
  have h := checkLog_sound (w := (421 / 2000421)) (n := 12)
    (lo := (420911 / 1000000000)) (hi := (26307 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000421 / 1000000) = 1/(1000000 / 1000421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11437 : Bounds (420911 / 1000000000) (26307 / 62500000) (Real.log (1000421 / 1000000)) := by
  have h := reflection_log_11437_neg
  have he : Real.log (1000421 / 1000000) = -Real.log (1000000 / 1000421) := by
    rw [show ((1000421 / 1000000) : ℝ) = ((1000000 / 1000421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11438_neg : (13159 / 31250000) ≤ -Real.log (999579 / 1000000) ∧
    -Real.log (999579 / 1000000) ≤ (421089 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1999579)) (n := 12)
    (lo := (13159 / 31250000)) (hi := (421089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999579) = 1/(999579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11438 : Bounds (-421089 / 1000000000) (-13159 / 31250000) (Real.log (999579 / 1000000)) := by
  have h := reflection_log_11438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11439_neg : (12266597 / 62500000) ≤ -Real.log (20000 / 24337) ∧
    -Real.log (20000 / 24337) ≤ (196265553 / 1000000000) := by
  have h := checkLog_sound (w := (4337 / 44337)) (n := 12)
    (lo := (12266597 / 62500000)) (hi := (196265553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24337 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24337 / 20000) = 1/(20000 / 24337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11439 : Bounds (12266597 / 62500000) (196265553 / 1000000000) (Real.log (24337 / 20000)) := by
  have h := reflection_log_11439_neg
  have he : Real.log (24337 / 20000) = -Real.log (20000 / 24337) := by
    rw [show ((24337 / 20000) : ℝ) = ((20000 / 24337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11440_neg : (24443103 / 100000000) ≤ -Real.log (15663 / 20000) ∧
    -Real.log (15663 / 20000) ≤ (244431031 / 1000000000) := by
  have h := checkLog_sound (w := (4337 / 35663)) (n := 12)
    (lo := (24443103 / 100000000)) (hi := (244431031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15663) = 1/(15663 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11440 : Bounds (-244431031 / 1000000000) (-24443103 / 100000000) (Real.log (15663 / 20000)) := by
  have h := reflection_log_11440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11441_neg : (98526671 / 500000000) ≤ -Real.log (1000000 / 1217809) ∧
    -Real.log (1000000 / 1217809) ≤ (197053343 / 1000000000) := by
  have h := checkLog_sound (w := (217809 / 2217809)) (n := 12)
    (lo := (98526671 / 500000000)) (hi := (197053343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217809 / 1000000) = 1/(1000000 / 1217809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11441 : Bounds (98526671 / 500000000) (197053343 / 1000000000) (Real.log (1217809 / 1000000)) := by
  have h := reflection_log_11441_neg
  have he : Real.log (1217809 / 1000000) = -Real.log (1000000 / 1217809) := by
    rw [show ((1217809 / 1000000) : ℝ) = ((1000000 / 1217809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11442_neg : (122828161 / 500000000) ≤ -Real.log (782191 / 1000000) ∧
    -Real.log (782191 / 1000000) ≤ (245656323 / 1000000000) := by
  have h := checkLog_sound (w := (217809 / 1782191)) (n := 12)
    (lo := (122828161 / 500000000)) (hi := (245656323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782191) = 1/(782191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11442 : Bounds (-245656323 / 1000000000) (-122828161 / 500000000) (Real.log (782191 / 1000000)) := by
  have h := reflection_log_11442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11443_neg : (2430149 / 50000000) ≤ -Real.log (952559239519 / 1000000000000) ∧
    -Real.log (952559239519 / 1000000000000) ≤ (48602981 / 1000000000) := by
  have h := checkLog_sound (w := (47440760481 / 1952559239519)) (n := 12)
    (lo := (2430149 / 50000000)) (hi := (48602981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 952559239519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 952559239519) = 1/(952559239519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11443 : Bounds (-48602981 / 1000000000) (-2430149 / 50000000) (Real.log (952559239519 / 1000000000000)) := by
  have h := reflection_log_11443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11444_neg : (48165477 / 1000000000) ≤ -Real.log (381190431 / 400000000) ∧
    -Real.log (381190431 / 400000000) ≤ (24082739 / 500000000) := by
  have h := checkLog_sound (w := (18809569 / 781190431)) (n := 12)
    (lo := (48165477 / 1000000000)) (hi := (24082739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 381190431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 381190431) = 1/(381190431 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11444 : Bounds (-24082739 / 500000000) (-48165477 / 1000000000) (Real.log (381190431 / 400000000)) := by
  have h := reflection_log_11444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11445_neg : (220348291 / 500000000) ≤ -Real.log (500000000000 / 776894592351) ∧
    -Real.log (500000000000 / 776894592351) ≤ (440696583 / 1000000000) := by
  have h := checkLog_sound (w := (276894592351 / 1276894592351)) (n := 12)
    (lo := (220348291 / 500000000)) (hi := (440696583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776894592351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776894592351 / 500000000000) = 1/(500000000000 / 776894592351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11445 : Bounds (220348291 / 500000000) (440696583 / 1000000000) (Real.log (776894592351 / 500000000000)) := by
  have h := reflection_log_11445_neg
  have he : Real.log (776894592351 / 500000000000) = -Real.log (500000000000 / 776894592351) := by
    rw [show ((776894592351 / 500000000000) : ℝ) = ((500000000000 / 776894592351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11446_neg : (88541933 / 200000000) ≤ -Real.log (100000000000 / 155692024071) ∧
    -Real.log (100000000000 / 155692024071) ≤ (221354833 / 500000000) := by
  have h := checkLog_sound (w := (55692024071 / 255692024071)) (n := 12)
    (lo := (88541933 / 200000000)) (hi := (221354833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155692024071 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155692024071 / 100000000000) = 1/(100000000000 / 155692024071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11446 : Bounds (88541933 / 200000000) (221354833 / 500000000) (Real.log (155692024071 / 100000000000)) := by
  have h := reflection_log_11446_neg
  have he : Real.log (155692024071 / 100000000000) = -Real.log (100000000000 / 155692024071) := by
    rw [show ((155692024071 / 100000000000) : ℝ) = ((100000000000 / 155692024071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11447_neg : (447692023 / 500000000) ≤ -Real.log (250000000000 / 612068965517) ∧
    -Real.log (250000000000 / 612068965517) ≤ (55961503 / 62500000) := by
  have h := checkLog_sound (w := (112068965517 / 1112068965517)) (n := 12)
    (lo := (101118433 / 500000000)) (hi := (202236867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612068965517 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(612068965517 / 500000000000) = 1/(250000000000 / 612068965517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11447 : Bounds (447692023 / 500000000) (55961503 / 62500000) (Real.log (612068965517 / 250000000000)) := by
  have h := reflection_log_11447_neg
  have he : Real.log (612068965517 / 250000000000) = -Real.log (250000000000 / 612068965517) := by
    rw [show ((612068965517 / 250000000000) : ℝ) = ((250000000000 / 612068965517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11448_neg : (897813649 / 1000000000) ≤ -Real.log (250000000000 / 613557858377) ∧
    -Real.log (250000000000 / 613557858377) ≤ (897813651 / 1000000000) := by
  have h := checkLog_sound (w := (113557858377 / 1113557858377)) (n := 12)
    (lo := (204666469 / 1000000000)) (hi := (20466647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613557858377 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(613557858377 / 500000000000) = 1/(250000000000 / 613557858377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11448 : Bounds (897813649 / 1000000000) (897813651 / 1000000000) (Real.log (613557858377 / 250000000000)) := by
  have h := reflection_log_11448_neg
  have he : Real.log (613557858377 / 250000000000) = -Real.log (250000000000 / 613557858377) := by
    rw [show ((613557858377 / 250000000000) : ℝ) = ((250000000000 / 613557858377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11449_neg : (352064331 / 1000000000) ≤ -Real.log (500 / 711) ∧
    -Real.log (500 / 711) ≤ (88016083 / 250000000) := by
  have h := checkLog_sound (w := (211 / 1211)) (n := 12)
    (lo := (352064331 / 1000000000)) (hi := (88016083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711 / 500) = 1/(500 / 711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11449 : Bounds (352064331 / 1000000000) (88016083 / 250000000) (Real.log (711 / 500)) := by
  have h := reflection_log_11449_neg
  have he : Real.log (711 / 500) = -Real.log (500 / 711) := by
    rw [show ((711 / 500) : ℝ) = ((500 / 711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11450_neg : (54818141 / 100000000) ≤ -Real.log (289 / 500) ∧
    -Real.log (289 / 500) ≤ (548181411 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 789)) (n := 12)
    (lo := (54818141 / 100000000)) (hi := (548181411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 289) = 1/(289 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11450 : Bounds (-548181411 / 1000000000) (-54818141 / 100000000) (Real.log (289 / 500)) := by
  have h := reflection_log_11450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11451_neg : (42191 / 100000000) ≤ -Real.log (500000 / 500211) ∧
    -Real.log (500000 / 500211) ≤ (421911 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1000211)) (n := 12)
    (lo := (42191 / 100000000)) (hi := (421911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500211 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500211 / 500000) = 1/(500000 / 500211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11451 : Bounds (42191 / 100000000) (421911 / 1000000000) (Real.log (500211 / 500000)) := by
  have h := reflection_log_11451_neg
  have he : Real.log (500211 / 500000) = -Real.log (500000 / 500211) := by
    rw [show ((500211 / 500000) : ℝ) = ((500000 / 500211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11452_neg : (422089 / 1000000000) ≤ -Real.log (499789 / 500000) ∧
    -Real.log (499789 / 500000) ≤ (42209 / 100000000) := by
  have h := checkLog_sound (w := (211 / 999789)) (n := 12)
    (lo := (422089 / 1000000000)) (hi := (42209 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499789) = 1/(499789 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11452 : Bounds (-42209 / 100000000) (-422089 / 1000000000) (Real.log (499789 / 500000)) := by
  have h := reflection_log_11452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11453_neg : (196719079 / 1000000000) ≤ -Real.log (500000 / 608701) ∧
    -Real.log (500000 / 608701) ≤ (4917977 / 25000000) := by
  have h := checkLog_sound (w := (108701 / 1108701)) (n := 12)
    (lo := (196719079 / 1000000000)) (hi := (4917977 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608701 / 500000) = 1/(500000 / 608701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11453 : Bounds (196719079 / 1000000000) (4917977 / 25000000) (Real.log (608701 / 500000)) := by
  have h := reflection_log_11453_neg
  have he : Real.log (608701 / 500000) = -Real.log (500000 / 608701) := by
    rw [show ((608701 / 500000) : ℝ) = ((500000 / 608701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11454_neg : (61284031 / 250000000) ≤ -Real.log (391299 / 500000) ∧
    -Real.log (391299 / 500000) ≤ (1961089 / 8000000) := by
  have h := checkLog_sound (w := (108701 / 891299)) (n := 12)
    (lo := (61284031 / 250000000)) (hi := (1961089 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391299) = 1/(391299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11454 : Bounds (-1961089 / 8000000) (-61284031 / 250000000) (Real.log (391299 / 500000)) := by
  have h := reflection_log_11454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11455_neg : (98754077 / 500000000) ≤ -Real.log (1000000 / 1218363) ∧
    -Real.log (1000000 / 1218363) ≤ (39501631 / 200000000) := by
  have h := checkLog_sound (w := (218363 / 2218363)) (n := 12)
    (lo := (98754077 / 500000000)) (hi := (39501631 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218363 / 1000000) = 1/(1000000 / 1218363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11455 : Bounds (98754077 / 500000000) (39501631 / 200000000) (Real.log (1218363 / 1000000)) := by
  have h := reflection_log_11455_neg
  have he : Real.log (1218363 / 1000000) = -Real.log (1000000 / 1218363) := by
    rw [show ((1218363 / 1000000) : ℝ) = ((1000000 / 1218363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0179 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11456_neg : (6159121 / 25000000) ≤ -Real.log (781637 / 1000000) ∧
    -Real.log (781637 / 1000000) ≤ (246364841 / 1000000000) := by
  have h := checkLog_sound (w := (218363 / 1781637)) (n := 12)
    (lo := (6159121 / 25000000)) (hi := (246364841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781637) = 1/(781637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11456 : Bounds (-246364841 / 1000000000) (-6159121 / 25000000) (Real.log (781637 / 1000000)) := by
  have h := reflection_log_11456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11457_neg : (24428343 / 500000000) ≤ -Real.log (952317600231 / 1000000000000) ∧
    -Real.log (952317600231 / 1000000000000) ≤ (48856687 / 1000000000) := by
  have h := checkLog_sound (w := (47682399769 / 1952317600231)) (n := 12)
    (lo := (24428343 / 500000000)) (hi := (48856687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 952317600231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 952317600231) = 1/(952317600231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11457 : Bounds (-48856687 / 1000000000) (-24428343 / 500000000) (Real.log (952317600231 / 1000000000000)) := by
  have h := reflection_log_11457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11458_neg : (12104261 / 250000000) ≤ -Real.log (238184092599 / 250000000000) ∧
    -Real.log (238184092599 / 250000000000) ≤ (9683409 / 200000000) := by
  have h := checkLog_sound (w := (11815907401 / 488184092599)) (n := 12)
    (lo := (12104261 / 250000000)) (hi := (9683409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238184092599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238184092599) = 1/(238184092599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11458 : Bounds (-9683409 / 200000000) (-12104261 / 250000000) (Real.log (238184092599 / 250000000000)) := by
  have h := reflection_log_11458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11459_neg : (110463801 / 250000000) ≤ -Real.log (500000000000 / 777795240979) ∧
    -Real.log (500000000000 / 777795240979) ≤ (88371041 / 200000000) := by
  have h := checkLog_sound (w := (277795240979 / 1277795240979)) (n := 12)
    (lo := (110463801 / 250000000)) (hi := (88371041 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777795240979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777795240979 / 500000000000) = 1/(500000000000 / 777795240979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11459 : Bounds (110463801 / 250000000) (88371041 / 200000000) (Real.log (777795240979 / 500000000000)) := by
  have h := reflection_log_11459_neg
  have he : Real.log (777795240979 / 500000000000) = -Real.log (500000000000 / 777795240979) := by
    rw [show ((777795240979 / 500000000000) : ℝ) = ((500000000000 / 777795240979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11460_neg : (88774599 / 200000000) ≤ -Real.log (500000000000 / 779366253133) ∧
    -Real.log (500000000000 / 779366253133) ≤ (110968249 / 250000000) := by
  have h := checkLog_sound (w := (279366253133 / 1279366253133)) (n := 12)
    (lo := (88774599 / 200000000)) (hi := (110968249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779366253133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779366253133 / 500000000000) = 1/(500000000000 / 779366253133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11460 : Bounds (88774599 / 200000000) (110968249 / 250000000) (Real.log (779366253133 / 500000000000)) := by
  have h := reflection_log_11460_neg
  have he : Real.log (779366253133 / 500000000000) = -Real.log (500000000000 / 779366253133) := by
    rw [show ((779366253133 / 500000000000) : ℝ) = ((500000000000 / 779366253133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11461_neg : (897813649 / 1000000000) ≤ -Real.log (500000000000 / 1227115716753) ∧
    -Real.log (500000000000 / 1227115716753) ≤ (897813651 / 1000000000) := by
  have h := checkLog_sound (w := (227115716753 / 2227115716753)) (n := 12)
    (lo := (204666469 / 1000000000)) (hi := (20466647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227115716753 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1227115716753 / 1000000000000) = 1/(500000000000 / 1227115716753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11461 : Bounds (897813649 / 1000000000) (897813651 / 1000000000) (Real.log (1227115716753 / 500000000000)) := by
  have h := reflection_log_11461_neg
  have he : Real.log (1227115716753 / 500000000000) = -Real.log (500000000000 / 1227115716753) := by
    rw [show ((1227115716753 / 500000000000) : ℝ) = ((500000000000 / 1227115716753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11462_neg : (900245741 / 1000000000) ≤ -Real.log (500000000000 / 1230103806229) ∧
    -Real.log (500000000000 / 1230103806229) ≤ (900245743 / 1000000000) := by
  have h := checkLog_sound (w := (230103806229 / 2230103806229)) (n := 12)
    (lo := (207098561 / 1000000000)) (hi := (103549281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230103806229 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1230103806229 / 1000000000000) = 1/(500000000000 / 1230103806229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11462 : Bounds (900245741 / 1000000000) (900245743 / 1000000000) (Real.log (1230103806229 / 500000000000)) := by
  have h := reflection_log_11462_neg
  have he : Real.log (1230103806229 / 500000000000) = -Real.log (500000000000 / 1230103806229) := by
    rw [show ((1230103806229 / 500000000000) : ℝ) = ((500000000000 / 1230103806229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11463_neg : (352767319 / 1000000000) ≤ -Real.log (1000 / 1423) ∧
    -Real.log (1000 / 1423) ≤ (8819183 / 25000000) := by
  have h := checkLog_sound (w := (423 / 2423)) (n := 12)
    (lo := (352767319 / 1000000000)) (hi := (8819183 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1423 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1423 / 1000) = 1/(1000 / 1423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11463 : Bounds (352767319 / 1000000000) (8819183 / 25000000) (Real.log (1423 / 1000)) := by
  have h := reflection_log_11463_neg
  have he : Real.log (1423 / 1000) = -Real.log (1000 / 1423) := by
    rw [show ((1423 / 1000) : ℝ) = ((1000 / 1423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11464_neg : (137478253 / 250000000) ≤ -Real.log (577 / 1000) ∧
    -Real.log (577 / 1000) ≤ (549913013 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 1577)) (n := 12)
    (lo := (137478253 / 250000000)) (hi := (549913013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 577) = 1/(577 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11464 : Bounds (-549913013 / 1000000000) (-137478253 / 250000000) (Real.log (577 / 1000)) := by
  have h := reflection_log_11464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11465_neg : (42291 / 100000000) ≤ -Real.log (1000000 / 1000423) ∧
    -Real.log (1000000 / 1000423) ≤ (422911 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 2000423)) (n := 12)
    (lo := (42291 / 100000000)) (hi := (422911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000423 / 1000000) = 1/(1000000 / 1000423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11465 : Bounds (42291 / 100000000) (422911 / 1000000000) (Real.log (1000423 / 1000000)) := by
  have h := reflection_log_11465_neg
  have he : Real.log (1000423 / 1000000) = -Real.log (1000000 / 1000423) := by
    rw [show ((1000423 / 1000000) : ℝ) = ((1000000 / 1000423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11466_neg : (423089 / 1000000000) ≤ -Real.log (999577 / 1000000) ∧
    -Real.log (999577 / 1000000) ≤ (42309 / 100000000) := by
  have h := checkLog_sound (w := (423 / 1999577)) (n := 12)
    (lo := (423089 / 1000000000)) (hi := (42309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999577) = 1/(999577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11466 : Bounds (-42309 / 100000000) (-423089 / 1000000000) (Real.log (999577 / 1000000)) := by
  have h := reflection_log_11466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11467_neg : (98586611 / 500000000) ≤ -Real.log (200000 / 243591) ∧
    -Real.log (200000 / 243591) ≤ (197173223 / 1000000000) := by
  have h := checkLog_sound (w := (43591 / 443591)) (n := 12)
    (lo := (98586611 / 500000000)) (hi := (197173223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243591 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243591 / 200000) = 1/(200000 / 243591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11467 : Bounds (98586611 / 500000000) (197173223 / 1000000000) (Real.log (243591 / 200000)) := by
  have h := reflection_log_11467_neg
  have he : Real.log (243591 / 200000) = -Real.log (200000 / 243591) := by
    rw [show ((243591 / 200000) : ℝ) = ((200000 / 243591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11468_neg : (49168599 / 200000000) ≤ -Real.log (156409 / 200000) ∧
    -Real.log (156409 / 200000) ≤ (61460749 / 250000000) := by
  have h := checkLog_sound (w := (43591 / 356409)) (n := 12)
    (lo := (49168599 / 200000000)) (hi := (61460749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 156409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 156409) = 1/(156409 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11468 : Bounds (-61460749 / 250000000) (-49168599 / 200000000) (Real.log (156409 / 200000)) := by
  have h := reflection_log_11468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11469_neg : (197961939 / 1000000000) ≤ -Real.log (250000 / 304729) ∧
    -Real.log (250000 / 304729) ≤ (9898097 / 50000000) := by
  have h := checkLog_sound (w := (54729 / 554729)) (n := 12)
    (lo := (197961939 / 1000000000)) (hi := (9898097 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304729 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304729 / 250000) = 1/(250000 / 304729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11469 : Bounds (197961939 / 1000000000) (9898097 / 50000000) (Real.log (304729 / 250000)) := by
  have h := reflection_log_11469_neg
  have he : Real.log (304729 / 250000) = -Real.log (250000 / 304729) := by
    rw [show ((304729 / 250000) : ℝ) = ((250000 / 304729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11470_neg : (12353629 / 50000000) ≤ -Real.log (195271 / 250000) ∧
    -Real.log (195271 / 250000) ≤ (247072581 / 1000000000) := by
  have h := checkLog_sound (w := (54729 / 445271)) (n := 12)
    (lo := (12353629 / 50000000)) (hi := (247072581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195271) = 1/(195271 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11470 : Bounds (-247072581 / 1000000000) (-12353629 / 50000000) (Real.log (195271 / 250000)) := by
  have h := reflection_log_11470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11471_neg : (49110641 / 1000000000) ≤ -Real.log (59504736559 / 62500000000) ∧
    -Real.log (59504736559 / 62500000000) ≤ (24555321 / 500000000) := by
  have h := checkLog_sound (w := (2995263441 / 122004736559)) (n := 12)
    (lo := (49110641 / 1000000000)) (hi := (24555321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59504736559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59504736559) = 1/(59504736559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11471 : Bounds (-24555321 / 500000000) (-49110641 / 1000000000) (Real.log (59504736559 / 62500000000)) := by
  have h := reflection_log_11471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11472_neg : (12167443 / 250000000) ≤ -Real.log (38099824719 / 40000000000) ∧
    -Real.log (38099824719 / 40000000000) ≤ (48669773 / 1000000000) := by
  have h := checkLog_sound (w := (1900175281 / 78099824719)) (n := 12)
    (lo := (12167443 / 250000000)) (hi := (48669773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38099824719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38099824719) = 1/(38099824719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11472 : Bounds (-48669773 / 1000000000) (-12167443 / 250000000) (Real.log (38099824719 / 40000000000)) := by
  have h := reflection_log_11472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11473_neg : (221508109 / 500000000) ≤ -Real.log (100000000000 / 155739759221) ∧
    -Real.log (100000000000 / 155739759221) ≤ (443016219 / 1000000000) := by
  have h := checkLog_sound (w := (55739759221 / 255739759221)) (n := 12)
    (lo := (221508109 / 500000000)) (hi := (443016219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155739759221 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155739759221 / 100000000000) = 1/(100000000000 / 155739759221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11473 : Bounds (221508109 / 500000000) (443016219 / 1000000000) (Real.log (155739759221 / 100000000000)) := by
  have h := reflection_log_11473_neg
  have he : Real.log (155739759221 / 100000000000) = -Real.log (100000000000 / 155739759221) := by
    rw [show ((155739759221 / 100000000000) : ℝ) = ((100000000000 / 155739759221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11474_neg : (445034519 / 1000000000) ≤ -Real.log (250000000000 / 390136016101) ∧
    -Real.log (250000000000 / 390136016101) ≤ (11125863 / 25000000) := by
  have h := checkLog_sound (w := (140136016101 / 640136016101)) (n := 12)
    (lo := (445034519 / 1000000000)) (hi := (11125863 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390136016101 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390136016101 / 250000000000) = 1/(250000000000 / 390136016101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11474 : Bounds (445034519 / 1000000000) (11125863 / 25000000) (Real.log (390136016101 / 250000000000)) := by
  have h := reflection_log_11474_neg
  have he : Real.log (390136016101 / 250000000000) = -Real.log (250000000000 / 390136016101) := by
    rw [show ((390136016101 / 250000000000) : ℝ) = ((250000000000 / 390136016101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11475_neg : (900245741 / 1000000000) ≤ -Real.log (125000000000 / 307525951557) ∧
    -Real.log (125000000000 / 307525951557) ≤ (900245743 / 1000000000) := by
  have h := checkLog_sound (w := (57525951557 / 557525951557)) (n := 12)
    (lo := (207098561 / 1000000000)) (hi := (103549281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307525951557 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(307525951557 / 250000000000) = 1/(125000000000 / 307525951557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11475 : Bounds (900245741 / 1000000000) (900245743 / 1000000000) (Real.log (307525951557 / 125000000000)) := by
  have h := reflection_log_11475_neg
  have he : Real.log (307525951557 / 125000000000) = -Real.log (125000000000 / 307525951557) := by
    rw [show ((307525951557 / 125000000000) : ℝ) = ((125000000000 / 307525951557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11476_neg : (902680331 / 1000000000) ≤ -Real.log (500000000000 / 1233102253033) ∧
    -Real.log (500000000000 / 1233102253033) ≤ (902680333 / 1000000000) := by
  have h := checkLog_sound (w := (233102253033 / 2233102253033)) (n := 12)
    (lo := (209533151 / 1000000000)) (hi := (6547911 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233102253033 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1233102253033 / 1000000000000) = 1/(500000000000 / 1233102253033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11476 : Bounds (902680331 / 1000000000) (902680333 / 1000000000) (Real.log (1233102253033 / 500000000000)) := by
  have h := reflection_log_11476_neg
  have he : Real.log (1233102253033 / 500000000000) = -Real.log (500000000000 / 1233102253033) := by
    rw [show ((1233102253033 / 500000000000) : ℝ) = ((500000000000 / 1233102253033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11477_neg : (88367453 / 250000000) ≤ -Real.log (125 / 178) ∧
    -Real.log (125 / 178) ≤ (353469813 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 303)) (n := 12)
    (lo := (88367453 / 250000000)) (hi := (353469813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178 / 125) = 1/(125 / 178) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11477 : Bounds (88367453 / 250000000) (353469813 / 1000000000) (Real.log (178 / 125)) := by
  have h := reflection_log_11477_neg
  have he : Real.log (178 / 125) = -Real.log (125 / 178) := by
    rw [show ((178 / 125) : ℝ) = ((125 / 178) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11478_neg : (275823809 / 500000000) ≤ -Real.log (72 / 125) ∧
    -Real.log (72 / 125) ≤ (551647619 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 197)) (n := 12)
    (lo := (275823809 / 500000000)) (hi := (551647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 72) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 72) = 1/(72 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11478 : Bounds (-551647619 / 1000000000) (-275823809 / 500000000) (Real.log (72 / 125)) := by
  have h := reflection_log_11478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11479_neg : (42391 / 100000000) ≤ -Real.log (125000 / 125053) ∧
    -Real.log (125000 / 125053) ≤ (423911 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 250053)) (n := 12)
    (lo := (42391 / 100000000)) (hi := (423911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125053 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125053 / 125000) = 1/(125000 / 125053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11479 : Bounds (42391 / 100000000) (423911 / 1000000000) (Real.log (125053 / 125000)) := by
  have h := reflection_log_11479_neg
  have he : Real.log (125053 / 125000) = -Real.log (125000 / 125053) := by
    rw [show ((125053 / 125000) : ℝ) = ((125000 / 125053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11480_neg : (424089 / 1000000000) ≤ -Real.log (124947 / 125000) ∧
    -Real.log (124947 / 125000) ≤ (42409 / 100000000) := by
  have h := checkLog_sound (w := (53 / 249947)) (n := 12)
    (lo := (424089 / 1000000000)) (hi := (42409 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124947) = 1/(124947 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11480 : Bounds (-42409 / 100000000) (-424089 / 1000000000) (Real.log (124947 / 125000)) := by
  have h := reflection_log_11480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11481_neg : (98813169 / 500000000) ≤ -Real.log (1000000 / 1218507) ∧
    -Real.log (1000000 / 1218507) ≤ (197626339 / 1000000000) := by
  have h := checkLog_sound (w := (218507 / 2218507)) (n := 12)
    (lo := (98813169 / 500000000)) (hi := (197626339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218507 / 1000000) = 1/(1000000 / 1218507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11481 : Bounds (98813169 / 500000000) (197626339 / 1000000000) (Real.log (1218507 / 1000000)) := by
  have h := reflection_log_11481_neg
  have he : Real.log (1218507 / 1000000) = -Real.log (1000000 / 1218507) := by
    rw [show ((1218507 / 1000000) : ℝ) = ((1000000 / 1218507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11482_neg : (123274543 / 500000000) ≤ -Real.log (781493 / 1000000) ∧
    -Real.log (781493 / 1000000) ≤ (246549087 / 1000000000) := by
  have h := checkLog_sound (w := (218507 / 1781493)) (n := 12)
    (lo := (123274543 / 500000000)) (hi := (246549087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781493) = 1/(781493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11482 : Bounds (-246549087 / 1000000000) (-123274543 / 500000000) (Real.log (781493 / 1000000)) := by
  have h := reflection_log_11482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11483_neg : (99208169 / 500000000) ≤ -Real.log (100000 / 121947) ∧
    -Real.log (100000 / 121947) ≤ (198416339 / 1000000000) := by
  have h := checkLog_sound (w := (21947 / 221947)) (n := 12)
    (lo := (99208169 / 500000000)) (hi := (198416339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121947 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121947 / 100000) = 1/(100000 / 121947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11483 : Bounds (99208169 / 500000000) (198416339 / 1000000000) (Real.log (121947 / 100000)) := by
  have h := reflection_log_11483_neg
  have he : Real.log (121947 / 100000) = -Real.log (100000 / 121947) := by
    rw [show ((121947 / 100000) : ℝ) = ((100000 / 121947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11484_neg : (123891051 / 500000000) ≤ -Real.log (78053 / 100000) ∧
    -Real.log (78053 / 100000) ≤ (247782103 / 1000000000) := by
  have h := checkLog_sound (w := (21947 / 178053)) (n := 12)
    (lo := (123891051 / 500000000)) (hi := (247782103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78053) = 1/(78053 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11484 : Bounds (-247782103 / 1000000000) (-123891051 / 500000000) (Real.log (78053 / 100000)) := by
  have h := reflection_log_11484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11485_neg : (12341441 / 250000000) ≤ -Real.log (9518329191 / 10000000000) ∧
    -Real.log (9518329191 / 10000000000) ≤ (9873153 / 200000000) := by
  have h := checkLog_sound (w := (481670809 / 19518329191)) (n := 12)
    (lo := (12341441 / 250000000)) (hi := (9873153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9518329191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9518329191) = 1/(9518329191 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11485 : Bounds (-9873153 / 200000000) (-12341441 / 250000000) (Real.log (9518329191 / 10000000000)) := by
  have h := reflection_log_11485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11486_neg : (48922747 / 1000000000) ≤ -Real.log (952254690951 / 1000000000000) ∧
    -Real.log (952254690951 / 1000000000000) ≤ (12230687 / 250000000) := by
  have h := checkLog_sound (w := (47745309049 / 1952254690951)) (n := 12)
    (lo := (48922747 / 1000000000)) (hi := (12230687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 952254690951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 952254690951) = 1/(952254690951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11486 : Bounds (-12230687 / 250000000) (-48922747 / 1000000000) (Real.log (952254690951 / 1000000000000)) := by
  have h := reflection_log_11486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11487_neg : (17767017 / 40000000) ≤ -Real.log (125000000000 / 194900498149) ∧
    -Real.log (125000000000 / 194900498149) ≤ (222087713 / 500000000) := by
  have h := checkLog_sound (w := (69900498149 / 319900498149)) (n := 12)
    (lo := (17767017 / 40000000)) (hi := (222087713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194900498149 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194900498149 / 125000000000) = 1/(125000000000 / 194900498149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11487 : Bounds (17767017 / 40000000) (222087713 / 500000000) (Real.log (194900498149 / 125000000000)) := by
  have h := reflection_log_11487_neg
  have he : Real.log (194900498149 / 125000000000) = -Real.log (125000000000 / 194900498149) := by
    rw [show ((194900498149 / 125000000000) : ℝ) = ((125000000000 / 194900498149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11488_neg : (11154961 / 25000000) ≤ -Real.log (500000000000 / 781180736167) ∧
    -Real.log (500000000000 / 781180736167) ≤ (446198441 / 1000000000) := by
  have h := checkLog_sound (w := (281180736167 / 1281180736167)) (n := 12)
    (lo := (11154961 / 25000000)) (hi := (446198441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781180736167 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781180736167 / 500000000000) = 1/(500000000000 / 781180736167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11488 : Bounds (11154961 / 25000000) (446198441 / 1000000000) (Real.log (781180736167 / 500000000000)) := by
  have h := reflection_log_11488_neg
  have he : Real.log (781180736167 / 500000000000) = -Real.log (500000000000 / 781180736167) := by
    rw [show ((781180736167 / 500000000000) : ℝ) = ((500000000000 / 781180736167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11489_neg : (902680331 / 1000000000) ≤ -Real.log (62500000000 / 154137781629) ∧
    -Real.log (62500000000 / 154137781629) ≤ (902680333 / 1000000000) := by
  have h := checkLog_sound (w := (29137781629 / 279137781629)) (n := 12)
    (lo := (209533151 / 1000000000)) (hi := (6547911 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154137781629 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(154137781629 / 125000000000) = 1/(62500000000 / 154137781629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11489 : Bounds (902680331 / 1000000000) (902680333 / 1000000000) (Real.log (154137781629 / 62500000000)) := by
  have h := reflection_log_11489_neg
  have he : Real.log (154137781629 / 62500000000) = -Real.log (62500000000 / 154137781629) := by
    rw [show ((154137781629 / 62500000000) : ℝ) = ((62500000000 / 154137781629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11490_neg : (90511743 / 100000000) ≤ -Real.log (62500000000 / 154513888889) ∧
    -Real.log (62500000000 / 154513888889) ≤ (113139679 / 125000000) := by
  have h := checkLog_sound (w := (29513888889 / 279513888889)) (n := 12)
    (lo := (847881 / 4000000)) (hi := (211970251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154513888889 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(154513888889 / 125000000000) = 1/(62500000000 / 154513888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11490 : Bounds (90511743 / 100000000) (113139679 / 125000000) (Real.log (154513888889 / 62500000000)) := by
  have h := reflection_log_11490_neg
  have he : Real.log (154513888889 / 62500000000) = -Real.log (62500000000 / 154513888889) := by
    rw [show ((154513888889 / 62500000000) : ℝ) = ((62500000000 / 154513888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11491_neg : (354171813 / 1000000000) ≤ -Real.log (40 / 57) ∧
    -Real.log (40 / 57) ≤ (177085907 / 500000000) := by
  have h := checkLog_sound (w := (17 / 97)) (n := 12)
    (lo := (354171813 / 1000000000)) (hi := (177085907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57 / 40) = 1/(40 / 57) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11491 : Bounds (354171813 / 1000000000) (177085907 / 500000000) (Real.log (57 / 40)) := by
  have h := reflection_log_11491_neg
  have he : Real.log (57 / 40) = -Real.log (40 / 57) := by
    rw [show ((57 / 40) : ℝ) = ((40 / 57) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11492_neg : (276692619 / 500000000) ≤ -Real.log (23 / 40) ∧
    -Real.log (23 / 40) ≤ (553385239 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 63)) (n := 12)
    (lo := (276692619 / 500000000)) (hi := (553385239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 23) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 23) = 1/(23 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11492 : Bounds (-553385239 / 1000000000) (-276692619 / 500000000) (Real.log (23 / 40)) := by
  have h := reflection_log_11492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11493_neg : (424909 / 1000000000) ≤ -Real.log (40000 / 40017) ∧
    -Real.log (40000 / 40017) ≤ (42491 / 100000000) := by
  have h := checkLog_sound (w := (17 / 80017)) (n := 12)
    (lo := (424909 / 1000000000)) (hi := (42491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40017 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40017 / 40000) = 1/(40000 / 40017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11493 : Bounds (424909 / 1000000000) (42491 / 100000000) (Real.log (40017 / 40000)) := by
  have h := reflection_log_11493_neg
  have he : Real.log (40017 / 40000) = -Real.log (40000 / 40017) := by
    rw [show ((40017 / 40000) : ℝ) = ((40000 / 40017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11494_neg : (42509 / 100000000) ≤ -Real.log (39983 / 40000) ∧
    -Real.log (39983 / 40000) ≤ (425091 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 79983)) (n := 12)
    (lo := (42509 / 100000000)) (hi := (425091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39983) = 1/(39983 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11494 : Bounds (-425091 / 1000000000) (-42509 / 100000000) (Real.log (39983 / 40000)) := by
  have h := reflection_log_11494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11495_neg : (198080069 / 1000000000) ≤ -Real.log (50000 / 60953) ∧
    -Real.log (50000 / 60953) ≤ (19808007 / 100000000) := by
  have h := checkLog_sound (w := (10953 / 110953)) (n := 12)
    (lo := (198080069 / 1000000000)) (hi := (19808007 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60953 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60953 / 50000) = 1/(50000 / 60953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11495 : Bounds (198080069 / 1000000000) (19808007 / 100000000) (Real.log (60953 / 50000)) := by
  have h := reflection_log_11495_neg
  have he : Real.log (60953 / 50000) = -Real.log (50000 / 60953) := by
    rw [show ((60953 / 50000) : ℝ) = ((50000 / 60953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11496_neg : (61814239 / 250000000) ≤ -Real.log (39047 / 50000) ∧
    -Real.log (39047 / 50000) ≤ (247256957 / 1000000000) := by
  have h := checkLog_sound (w := (10953 / 89047)) (n := 12)
    (lo := (61814239 / 250000000)) (hi := (247256957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39047) = 1/(39047 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11496 : Bounds (-247256957 / 1000000000) (-61814239 / 250000000) (Real.log (39047 / 50000)) := by
  have h := reflection_log_11496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11497_neg : (19887053 / 100000000) ≤ -Real.log (125000 / 152503) ∧
    -Real.log (125000 / 152503) ≤ (198870531 / 1000000000) := by
  have h := checkLog_sound (w := (27503 / 277503)) (n := 12)
    (lo := (19887053 / 100000000)) (hi := (198870531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152503 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152503 / 125000) = 1/(125000 / 152503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11497 : Bounds (19887053 / 100000000) (198870531 / 1000000000) (Real.log (152503 / 125000)) := by
  have h := reflection_log_11497_neg
  have he : Real.log (152503 / 125000) = -Real.log (125000 / 152503) := by
    rw [show ((152503 / 125000) : ℝ) = ((125000 / 152503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11498_neg : (248492129 / 1000000000) ≤ -Real.log (97497 / 125000) ∧
    -Real.log (97497 / 125000) ≤ (24849213 / 100000000) := by
  have h := checkLog_sound (w := (27503 / 222497)) (n := 12)
    (lo := (248492129 / 1000000000)) (hi := (24849213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97497) = 1/(97497 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11498 : Bounds (-24849213 / 100000000) (-248492129 / 1000000000) (Real.log (97497 / 125000)) := by
  have h := reflection_log_11498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11499_neg : (24810799 / 500000000) ≤ -Real.log (14868584991 / 15625000000) ∧
    -Real.log (14868584991 / 15625000000) ≤ (49621599 / 1000000000) := by
  have h := checkLog_sound (w := (756415009 / 30493584991)) (n := 12)
    (lo := (24810799 / 500000000)) (hi := (49621599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14868584991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14868584991) = 1/(14868584991 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11499 : Bounds (-49621599 / 1000000000) (-24810799 / 500000000) (Real.log (14868584991 / 15625000000)) := by
  have h := reflection_log_11499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11500_neg : (24588443 / 500000000) ≤ -Real.log (2380031791 / 2500000000) ∧
    -Real.log (2380031791 / 2500000000) ≤ (49176887 / 1000000000) := by
  have h := checkLog_sound (w := (119968209 / 4880031791)) (n := 12)
    (lo := (24588443 / 500000000)) (hi := (49176887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2380031791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2380031791) = 1/(2380031791 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11500 : Bounds (-49176887 / 1000000000) (-24588443 / 500000000) (Real.log (2380031791 / 2500000000)) := by
  have h := reflection_log_11500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11501_neg : (222668513 / 500000000) ≤ -Real.log (31250000000 / 48781756601) ∧
    -Real.log (31250000000 / 48781756601) ≤ (445337027 / 1000000000) := by
  have h := checkLog_sound (w := (17531756601 / 80031756601)) (n := 12)
    (lo := (222668513 / 500000000)) (hi := (445337027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48781756601 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48781756601 / 31250000000) = 1/(31250000000 / 48781756601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11501 : Bounds (222668513 / 500000000) (445337027 / 1000000000) (Real.log (48781756601 / 31250000000)) := by
  have h := reflection_log_11501_neg
  have he : Real.log (48781756601 / 31250000000) = -Real.log (31250000000 / 48781756601) := by
    rw [show ((48781756601 / 31250000000) : ℝ) = ((31250000000 / 48781756601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11502_neg : (447362659 / 1000000000) ≤ -Real.log (500000000000 / 782090730997) ∧
    -Real.log (500000000000 / 782090730997) ≤ (22368133 / 50000000) := by
  have h := checkLog_sound (w := (282090730997 / 1282090730997)) (n := 12)
    (lo := (447362659 / 1000000000)) (hi := (22368133 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782090730997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782090730997 / 500000000000) = 1/(500000000000 / 782090730997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11502 : Bounds (447362659 / 1000000000) (22368133 / 50000000) (Real.log (782090730997 / 500000000000)) := by
  have h := reflection_log_11502_neg
  have he : Real.log (782090730997 / 500000000000) = -Real.log (500000000000 / 782090730997) := by
    rw [show ((782090730997 / 500000000000) : ℝ) = ((500000000000 / 782090730997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11503_neg : (90511743 / 100000000) ≤ -Real.log (500000000000 / 1236111111111) ∧
    -Real.log (500000000000 / 1236111111111) ≤ (113139679 / 125000000) := by
  have h := checkLog_sound (w := (236111111111 / 2236111111111)) (n := 12)
    (lo := (847881 / 4000000)) (hi := (211970251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236111111111 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1236111111111 / 1000000000000) = 1/(500000000000 / 1236111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11503 : Bounds (90511743 / 100000000) (113139679 / 125000000) (Real.log (1236111111111 / 500000000000)) := by
  have h := reflection_log_11503_neg
  have he : Real.log (1236111111111 / 500000000000) = -Real.log (500000000000 / 1236111111111) := by
    rw [show ((1236111111111 / 500000000000) : ℝ) = ((500000000000 / 1236111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11504_neg : (907557051 / 1000000000) ≤ -Real.log (500000000000 / 1239130434783) ∧
    -Real.log (500000000000 / 1239130434783) ≤ (907557053 / 1000000000) := by
  have h := checkLog_sound (w := (239130434783 / 2239130434783)) (n := 12)
    (lo := (214409871 / 1000000000)) (hi := (13400617 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239130434783 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1239130434783 / 1000000000000) = 1/(500000000000 / 1239130434783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11504 : Bounds (907557051 / 1000000000) (907557053 / 1000000000) (Real.log (1239130434783 / 500000000000)) := by
  have h := reflection_log_11504_neg
  have he : Real.log (1239130434783 / 500000000000) = -Real.log (500000000000 / 1239130434783) := by
    rw [show ((1239130434783 / 500000000000) : ℝ) = ((500000000000 / 1239130434783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11505_neg : (354873321 / 1000000000) ≤ -Real.log (500 / 713) ∧
    -Real.log (500 / 713) ≤ (177436661 / 500000000) := by
  have h := checkLog_sound (w := (213 / 1213)) (n := 12)
    (lo := (354873321 / 1000000000)) (hi := (177436661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713 / 500) = 1/(500 / 713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11505 : Bounds (354873321 / 1000000000) (177436661 / 500000000) (Real.log (713 / 500)) := by
  have h := reflection_log_11505_neg
  have he : Real.log (713 / 500) = -Real.log (500 / 713) := by
    rw [show ((713 / 500) : ℝ) = ((500 / 713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11506_neg : (277562941 / 500000000) ≤ -Real.log (287 / 500) ∧
    -Real.log (287 / 500) ≤ (555125883 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 787)) (n := 12)
    (lo := (277562941 / 500000000)) (hi := (555125883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 287) = 1/(287 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11506 : Bounds (-555125883 / 1000000000) (-277562941 / 500000000) (Real.log (287 / 500)) := by
  have h := reflection_log_11506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11507_neg : (425909 / 1000000000) ≤ -Real.log (500000 / 500213) ∧
    -Real.log (500000 / 500213) ≤ (42591 / 100000000) := by
  have h := checkLog_sound (w := (213 / 1000213)) (n := 12)
    (lo := (425909 / 1000000000)) (hi := (42591 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500213 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500213 / 500000) = 1/(500000 / 500213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11507 : Bounds (425909 / 1000000000) (42591 / 100000000) (Real.log (500213 / 500000)) := by
  have h := reflection_log_11507_neg
  have he : Real.log (500213 / 500000) = -Real.log (500000 / 500213) := by
    rw [show ((500213 / 500000) : ℝ) = ((500000 / 500213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11508_neg : (42609 / 100000000) ≤ -Real.log (499787 / 500000) ∧
    -Real.log (499787 / 500000) ≤ (426091 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 999787)) (n := 12)
    (lo := (42609 / 100000000)) (hi := (426091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499787) = 1/(499787 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11508 : Bounds (-426091 / 1000000000) (-42609 / 100000000) (Real.log (499787 / 500000)) := by
  have h := reflection_log_11508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11509_neg : (39706719 / 200000000) ≤ -Real.log (1000000 / 1219613) ∧
    -Real.log (1000000 / 1219613) ≤ (49633399 / 250000000) := by
  have h := checkLog_sound (w := (219613 / 2219613)) (n := 12)
    (lo := (39706719 / 200000000)) (hi := (49633399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219613 / 1000000) = 1/(1000000 / 1219613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11509 : Bounds (39706719 / 200000000) (49633399 / 250000000) (Real.log (1219613 / 1000000)) := by
  have h := reflection_log_11509_neg
  have he : Real.log (1219613 / 1000000) = -Real.log (1000000 / 1219613) := by
    rw [show ((1219613 / 1000000) : ℝ) = ((1000000 / 1219613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11510_neg : (15497833 / 62500000) ≤ -Real.log (780387 / 1000000) ∧
    -Real.log (780387 / 1000000) ≤ (247965329 / 1000000000) := by
  have h := checkLog_sound (w := (219613 / 1780387)) (n := 12)
    (lo := (15497833 / 62500000)) (hi := (247965329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780387) = 1/(780387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11510 : Bounds (-247965329 / 1000000000) (-15497833 / 62500000) (Real.log (780387 / 1000000)) := by
  have h := reflection_log_11510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11511_neg : (199324517 / 1000000000) ≤ -Real.log (500000 / 610289) ∧
    -Real.log (500000 / 610289) ≤ (99662259 / 500000000) := by
  have h := checkLog_sound (w := (110289 / 1110289)) (n := 12)
    (lo := (199324517 / 1000000000)) (hi := (99662259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610289 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610289 / 500000) = 1/(500000 / 610289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11511 : Bounds (199324517 / 1000000000) (99662259 / 500000000) (Real.log (610289 / 500000)) := by
  have h := reflection_log_11511_neg
  have he : Real.log (610289 / 500000) = -Real.log (500000 / 610289) := by
    rw [show ((610289 / 500000) : ℝ) = ((500000 / 610289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11512_neg : (249202659 / 1000000000) ≤ -Real.log (389711 / 500000) ∧
    -Real.log (389711 / 500000) ≤ (12460133 / 50000000) := by
  have h := checkLog_sound (w := (110289 / 889711)) (n := 12)
    (lo := (249202659 / 1000000000)) (hi := (12460133 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 389711) = 1/(389711 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11512 : Bounds (-12460133 / 50000000) (-249202659 / 1000000000) (Real.log (389711 / 500000)) := by
  have h := reflection_log_11512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11513_neg : (24939071 / 500000000) ≤ -Real.log (237836336479 / 250000000000) ∧
    -Real.log (237836336479 / 250000000000) ≤ (49878143 / 1000000000) := by
  have h := checkLog_sound (w := (12163663521 / 487836336479)) (n := 12)
    (lo := (24939071 / 500000000)) (hi := (49878143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237836336479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237836336479) = 1/(237836336479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11513 : Bounds (-49878143 / 1000000000) (-24939071 / 500000000) (Real.log (237836336479 / 250000000000)) := by
  have h := reflection_log_11513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11514_neg : (49431733 / 1000000000) ≤ -Real.log (951770130231 / 1000000000000) ∧
    -Real.log (951770130231 / 1000000000000) ≤ (24715867 / 500000000) := by
  have h := checkLog_sound (w := (48229869769 / 1951770130231)) (n := 12)
    (lo := (49431733 / 1000000000)) (hi := (24715867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 951770130231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 951770130231) = 1/(951770130231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11514 : Bounds (-24715867 / 500000000) (-49431733 / 1000000000) (Real.log (951770130231 / 1000000000000)) := by
  have h := reflection_log_11514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11515_neg : (446498923 / 1000000000) ≤ -Real.log (500000000000 / 781415502821) ∧
    -Real.log (500000000000 / 781415502821) ≤ (111624731 / 250000000) := by
  have h := checkLog_sound (w := (281415502821 / 1281415502821)) (n := 12)
    (lo := (446498923 / 1000000000)) (hi := (111624731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781415502821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781415502821 / 500000000000) = 1/(500000000000 / 781415502821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11515 : Bounds (446498923 / 1000000000) (111624731 / 250000000) (Real.log (781415502821 / 500000000000)) := by
  have h := reflection_log_11515_neg
  have he : Real.log (781415502821 / 500000000000) = -Real.log (500000000000 / 781415502821) := by
    rw [show ((781415502821 / 500000000000) : ℝ) = ((500000000000 / 781415502821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11516_neg : (56065897 / 125000000) ≤ -Real.log (250000000000 / 391501009723) ∧
    -Real.log (250000000000 / 391501009723) ≤ (448527177 / 1000000000) := by
  have h := checkLog_sound (w := (141501009723 / 641501009723)) (n := 12)
    (lo := (56065897 / 125000000)) (hi := (448527177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391501009723 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391501009723 / 250000000000) = 1/(250000000000 / 391501009723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11516 : Bounds (56065897 / 125000000) (448527177 / 1000000000) (Real.log (391501009723 / 250000000000)) := by
  have h := reflection_log_11516_neg
  have he : Real.log (391501009723 / 250000000000) = -Real.log (250000000000 / 391501009723) := by
    rw [show ((391501009723 / 250000000000) : ℝ) = ((250000000000 / 391501009723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11517_neg : (907557051 / 1000000000) ≤ -Real.log (250000000000 / 619565217391) ∧
    -Real.log (250000000000 / 619565217391) ≤ (907557053 / 1000000000) := by
  have h := checkLog_sound (w := (119565217391 / 1119565217391)) (n := 12)
    (lo := (214409871 / 1000000000)) (hi := (13400617 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619565217391 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(619565217391 / 500000000000) = 1/(250000000000 / 619565217391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11517 : Bounds (907557051 / 1000000000) (907557053 / 1000000000) (Real.log (619565217391 / 250000000000)) := by
  have h := reflection_log_11517_neg
  have he : Real.log (619565217391 / 250000000000) = -Real.log (250000000000 / 619565217391) := by
    rw [show ((619565217391 / 250000000000) : ℝ) = ((250000000000 / 619565217391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11518_neg : (227499801 / 250000000) ≤ -Real.log (250000000000 / 621080139373) ∧
    -Real.log (250000000000 / 621080139373) ≤ (454999603 / 500000000) := by
  have h := checkLog_sound (w := (121080139373 / 1121080139373)) (n := 12)
    (lo := (27106503 / 125000000)) (hi := (8674081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621080139373 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(621080139373 / 500000000000) = 1/(250000000000 / 621080139373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11518 : Bounds (227499801 / 250000000) (454999603 / 500000000) (Real.log (621080139373 / 250000000000)) := by
  have h := reflection_log_11518_neg
  have he : Real.log (621080139373 / 250000000000) = -Real.log (250000000000 / 621080139373) := by
    rw [show ((621080139373 / 250000000000) : ℝ) = ((250000000000 / 621080139373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11519_neg : (177787169 / 500000000) ≤ -Real.log (1000 / 1427) ∧
    -Real.log (1000 / 1427) ≤ (355574339 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 2427)) (n := 12)
    (lo := (177787169 / 500000000)) (hi := (355574339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427 / 1000) = 1/(1000 / 1427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11519 : Bounds (177787169 / 500000000) (355574339 / 1000000000) (Real.log (1427 / 1000)) := by
  have h := reflection_log_11519_neg
  have he : Real.log (1427 / 1000) = -Real.log (1000 / 1427) := by
    rw [show ((1427 / 1000) : ℝ) = ((1000 / 1427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0180 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11520_neg : (278434781 / 500000000) ≤ -Real.log (573 / 1000) ∧
    -Real.log (573 / 1000) ≤ (556869563 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 1573)) (n := 12)
    (lo := (278434781 / 500000000)) (hi := (556869563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 573) = 1/(573 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11520 : Bounds (-556869563 / 1000000000) (-278434781 / 500000000) (Real.log (573 / 1000)) := by
  have h := reflection_log_11520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11521_neg : (106727 / 250000000) ≤ -Real.log (1000000 / 1000427) ∧
    -Real.log (1000000 / 1000427) ≤ (426909 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 2000427)) (n := 12)
    (lo := (106727 / 250000000)) (hi := (426909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000427 / 1000000) = 1/(1000000 / 1000427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11521 : Bounds (106727 / 250000000) (426909 / 1000000000) (Real.log (1000427 / 1000000)) := by
  have h := reflection_log_11521_neg
  have he : Real.log (1000427 / 1000000) = -Real.log (1000000 / 1000427) := by
    rw [show ((1000427 / 1000000) : ℝ) = ((1000000 / 1000427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11522_neg : (427091 / 1000000000) ≤ -Real.log (999573 / 1000000) ∧
    -Real.log (999573 / 1000000) ≤ (106773 / 250000000) := by
  have h := checkLog_sound (w := (427 / 1999573)) (n := 12)
    (lo := (427091 / 1000000000)) (hi := (106773 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999573) = 1/(999573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11522 : Bounds (-106773 / 250000000) (-427091 / 1000000000) (Real.log (999573 / 1000000)) := by
  have h := reflection_log_11522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11523_neg : (99493867 / 500000000) ≤ -Real.log (1000000 / 1220167) ∧
    -Real.log (1000000 / 1220167) ≤ (39797547 / 200000000) := by
  have h := checkLog_sound (w := (220167 / 2220167)) (n := 12)
    (lo := (99493867 / 500000000)) (hi := (39797547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220167 / 1000000) = 1/(1000000 / 1220167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11523 : Bounds (99493867 / 500000000) (39797547 / 200000000) (Real.log (1220167 / 1000000)) := by
  have h := reflection_log_11523_neg
  have he : Real.log (1220167 / 1000000) = -Real.log (1000000 / 1220167) := by
    rw [show ((1220167 / 1000000) : ℝ) = ((1000000 / 1220167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11524_neg : (62168871 / 250000000) ≤ -Real.log (779833 / 1000000) ∧
    -Real.log (779833 / 1000000) ≤ (49735097 / 200000000) := by
  have h := checkLog_sound (w := (220167 / 1779833)) (n := 12)
    (lo := (62168871 / 250000000)) (hi := (49735097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779833) = 1/(779833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11524 : Bounds (-49735097 / 200000000) (-62168871 / 250000000) (Real.log (779833 / 1000000)) := by
  have h := reflection_log_11524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11525_neg : (49944779 / 250000000) ≤ -Real.log (1000000 / 1221133) ∧
    -Real.log (1000000 / 1221133) ≤ (199779117 / 1000000000) := by
  have h := checkLog_sound (w := (221133 / 2221133)) (n := 12)
    (lo := (49944779 / 250000000)) (hi := (199779117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221133 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221133 / 1000000) = 1/(1000000 / 1221133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11525 : Bounds (49944779 / 250000000) (199779117 / 1000000000) (Real.log (1221133 / 1000000)) := by
  have h := reflection_log_11525_neg
  have he : Real.log (1221133 / 1000000) = -Real.log (1000000 / 1221133) := by
    rw [show ((1221133 / 1000000) : ℝ) = ((1000000 / 1221133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11526_neg : (249914979 / 1000000000) ≤ -Real.log (778867 / 1000000) ∧
    -Real.log (778867 / 1000000) ≤ (12495749 / 50000000) := by
  have h := checkLog_sound (w := (221133 / 1778867)) (n := 12)
    (lo := (249914979 / 1000000000)) (hi := (12495749 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778867) = 1/(778867 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11526 : Bounds (-12495749 / 50000000) (-249914979 / 1000000000) (Real.log (778867 / 1000000)) := by
  have h := reflection_log_11526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11527_neg : (50135863 / 1000000000) ≤ -Real.log (951100196311 / 1000000000000) ∧
    -Real.log (951100196311 / 1000000000000) ≤ (6266983 / 125000000) := by
  have h := checkLog_sound (w := (48899803689 / 1951100196311)) (n := 12)
    (lo := (50135863 / 1000000000)) (hi := (6266983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 951100196311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 951100196311) = 1/(951100196311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11527 : Bounds (-6266983 / 125000000) (-50135863 / 1000000000) (Real.log (951100196311 / 1000000000000)) := by
  have h := reflection_log_11527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11528_neg : (198751 / 4000000) ≤ -Real.log (951526492111 / 1000000000000) ∧
    -Real.log (951526492111 / 1000000000000) ≤ (49687751 / 1000000000) := by
  have h := checkLog_sound (w := (48473507889 / 1951526492111)) (n := 12)
    (lo := (198751 / 4000000)) (hi := (49687751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 951526492111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 951526492111) = 1/(951526492111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11528 : Bounds (-49687751 / 1000000000) (-198751 / 4000000) (Real.log (951526492111 / 1000000000000)) := by
  have h := reflection_log_11528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11529_neg : (447663219 / 1000000000) ≤ -Real.log (500000000000 / 782325831299) ∧
    -Real.log (500000000000 / 782325831299) ≤ (22383161 / 50000000) := by
  have h := checkLog_sound (w := (282325831299 / 1282325831299)) (n := 12)
    (lo := (447663219 / 1000000000)) (hi := (22383161 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782325831299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782325831299 / 500000000000) = 1/(500000000000 / 782325831299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11529 : Bounds (447663219 / 1000000000) (22383161 / 50000000) (Real.log (782325831299 / 500000000000)) := by
  have h := reflection_log_11529_neg
  have he : Real.log (782325831299 / 500000000000) = -Real.log (500000000000 / 782325831299) := by
    rw [show ((782325831299 / 500000000000) : ℝ) = ((500000000000 / 782325831299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11530_neg : (89938819 / 200000000) ≤ -Real.log (500000000000 / 783916252711) ∧
    -Real.log (500000000000 / 783916252711) ≤ (28105881 / 62500000) := by
  have h := checkLog_sound (w := (283916252711 / 1283916252711)) (n := 12)
    (lo := (89938819 / 200000000)) (hi := (28105881 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783916252711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783916252711 / 500000000000) = 1/(500000000000 / 783916252711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11530 : Bounds (89938819 / 200000000) (28105881 / 62500000) (Real.log (783916252711 / 500000000000)) := by
  have h := reflection_log_11530_neg
  have he : Real.log (783916252711 / 500000000000) = -Real.log (500000000000 / 783916252711) := by
    rw [show ((783916252711 / 500000000000) : ℝ) = ((500000000000 / 783916252711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11531_neg : (227499801 / 250000000) ≤ -Real.log (100000000000 / 248432055749) ∧
    -Real.log (100000000000 / 248432055749) ≤ (454999603 / 500000000) := by
  have h := checkLog_sound (w := (48432055749 / 448432055749)) (n := 12)
    (lo := (27106503 / 125000000)) (hi := (8674081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248432055749 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(248432055749 / 200000000000) = 1/(100000000000 / 248432055749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11531 : Bounds (227499801 / 250000000) (454999603 / 500000000) (Real.log (248432055749 / 100000000000)) := by
  have h := reflection_log_11531_neg
  have he : Real.log (248432055749 / 100000000000) = -Real.log (100000000000 / 248432055749) := by
    rw [show ((248432055749 / 100000000000) : ℝ) = ((100000000000 / 248432055749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11532_neg : (9124439 / 10000000) ≤ -Real.log (500000000000 / 1245200698081) ∧
    -Real.log (500000000000 / 1245200698081) ≤ (456221951 / 500000000) := by
  have h := checkLog_sound (w := (245200698081 / 2245200698081)) (n := 12)
    (lo := (2741209 / 12500000)) (hi := (219296721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245200698081 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1245200698081 / 1000000000000) = 1/(500000000000 / 1245200698081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11532 : Bounds (9124439 / 10000000) (456221951 / 500000000) (Real.log (1245200698081 / 500000000000)) := by
  have h := reflection_log_11532_neg
  have he : Real.log (1245200698081 / 500000000000) = -Real.log (500000000000 / 1245200698081) := by
    rw [show ((1245200698081 / 500000000000) : ℝ) = ((500000000000 / 1245200698081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11533_neg : (356274863 / 1000000000) ≤ -Real.log (250 / 357) ∧
    -Real.log (250 / 357) ≤ (22267179 / 62500000) := by
  have h := checkLog_sound (w := (107 / 607)) (n := 12)
    (lo := (356274863 / 1000000000)) (hi := (22267179 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357 / 250) = 1/(250 / 357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11533 : Bounds (356274863 / 1000000000) (22267179 / 62500000) (Real.log (357 / 250)) := by
  have h := reflection_log_11533_neg
  have he : Real.log (357 / 250) = -Real.log (250 / 357) := by
    rw [show ((357 / 250) : ℝ) = ((250 / 357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11534_neg : (558616287 / 1000000000) ≤ -Real.log (143 / 250) ∧
    -Real.log (143 / 250) ≤ (17456759 / 31250000) := by
  have h := checkLog_sound (w := (107 / 393)) (n := 12)
    (lo := (558616287 / 1000000000)) (hi := (17456759 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 143) = 1/(143 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11534 : Bounds (-17456759 / 31250000) (-558616287 / 1000000000) (Real.log (143 / 250)) := by
  have h := reflection_log_11534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11535_neg : (106977 / 250000000) ≤ -Real.log (250000 / 250107) ∧
    -Real.log (250000 / 250107) ≤ (427909 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 500107)) (n := 12)
    (lo := (106977 / 250000000)) (hi := (427909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250107 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250107 / 250000) = 1/(250000 / 250107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11535 : Bounds (106977 / 250000000) (427909 / 1000000000) (Real.log (250107 / 250000)) := by
  have h := reflection_log_11535_neg
  have he : Real.log (250107 / 250000) = -Real.log (250000 / 250107) := by
    rw [show ((250107 / 250000) : ℝ) = ((250000 / 250107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11536_neg : (428091 / 1000000000) ≤ -Real.log (249893 / 250000) ∧
    -Real.log (249893 / 250000) ≤ (107023 / 250000000) := by
  have h := checkLog_sound (w := (107 / 499893)) (n := 12)
    (lo := (428091 / 1000000000)) (hi := (107023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249893) = 1/(249893 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11536 : Bounds (-107023 / 250000000) (-428091 / 1000000000) (Real.log (249893 / 250000)) := by
  have h := reflection_log_11536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11537_neg : (12465053 / 62500000) ≤ -Real.log (12500 / 15259) ∧
    -Real.log (12500 / 15259) ≤ (199440849 / 1000000000) := by
  have h := checkLog_sound (w := (2759 / 27759)) (n := 12)
    (lo := (12465053 / 62500000)) (hi := (199440849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15259 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15259 / 12500) = 1/(12500 / 15259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11537 : Bounds (12465053 / 62500000) (199440849 / 1000000000) (Real.log (15259 / 12500)) := by
  have h := reflection_log_11537_neg
  have he : Real.log (15259 / 12500) = -Real.log (12500 / 15259) := by
    rw [show ((15259 / 12500) : ℝ) = ((12500 / 15259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11538_neg : (124692431 / 500000000) ≤ -Real.log (9741 / 12500) ∧
    -Real.log (9741 / 12500) ≤ (249384863 / 1000000000) := by
  have h := checkLog_sound (w := (2759 / 22241)) (n := 12)
    (lo := (124692431 / 500000000)) (hi := (249384863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9741) = 1/(9741 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11538 : Bounds (-249384863 / 1000000000) (-124692431 / 500000000) (Real.log (9741 / 12500)) := by
  have h := reflection_log_11538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11539_neg : (20023269 / 100000000) ≤ -Real.log (1000000 / 1221687) ∧
    -Real.log (1000000 / 1221687) ≤ (200232691 / 1000000000) := by
  have h := checkLog_sound (w := (221687 / 2221687)) (n := 12)
    (lo := (20023269 / 100000000)) (hi := (200232691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221687 / 1000000) = 1/(1000000 / 1221687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11539 : Bounds (20023269 / 100000000) (200232691 / 1000000000) (Real.log (1221687 / 1000000)) := by
  have h := reflection_log_11539_neg
  have he : Real.log (1221687 / 1000000) = -Real.log (1000000 / 1221687) := by
    rw [show ((1221687 / 1000000) : ℝ) = ((1000000 / 1221687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11540_neg : (125313261 / 500000000) ≤ -Real.log (778313 / 1000000) ∧
    -Real.log (778313 / 1000000) ≤ (250626523 / 1000000000) := by
  have h := checkLog_sound (w := (221687 / 1778313)) (n := 12)
    (lo := (125313261 / 500000000)) (hi := (250626523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778313) = 1/(778313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11540 : Bounds (-250626523 / 1000000000) (-125313261 / 500000000) (Real.log (778313 / 1000000)) := by
  have h := reflection_log_11540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11541_neg : (50393831 / 1000000000) ≤ -Real.log (950854874031 / 1000000000000) ∧
    -Real.log (950854874031 / 1000000000000) ≤ (6299229 / 125000000) := by
  have h := checkLog_sound (w := (49145125969 / 1950854874031)) (n := 12)
    (lo := (50393831 / 1000000000)) (hi := (6299229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 950854874031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 950854874031) = 1/(950854874031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11541 : Bounds (-6299229 / 125000000) (-50393831 / 1000000000) (Real.log (950854874031 / 1000000000000)) := by
  have h := reflection_log_11541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11542_neg : (49944013 / 1000000000) ≤ -Real.log (148637919 / 156250000) ∧
    -Real.log (148637919 / 156250000) ≤ (24972007 / 500000000) := by
  have h := checkLog_sound (w := (7612081 / 304887919)) (n := 12)
    (lo := (49944013 / 1000000000)) (hi := (24972007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 148637919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 148637919) = 1/(148637919 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11542 : Bounds (-24972007 / 500000000) (-49944013 / 1000000000) (Real.log (148637919 / 156250000)) := by
  have h := reflection_log_11542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11543_neg : (448825711 / 1000000000) ≤ -Real.log (500000000000 / 783235807411) ∧
    -Real.log (500000000000 / 783235807411) ≤ (28051607 / 62500000) := by
  have h := checkLog_sound (w := (283235807411 / 1283235807411)) (n := 12)
    (lo := (448825711 / 1000000000)) (hi := (28051607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783235807411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783235807411 / 500000000000) = 1/(500000000000 / 783235807411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11543 : Bounds (448825711 / 1000000000) (28051607 / 62500000) (Real.log (783235807411 / 500000000000)) := by
  have h := reflection_log_11543_neg
  have he : Real.log (783235807411 / 500000000000) = -Real.log (500000000000 / 783235807411) := by
    rw [show ((783235807411 / 500000000000) : ℝ) = ((500000000000 / 783235807411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11544_neg : (112714803 / 250000000) ≤ -Real.log (62500000000 / 98103767379) ∧
    -Real.log (62500000000 / 98103767379) ≤ (450859213 / 1000000000) := by
  have h := checkLog_sound (w := (35603767379 / 160603767379)) (n := 12)
    (lo := (112714803 / 250000000)) (hi := (450859213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98103767379 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98103767379 / 62500000000) = 1/(62500000000 / 98103767379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11544 : Bounds (112714803 / 250000000) (450859213 / 1000000000) (Real.log (98103767379 / 62500000000)) := by
  have h := reflection_log_11544_neg
  have he : Real.log (98103767379 / 62500000000) = -Real.log (62500000000 / 98103767379) := by
    rw [show ((98103767379 / 62500000000) : ℝ) = ((62500000000 / 98103767379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11545_neg : (9124439 / 10000000) ≤ -Real.log (3125000000 / 7782504363) ∧
    -Real.log (3125000000 / 7782504363) ≤ (456221951 / 500000000) := by
  have h := checkLog_sound (w := (1532504363 / 14032504363)) (n := 12)
    (lo := (2741209 / 12500000)) (hi := (219296721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7782504363 / 6250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(7782504363 / 6250000000) = 1/(3125000000 / 7782504363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11545 : Bounds (9124439 / 10000000) (456221951 / 500000000) (Real.log (7782504363 / 3125000000)) := by
  have h := reflection_log_11545_neg
  have he : Real.log (7782504363 / 3125000000) = -Real.log (3125000000 / 7782504363) := by
    rw [show ((7782504363 / 3125000000) : ℝ) = ((3125000000 / 7782504363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11546_neg : (18297823 / 20000000) ≤ -Real.log (125000000000 / 312062937063) ∧
    -Real.log (125000000000 / 312062937063) ≤ (57180697 / 62500000) := by
  have h := checkLog_sound (w := (62062937063 / 562062937063)) (n := 12)
    (lo := (22174397 / 100000000)) (hi := (221743971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312062937063 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(312062937063 / 250000000000) = 1/(125000000000 / 312062937063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11546 : Bounds (18297823 / 20000000) (57180697 / 62500000) (Real.log (312062937063 / 125000000000)) := by
  have h := reflection_log_11546_neg
  have he : Real.log (312062937063 / 125000000000) = -Real.log (125000000000 / 312062937063) := by
    rw [show ((312062937063 / 125000000000) : ℝ) = ((125000000000 / 312062937063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11547_neg : (178487449 / 500000000) ≤ -Real.log (1000 / 1429) ∧
    -Real.log (1000 / 1429) ≤ (356974899 / 1000000000) := by
  have h := checkLog_sound (w := (429 / 2429)) (n := 12)
    (lo := (178487449 / 500000000)) (hi := (356974899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1429 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1429 / 1000) = 1/(1000 / 1429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11547 : Bounds (178487449 / 500000000) (356974899 / 1000000000) (Real.log (1429 / 1000)) := by
  have h := reflection_log_11547_neg
  have he : Real.log (1429 / 1000) = -Real.log (1000 / 1429) := by
    rw [show ((1429 / 1000) : ℝ) = ((1000 / 1429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11548_neg : (560366069 / 1000000000) ≤ -Real.log (571 / 1000) ∧
    -Real.log (571 / 1000) ≤ (56036607 / 100000000) := by
  have h := checkLog_sound (w := (429 / 1571)) (n := 12)
    (lo := (560366069 / 1000000000)) (hi := (56036607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 571) = 1/(571 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11548 : Bounds (-56036607 / 100000000) (-560366069 / 1000000000) (Real.log (571 / 1000)) := by
  have h := reflection_log_11548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11549_neg : (107227 / 250000000) ≤ -Real.log (1000000 / 1000429) ∧
    -Real.log (1000000 / 1000429) ≤ (428909 / 1000000000) := by
  have h := checkLog_sound (w := (429 / 2000429)) (n := 12)
    (lo := (107227 / 250000000)) (hi := (428909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000429 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000429 / 1000000) = 1/(1000000 / 1000429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11549 : Bounds (107227 / 250000000) (428909 / 1000000000) (Real.log (1000429 / 1000000)) := by
  have h := reflection_log_11549_neg
  have he : Real.log (1000429 / 1000000) = -Real.log (1000000 / 1000429) := by
    rw [show ((1000429 / 1000000) : ℝ) = ((1000000 / 1000429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11550_neg : (107273 / 250000000) ≤ -Real.log (999571 / 1000000) ∧
    -Real.log (999571 / 1000000) ≤ (429093 / 1000000000) := by
  have h := checkLog_sound (w := (429 / 1999571)) (n := 12)
    (lo := (107273 / 250000000)) (hi := (429093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999571) = 1/(999571 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11550 : Bounds (-429093 / 1000000000) (-107273 / 250000000) (Real.log (999571 / 1000000)) := by
  have h := reflection_log_11550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11551_neg : (12493411 / 62500000) ≤ -Real.log (500000 / 610637) ∧
    -Real.log (500000 / 610637) ≤ (199894577 / 1000000000) := by
  have h := checkLog_sound (w := (110637 / 1110637)) (n := 12)
    (lo := (12493411 / 62500000)) (hi := (199894577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610637 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610637 / 500000) = 1/(500000 / 610637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11551 : Bounds (12493411 / 62500000) (199894577 / 1000000000) (Real.log (610637 / 500000)) := by
  have h := reflection_log_11551_neg
  have he : Real.log (610637 / 500000) = -Real.log (500000 / 610637) := by
    rw [show ((610637 / 500000) : ℝ) = ((500000 / 610637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11552_neg : (250096027 / 1000000000) ≤ -Real.log (389363 / 500000) ∧
    -Real.log (389363 / 500000) ≤ (62524007 / 250000000) := by
  have h := checkLog_sound (w := (110637 / 889363)) (n := 12)
    (lo := (250096027 / 1000000000)) (hi := (62524007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 389363) = 1/(389363 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11552 : Bounds (-62524007 / 250000000) (-250096027 / 1000000000) (Real.log (389363 / 500000)) := by
  have h := reflection_log_11552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11553_neg : (200686877 / 1000000000) ≤ -Real.log (500000 / 611121) ∧
    -Real.log (500000 / 611121) ≤ (100343439 / 500000000) := by
  have h := checkLog_sound (w := (111121 / 1111121)) (n := 12)
    (lo := (200686877 / 1000000000)) (hi := (100343439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611121 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611121 / 500000) = 1/(500000 / 611121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11553 : Bounds (200686877 / 1000000000) (100343439 / 500000000) (Real.log (611121 / 500000)) := by
  have h := reflection_log_11553_neg
  have he : Real.log (611121 / 500000) = -Real.log (500000 / 611121) := by
    rw [show ((611121 / 500000) : ℝ) = ((500000 / 611121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11554_neg : (251339857 / 1000000000) ≤ -Real.log (388879 / 500000) ∧
    -Real.log (388879 / 500000) ≤ (125669929 / 500000000) := by
  have h := checkLog_sound (w := (111121 / 888879)) (n := 12)
    (lo := (251339857 / 1000000000)) (hi := (125669929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388879) = 1/(388879 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11554 : Bounds (-125669929 / 500000000) (-251339857 / 1000000000) (Real.log (388879 / 500000)) := by
  have h := reflection_log_11554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11555_neg : (2532649 / 50000000) ≤ -Real.log (237652123359 / 250000000000) ∧
    -Real.log (237652123359 / 250000000000) ≤ (50652981 / 1000000000) := by
  have h := checkLog_sound (w := (12347876641 / 487652123359)) (n := 12)
    (lo := (2532649 / 50000000)) (hi := (50652981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237652123359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237652123359) = 1/(237652123359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11555 : Bounds (-50652981 / 1000000000) (-2532649 / 50000000) (Real.log (237652123359 / 250000000000)) := by
  have h := reflection_log_11555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11556_neg : (50201451 / 1000000000) ≤ -Real.log (237759454231 / 250000000000) ∧
    -Real.log (237759454231 / 250000000000) ≤ (12550363 / 250000000) := by
  have h := checkLog_sound (w := (12240545769 / 487759454231)) (n := 12)
    (lo := (50201451 / 1000000000)) (hi := (12550363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237759454231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237759454231) = 1/(237759454231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11556 : Bounds (-12550363 / 250000000) (-50201451 / 1000000000) (Real.log (237759454231 / 250000000000)) := by
  have h := reflection_log_11556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11557_neg : (112497651 / 250000000) ≤ -Real.log (62500000000 / 98018590621) ∧
    -Real.log (62500000000 / 98018590621) ≤ (89998121 / 200000000) := by
  have h := checkLog_sound (w := (35518590621 / 160518590621)) (n := 12)
    (lo := (112497651 / 250000000)) (hi := (89998121 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98018590621 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98018590621 / 62500000000) = 1/(62500000000 / 98018590621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11557 : Bounds (112497651 / 250000000) (89998121 / 200000000) (Real.log (98018590621 / 62500000000)) := by
  have h := reflection_log_11557_neg
  have he : Real.log (98018590621 / 62500000000) = -Real.log (62500000000 / 98018590621) := by
    rw [show ((98018590621 / 62500000000) : ℝ) = ((62500000000 / 98018590621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11558_neg : (226013367 / 500000000) ≤ -Real.log (62500000000 / 98218372553) ∧
    -Real.log (62500000000 / 98218372553) ≤ (90405347 / 200000000) := by
  have h := checkLog_sound (w := (35718372553 / 160718372553)) (n := 12)
    (lo := (226013367 / 500000000)) (hi := (90405347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98218372553 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98218372553 / 62500000000) = 1/(62500000000 / 98218372553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11558 : Bounds (226013367 / 500000000) (90405347 / 200000000) (Real.log (98218372553 / 62500000000)) := by
  have h := reflection_log_11558_neg
  have he : Real.log (98218372553 / 62500000000) = -Real.log (62500000000 / 98218372553) := by
    rw [show ((98218372553 / 62500000000) : ℝ) = ((62500000000 / 98218372553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11559_neg : (18297823 / 20000000) ≤ -Real.log (500000000000 / 1248251748251) ∧
    -Real.log (500000000000 / 1248251748251) ≤ (57180697 / 62500000) := by
  have h := checkLog_sound (w := (248251748251 / 2248251748251)) (n := 12)
    (lo := (22174397 / 100000000)) (hi := (221743971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248251748251 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1248251748251 / 1000000000000) = 1/(500000000000 / 1248251748251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11559 : Bounds (18297823 / 20000000) (57180697 / 62500000) (Real.log (1248251748251 / 500000000000)) := by
  have h := reflection_log_11559_neg
  have he : Real.log (1248251748251 / 500000000000) = -Real.log (500000000000 / 1248251748251) := by
    rw [show ((1248251748251 / 500000000000) : ℝ) = ((500000000000 / 1248251748251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11560_neg : (917340967 / 1000000000) ≤ -Real.log (250000000000 / 625656742557) ∧
    -Real.log (250000000000 / 625656742557) ≤ (917340969 / 1000000000) := by
  have h := checkLog_sound (w := (125656742557 / 1125656742557)) (n := 12)
    (lo := (224193787 / 1000000000)) (hi := (56048447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625656742557 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(625656742557 / 500000000000) = 1/(250000000000 / 625656742557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11560 : Bounds (917340967 / 1000000000) (917340969 / 1000000000) (Real.log (625656742557 / 250000000000)) := by
  have h := reflection_log_11560_neg
  have he : Real.log (625656742557 / 250000000000) = -Real.log (250000000000 / 625656742557) := by
    rw [show ((625656742557 / 250000000000) : ℝ) = ((250000000000 / 625656742557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11561_neg : (89418611 / 250000000) ≤ -Real.log (100 / 143) ∧
    -Real.log (100 / 143) ≤ (71534889 / 200000000) := by
  have h := checkLog_sound (w := (43 / 243)) (n := 12)
    (lo := (89418611 / 250000000)) (hi := (71534889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143 / 100) = 1/(100 / 143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11561 : Bounds (89418611 / 250000000) (71534889 / 200000000) (Real.log (143 / 100)) := by
  have h := reflection_log_11561_neg
  have he : Real.log (143 / 100) = -Real.log (100 / 143) := by
    rw [show ((143 / 100) : ℝ) = ((100 / 143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11562_neg : (281059459 / 500000000) ≤ -Real.log (57 / 100) ∧
    -Real.log (57 / 100) ≤ (562118919 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 157)) (n := 12)
    (lo := (281059459 / 500000000)) (hi := (562118919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 57) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 57) = 1/(57 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11562 : Bounds (-562118919 / 1000000000) (-281059459 / 500000000) (Real.log (57 / 100)) := by
  have h := reflection_log_11562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11563_neg : (429907 / 1000000000) ≤ -Real.log (100000 / 100043) ∧
    -Real.log (100000 / 100043) ≤ (107477 / 250000000) := by
  have h := checkLog_sound (w := (43 / 200043)) (n := 12)
    (lo := (429907 / 1000000000)) (hi := (107477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100043 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100043 / 100000) = 1/(100000 / 100043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11563 : Bounds (429907 / 1000000000) (107477 / 250000000) (Real.log (100043 / 100000)) := by
  have h := reflection_log_11563_neg
  have he : Real.log (100043 / 100000) = -Real.log (100000 / 100043) := by
    rw [show ((100043 / 100000) : ℝ) = ((100000 / 100043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11564_neg : (107523 / 250000000) ≤ -Real.log (99957 / 100000) ∧
    -Real.log (99957 / 100000) ≤ (430093 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 199957)) (n := 12)
    (lo := (107523 / 250000000)) (hi := (430093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99957) = 1/(99957 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11564 : Bounds (-430093 / 1000000000) (-107523 / 250000000) (Real.log (99957 / 100000)) := by
  have h := reflection_log_11564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11565_neg : (200348097 / 1000000000) ≤ -Real.log (250000 / 305457) ∧
    -Real.log (250000 / 305457) ≤ (100174049 / 500000000) := by
  have h := checkLog_sound (w := (55457 / 555457)) (n := 12)
    (lo := (200348097 / 1000000000)) (hi := (100174049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305457 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305457 / 250000) = 1/(250000 / 305457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11565 : Bounds (200348097 / 1000000000) (100174049 / 500000000) (Real.log (305457 / 250000)) := by
  have h := reflection_log_11565_neg
  have he : Real.log (305457 / 250000) = -Real.log (250000 / 305457) := by
    rw [show ((305457 / 250000) : ℝ) = ((250000 / 305457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11566_neg : (250807699 / 1000000000) ≤ -Real.log (194543 / 250000) ∧
    -Real.log (194543 / 250000) ≤ (2508077 / 10000000) := by
  have h := checkLog_sound (w := (55457 / 444543)) (n := 12)
    (lo := (250807699 / 1000000000)) (hi := (2508077 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194543) = 1/(194543 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11566 : Bounds (-2508077 / 10000000) (-250807699 / 1000000000) (Real.log (194543 / 250000)) := by
  have h := reflection_log_11566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11567_neg : (8045667 / 40000000) ≤ -Real.log (500000 / 611399) ∧
    -Real.log (500000 / 611399) ≤ (50285419 / 250000000) := by
  have h := checkLog_sound (w := (111399 / 1111399)) (n := 12)
    (lo := (8045667 / 40000000)) (hi := (50285419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611399 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611399 / 500000) = 1/(500000 / 611399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11567 : Bounds (8045667 / 40000000) (50285419 / 250000000) (Real.log (611399 / 500000)) := by
  have h := reflection_log_11567_neg
  have he : Real.log (611399 / 500000) = -Real.log (500000 / 611399) := by
    rw [show ((611399 / 500000) : ℝ) = ((500000 / 611399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11568_neg : (63013747 / 250000000) ≤ -Real.log (388601 / 500000) ∧
    -Real.log (388601 / 500000) ≤ (252054989 / 1000000000) := by
  have h := checkLog_sound (w := (111399 / 888601)) (n := 12)
    (lo := (63013747 / 250000000)) (hi := (252054989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388601) = 1/(388601 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11568 : Bounds (-252054989 / 1000000000) (-63013747 / 250000000) (Real.log (388601 / 500000)) := by
  have h := reflection_log_11568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11569_neg : (1591041 / 31250000) ≤ -Real.log (237590262799 / 250000000000) ∧
    -Real.log (237590262799 / 250000000000) ≤ (50913313 / 1000000000) := by
  have h := checkLog_sound (w := (12409737201 / 487590262799)) (n := 12)
    (lo := (1591041 / 31250000)) (hi := (50913313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237590262799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237590262799) = 1/(237590262799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11569 : Bounds (-50913313 / 1000000000) (-1591041 / 31250000) (Real.log (237590262799 / 250000000000)) := by
  have h := reflection_log_11569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11570_neg : (50459601 / 1000000000) ≤ -Real.log (59424521151 / 62500000000) ∧
    -Real.log (59424521151 / 62500000000) ≤ (25229801 / 500000000) := by
  have h := checkLog_sound (w := (3075478849 / 121924521151)) (n := 12)
    (lo := (50459601 / 1000000000)) (hi := (25229801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59424521151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59424521151) = 1/(59424521151 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11570 : Bounds (-25229801 / 500000000) (-50459601 / 1000000000) (Real.log (59424521151 / 62500000000)) := by
  have h := reflection_log_11570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11571_neg : (451155797 / 1000000000) ≤ -Real.log (250000000000 / 392531471191) ∧
    -Real.log (250000000000 / 392531471191) ≤ (225577899 / 500000000) := by
  have h := checkLog_sound (w := (142531471191 / 642531471191)) (n := 12)
    (lo := (451155797 / 1000000000)) (hi := (225577899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392531471191 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392531471191 / 250000000000) = 1/(250000000000 / 392531471191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11571 : Bounds (451155797 / 1000000000) (225577899 / 500000000) (Real.log (392531471191 / 250000000000)) := by
  have h := reflection_log_11571_neg
  have he : Real.log (392531471191 / 250000000000) = -Real.log (250000000000 / 392531471191) := by
    rw [show ((392531471191 / 250000000000) : ℝ) = ((250000000000 / 392531471191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11572_neg : (453196663 / 1000000000) ≤ -Real.log (125000000000 / 196666696689) ∧
    -Real.log (125000000000 / 196666696689) ≤ (56649583 / 125000000) := by
  have h := checkLog_sound (w := (71666696689 / 321666696689)) (n := 12)
    (lo := (453196663 / 1000000000)) (hi := (56649583 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196666696689 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196666696689 / 125000000000) = 1/(125000000000 / 196666696689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11572 : Bounds (453196663 / 1000000000) (56649583 / 125000000) (Real.log (196666696689 / 125000000000)) := by
  have h := reflection_log_11572_neg
  have he : Real.log (196666696689 / 125000000000) = -Real.log (125000000000 / 196666696689) := by
    rw [show ((196666696689 / 125000000000) : ℝ) = ((125000000000 / 196666696689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11573_neg : (917340967 / 1000000000) ≤ -Real.log (500000000000 / 1251313485113) ∧
    -Real.log (500000000000 / 1251313485113) ≤ (917340969 / 1000000000) := by
  have h := checkLog_sound (w := (251313485113 / 2251313485113)) (n := 12)
    (lo := (224193787 / 1000000000)) (hi := (56048447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251313485113 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1251313485113 / 1000000000000) = 1/(500000000000 / 1251313485113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11573 : Bounds (917340967 / 1000000000) (917340969 / 1000000000) (Real.log (1251313485113 / 500000000000)) := by
  have h := reflection_log_11573_neg
  have he : Real.log (1251313485113 / 500000000000) = -Real.log (500000000000 / 1251313485113) := by
    rw [show ((1251313485113 / 500000000000) : ℝ) = ((500000000000 / 1251313485113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11574_neg : (919793361 / 1000000000) ≤ -Real.log (500000000000 / 1254385964913) ∧
    -Real.log (500000000000 / 1254385964913) ≤ (919793363 / 1000000000) := by
  have h := checkLog_sound (w := (254385964913 / 2254385964913)) (n := 12)
    (lo := (226646181 / 1000000000)) (hi := (113323091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254385964913 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1254385964913 / 1000000000000) = 1/(500000000000 / 1254385964913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11574 : Bounds (919793361 / 1000000000) (919793363 / 1000000000) (Real.log (1254385964913 / 500000000000)) := by
  have h := reflection_log_11574_neg
  have he : Real.log (1254385964913 / 500000000000) = -Real.log (500000000000 / 1254385964913) := by
    rw [show ((1254385964913 / 500000000000) : ℝ) = ((500000000000 / 1254385964913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11575_neg : (716747 / 2000000) ≤ -Real.log (1000 / 1431) ∧
    -Real.log (1000 / 1431) ≤ (358373501 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2431)) (n := 12)
    (lo := (716747 / 2000000)) (hi := (358373501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1431 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1431 / 1000) = 1/(1000 / 1431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11575 : Bounds (716747 / 2000000) (358373501 / 1000000000) (Real.log (1431 / 1000)) := by
  have h := reflection_log_11575_neg
  have he : Real.log (1431 / 1000) = -Real.log (1000 / 1431) := by
    rw [show ((1431 / 1000) : ℝ) = ((1000 / 1431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11576_neg : (140968711 / 250000000) ≤ -Real.log (569 / 1000) ∧
    -Real.log (569 / 1000) ≤ (112774969 / 200000000) := by
  have h := checkLog_sound (w := (431 / 1569)) (n := 12)
    (lo := (140968711 / 250000000)) (hi := (112774969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 569) = 1/(569 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11576 : Bounds (-112774969 / 200000000) (-140968711 / 250000000) (Real.log (569 / 1000)) := by
  have h := reflection_log_11576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11577_neg : (430907 / 1000000000) ≤ -Real.log (1000000 / 1000431) ∧
    -Real.log (1000000 / 1000431) ≤ (107727 / 250000000) := by
  have h := checkLog_sound (w := (431 / 2000431)) (n := 12)
    (lo := (430907 / 1000000000)) (hi := (107727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000431 / 1000000) = 1/(1000000 / 1000431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11577 : Bounds (430907 / 1000000000) (107727 / 250000000) (Real.log (1000431 / 1000000)) := by
  have h := reflection_log_11577_neg
  have he : Real.log (1000431 / 1000000) = -Real.log (1000000 / 1000431) := by
    rw [show ((1000431 / 1000000) : ℝ) = ((1000000 / 1000431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11578_neg : (107773 / 250000000) ≤ -Real.log (999569 / 1000000) ∧
    -Real.log (999569 / 1000000) ≤ (431093 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 1999569)) (n := 12)
    (lo := (107773 / 250000000)) (hi := (431093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999569) = 1/(999569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11578 : Bounds (-431093 / 1000000000) (-107773 / 250000000) (Real.log (999569 / 1000000)) := by
  have h := reflection_log_11578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11579_neg : (25100279 / 125000000) ≤ -Real.log (1000000 / 1222383) ∧
    -Real.log (1000000 / 1222383) ≤ (200802233 / 1000000000) := by
  have h := checkLog_sound (w := (222383 / 2222383)) (n := 12)
    (lo := (25100279 / 125000000)) (hi := (200802233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222383 / 1000000) = 1/(1000000 / 1222383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11579 : Bounds (25100279 / 125000000) (200802233 / 1000000000) (Real.log (1222383 / 1000000)) := by
  have h := reflection_log_11579_neg
  have he : Real.log (1222383 / 1000000) = -Real.log (1000000 / 1222383) := by
    rw [show ((1222383 / 1000000) : ℝ) = ((1000000 / 1222383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11580_neg : (251521163 / 1000000000) ≤ -Real.log (777617 / 1000000) ∧
    -Real.log (777617 / 1000000) ≤ (62880291 / 250000000) := by
  have h := checkLog_sound (w := (222383 / 1777617)) (n := 12)
    (lo := (251521163 / 1000000000)) (hi := (62880291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777617) = 1/(777617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11580 : Bounds (-62880291 / 250000000) (-251521163 / 1000000000) (Real.log (777617 / 1000000)) := by
  have h := reflection_log_11580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11581_neg : (100798133 / 500000000) ≤ -Real.log (500000 / 611677) ∧
    -Real.log (500000 / 611677) ≤ (201596267 / 1000000000) := by
  have h := checkLog_sound (w := (111677 / 1111677)) (n := 12)
    (lo := (100798133 / 500000000)) (hi := (201596267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611677 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611677 / 500000) = 1/(500000 / 611677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11581 : Bounds (100798133 / 500000000) (201596267 / 1000000000) (Real.log (611677 / 500000)) := by
  have h := reflection_log_11581_neg
  have he : Real.log (611677 / 500000) = -Real.log (500000 / 611677) := by
    rw [show ((611677 / 500000) : ℝ) = ((500000 / 611677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11582_neg : (25277063 / 100000000) ≤ -Real.log (388323 / 500000) ∧
    -Real.log (388323 / 500000) ≤ (252770631 / 1000000000) := by
  have h := checkLog_sound (w := (111677 / 888323)) (n := 12)
    (lo := (25277063 / 100000000)) (hi := (252770631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388323) = 1/(388323 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11582 : Bounds (-252770631 / 1000000000) (-25277063 / 100000000) (Real.log (388323 / 500000)) := by
  have h := reflection_log_11582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11583_neg : (51174363 / 1000000000) ≤ -Real.log (237528247671 / 250000000000) ∧
    -Real.log (237528247671 / 250000000000) ≤ (12793591 / 250000000) := by
  have h := checkLog_sound (w := (12471752329 / 487528247671)) (n := 12)
    (lo := (51174363 / 1000000000)) (hi := (12793591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237528247671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237528247671) = 1/(237528247671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11583 : Bounds (-12793591 / 250000000) (-51174363 / 1000000000) (Real.log (237528247671 / 250000000000)) := by
  have h := reflection_log_11583_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


