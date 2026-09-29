-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0083__3_q00
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0083__3_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:35:53.667283+00:00
-- url     : https://prove2.me/theorems/2f1127e3-7955-4a0c-8cfa-b65a434b0a0c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0084, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0085) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0083 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0084, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0085) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0083 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5312_neg : (4513929 / 500000000) ≤ -Real.log (991012770399 / 1000000000000) ∧
    -Real.log (991012770399 / 1000000000000) ≤ (9027859 / 1000000000) := by
  have h := checkLog_sound (w := (8987229601 / 1991012770399)) (n := 12)
    (lo := (4513929 / 500000000)) (hi := (9027859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991012770399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991012770399) = 1/(991012770399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5312 : Bounds (-9027859 / 1000000000) (-4513929 / 500000000) (Real.log (991012770399 / 1000000000000)) := by
  have h := reflection_log_5312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5313_neg : (8982191 / 1000000000) ≤ -Real.log (247764507039 / 250000000000) ∧
    -Real.log (247764507039 / 250000000000) ≤ (561387 / 62500000) := by
  have h := checkLog_sound (w := (2235492961 / 497764507039)) (n := 12)
    (lo := (8982191 / 1000000000)) (hi := (561387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247764507039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247764507039) = 1/(247764507039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5313 : Bounds (-561387 / 62500000) (-8982191 / 1000000000) (Real.log (247764507039 / 250000000000)) := by
  have h := reflection_log_5313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5314_neg : (189690757 / 1000000000) ≤ -Real.log (500000000000 / 604437852177) ∧
    -Real.log (500000000000 / 604437852177) ≤ (94845379 / 500000000) := by
  have h := checkLog_sound (w := (104437852177 / 1104437852177)) (n := 12)
    (lo := (189690757 / 1000000000)) (hi := (94845379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604437852177 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604437852177 / 500000000000) = 1/(500000000000 / 604437852177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5314 : Bounds (189690757 / 1000000000) (94845379 / 500000000) (Real.log (604437852177 / 500000000000)) := by
  have h := reflection_log_5314_neg
  have he : Real.log (604437852177 / 500000000000) = -Real.log (500000000000 / 604437852177) := by
    rw [show ((604437852177 / 500000000000) : ℝ) = ((500000000000 / 604437852177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5315_neg : (190173081 / 1000000000) ≤ -Real.log (781250000 / 944889777) ∧
    -Real.log (781250000 / 944889777) ≤ (95086541 / 500000000) := by
  have h := checkLog_sound (w := (163639777 / 1726139777)) (n := 12)
    (lo := (190173081 / 1000000000)) (hi := (95086541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((944889777 / 781250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(944889777 / 781250000) = 1/(781250000 / 944889777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5315 : Bounds (190173081 / 1000000000) (95086541 / 500000000) (Real.log (944889777 / 781250000)) := by
  have h := reflection_log_5315_neg
  have he : Real.log (944889777 / 781250000) = -Real.log (781250000 / 944889777) := by
    rw [show ((944889777 / 781250000) : ℝ) = ((781250000 / 944889777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5316_neg : (380733491 / 1000000000) ≤ -Real.log (250000000000 / 365839389087) ∧
    -Real.log (250000000000 / 365839389087) ≤ (95183373 / 250000000) := by
  have h := checkLog_sound (w := (115839389087 / 615839389087)) (n := 12)
    (lo := (380733491 / 1000000000)) (hi := (95183373 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365839389087 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365839389087 / 250000000000) = 1/(250000000000 / 365839389087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5316 : Bounds (380733491 / 1000000000) (95183373 / 250000000) (Real.log (365839389087 / 250000000000)) := by
  have h := reflection_log_5316_neg
  have he : Real.log (365839389087 / 250000000000) = -Real.log (250000000000 / 365839389087) := by
    rw [show ((365839389087 / 250000000000) : ℝ) = ((250000000000 / 365839389087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5317_neg : (380940831 / 1000000000) ≤ -Real.log (125000000000 / 182957625031) ∧
    -Real.log (125000000000 / 182957625031) ≤ (11904401 / 31250000) := by
  have h := checkLog_sound (w := (57957625031 / 307957625031)) (n := 12)
    (lo := (380940831 / 1000000000)) (hi := (11904401 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182957625031 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182957625031 / 125000000000) = 1/(125000000000 / 182957625031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5317 : Bounds (380940831 / 1000000000) (11904401 / 31250000) (Real.log (182957625031 / 125000000000)) := by
  have h := reflection_log_5317_neg
  have he : Real.log (182957625031 / 125000000000) = -Real.log (125000000000 / 182957625031) := by
    rw [show ((182957625031 / 125000000000) : ℝ) = ((125000000000 / 182957625031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5318_neg : (86261857 / 500000000) ≤ -Real.log (10000 / 11883) ∧
    -Real.log (10000 / 11883) ≤ (34504743 / 200000000) := by
  have h := checkLog_sound (w := (1883 / 21883)) (n := 12)
    (lo := (86261857 / 500000000)) (hi := (34504743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11883 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11883 / 10000) = 1/(10000 / 11883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5318 : Bounds (86261857 / 500000000) (34504743 / 200000000) (Real.log (11883 / 10000)) := by
  have h := reflection_log_5318_neg
  have he : Real.log (11883 / 10000) = -Real.log (10000 / 11883) := by
    rw [show ((11883 / 10000) : ℝ) = ((10000 / 11883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5319_neg : (41724893 / 200000000) ≤ -Real.log (8117 / 10000) ∧
    -Real.log (8117 / 10000) ≤ (104312233 / 500000000) := by
  have h := checkLog_sound (w := (1883 / 18117)) (n := 12)
    (lo := (41724893 / 200000000)) (hi := (104312233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8117) = 1/(8117 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5319 : Bounds (-104312233 / 500000000) (-41724893 / 200000000) (Real.log (8117 / 10000)) := by
  have h := reflection_log_5319_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5320_neg : (94141 / 500000000) ≤ -Real.log (10000000 / 10001883) ∧
    -Real.log (10000000 / 10001883) ≤ (188283 / 1000000000) := by
  have h := checkLog_sound (w := (1883 / 20001883)) (n := 12)
    (lo := (94141 / 500000000)) (hi := (188283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001883 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001883 / 10000000) = 1/(10000000 / 10001883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5320 : Bounds (94141 / 500000000) (188283 / 1000000000) (Real.log (10001883 / 10000000)) := by
  have h := reflection_log_5320_neg
  have he : Real.log (10001883 / 10000000) = -Real.log (10000000 / 10001883) := by
    rw [show ((10001883 / 10000000) : ℝ) = ((10000000 / 10001883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5321_neg : (188317 / 1000000000) ≤ -Real.log (9998117 / 10000000) ∧
    -Real.log (9998117 / 10000000) ≤ (94159 / 500000000) := by
  have h := checkLog_sound (w := (1883 / 19998117)) (n := 12)
    (lo := (188317 / 1000000000)) (hi := (94159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998117) = 1/(9998117 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5321 : Bounds (-94159 / 500000000) (-188317 / 1000000000) (Real.log (9998117 / 10000000)) := by
  have h := reflection_log_5321_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5322_neg : (22600219 / 250000000) ≤ -Real.log (1000000 / 1094613) ∧
    -Real.log (1000000 / 1094613) ≤ (90400877 / 1000000000) := by
  have h := checkLog_sound (w := (94613 / 2094613)) (n := 12)
    (lo := (22600219 / 250000000)) (hi := (90400877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094613 / 1000000) = 1/(1000000 / 1094613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5322 : Bounds (22600219 / 250000000) (90400877 / 1000000000) (Real.log (1094613 / 1000000)) := by
  have h := reflection_log_5322_neg
  have he : Real.log (1094613 / 1000000) = -Real.log (1000000 / 1094613) := by
    rw [show ((1094613 / 1000000) : ℝ) = ((1000000 / 1094613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5323_neg : (49696401 / 500000000) ≤ -Real.log (905387 / 1000000) ∧
    -Real.log (905387 / 1000000) ≤ (99392803 / 1000000000) := by
  have h := checkLog_sound (w := (94613 / 1905387)) (n := 12)
    (lo := (49696401 / 500000000)) (hi := (99392803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905387) = 1/(905387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5323 : Bounds (-99392803 / 1000000000) (-49696401 / 500000000) (Real.log (905387 / 1000000)) := by
  have h := reflection_log_5323_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5324_neg : (45309597 / 500000000) ≤ -Real.log (250000 / 273713) ∧
    -Real.log (250000 / 273713) ≤ (18123839 / 200000000) := by
  have h := checkLog_sound (w := (23713 / 523713)) (n := 12)
    (lo := (45309597 / 500000000)) (hi := (18123839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273713 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273713 / 250000) = 1/(250000 / 273713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5324 : Bounds (45309597 / 500000000) (18123839 / 200000000) (Real.log (273713 / 250000)) := by
  have h := reflection_log_5324_neg
  have he : Real.log (273713 / 250000) = -Real.log (250000 / 273713) := by
    rw [show ((273713 / 250000) : ℝ) = ((250000 / 273713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5325_neg : (24914203 / 250000000) ≤ -Real.log (226287 / 250000) ∧
    -Real.log (226287 / 250000) ≤ (99656813 / 1000000000) := by
  have h := checkLog_sound (w := (23713 / 476287)) (n := 12)
    (lo := (24914203 / 250000000)) (hi := (99656813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226287) = 1/(226287 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5325 : Bounds (-99656813 / 1000000000) (-24914203 / 250000000) (Real.log (226287 / 250000)) := by
  have h := reflection_log_5325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5326_neg : (4518809 / 500000000) ≤ -Real.log (61937693631 / 62500000000) ∧
    -Real.log (61937693631 / 62500000000) ≤ (9037619 / 1000000000) := by
  have h := checkLog_sound (w := (562306369 / 124437693631)) (n := 12)
    (lo := (4518809 / 500000000)) (hi := (9037619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61937693631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61937693631) = 1/(61937693631 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5326 : Bounds (-9037619 / 1000000000) (-4518809 / 500000000) (Real.log (61937693631 / 62500000000)) := by
  have h := reflection_log_5326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5327_neg : (4495963 / 500000000) ≤ -Real.log (991048380231 / 1000000000000) ∧
    -Real.log (991048380231 / 1000000000000) ≤ (8991927 / 1000000000) := by
  have h := checkLog_sound (w := (8951619769 / 1991048380231)) (n := 12)
    (lo := (4495963 / 500000000)) (hi := (8991927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991048380231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991048380231) = 1/(991048380231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5327 : Bounds (-8991927 / 1000000000) (-4495963 / 500000000) (Real.log (991048380231 / 1000000000000)) := by
  have h := reflection_log_5327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5328_neg : (94896839 / 500000000) ≤ -Real.log (500000000000 / 604500064613) ∧
    -Real.log (500000000000 / 604500064613) ≤ (189793679 / 1000000000) := by
  have h := checkLog_sound (w := (104500064613 / 1104500064613)) (n := 12)
    (lo := (94896839 / 500000000)) (hi := (189793679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604500064613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604500064613 / 500000000000) = 1/(500000000000 / 604500064613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5328 : Bounds (94896839 / 500000000) (189793679 / 1000000000) (Real.log (604500064613 / 500000000000)) := by
  have h := reflection_log_5328_neg
  have he : Real.log (604500064613 / 500000000000) = -Real.log (500000000000 / 604500064613) := by
    rw [show ((604500064613 / 500000000000) : ℝ) = ((500000000000 / 604500064613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5329_neg : (190276007 / 1000000000) ≤ -Real.log (500000000000 / 604791702573) ∧
    -Real.log (500000000000 / 604791702573) ≤ (23784501 / 125000000) := by
  have h := checkLog_sound (w := (104791702573 / 1104791702573)) (n := 12)
    (lo := (190276007 / 1000000000)) (hi := (23784501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604791702573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604791702573 / 500000000000) = 1/(500000000000 / 604791702573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5329 : Bounds (190276007 / 1000000000) (23784501 / 125000000) (Real.log (604791702573 / 500000000000)) := by
  have h := reflection_log_5329_neg
  have he : Real.log (604791702573 / 500000000000) = -Real.log (500000000000 / 604791702573) := by
    rw [show ((604791702573 / 500000000000) : ℝ) = ((500000000000 / 604791702573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5330_neg : (380940831 / 1000000000) ≤ -Real.log (500000000000 / 731830500123) ∧
    -Real.log (500000000000 / 731830500123) ≤ (11904401 / 31250000) := by
  have h := checkLog_sound (w := (231830500123 / 1231830500123)) (n := 12)
    (lo := (380940831 / 1000000000)) (hi := (11904401 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731830500123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731830500123 / 500000000000) = 1/(500000000000 / 731830500123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5330 : Bounds (380940831 / 1000000000) (11904401 / 31250000) (Real.log (731830500123 / 500000000000)) := by
  have h := reflection_log_5330_neg
  have he : Real.log (731830500123 / 500000000000) = -Real.log (500000000000 / 731830500123) := by
    rw [show ((731830500123 / 500000000000) : ℝ) = ((500000000000 / 731830500123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5331_neg : (381148179 / 1000000000) ≤ -Real.log (1953125000 / 2859305701) ∧
    -Real.log (1953125000 / 2859305701) ≤ (19057409 / 50000000) := by
  have h := checkLog_sound (w := (906180701 / 4812430701)) (n := 12)
    (lo := (381148179 / 1000000000)) (hi := (19057409 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2859305701 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2859305701 / 1953125000) = 1/(1953125000 / 2859305701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5331 : Bounds (381148179 / 1000000000) (19057409 / 50000000) (Real.log (2859305701 / 1953125000)) := by
  have h := reflection_log_5331_neg
  have he : Real.log (2859305701 / 1953125000) = -Real.log (1953125000 / 2859305701) := by
    rw [show ((2859305701 / 1953125000) : ℝ) = ((1953125000 / 2859305701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5332_neg : (21575983 / 125000000) ≤ -Real.log (2500 / 2971) ∧
    -Real.log (2500 / 2971) ≤ (34521573 / 200000000) := by
  have h := checkLog_sound (w := (471 / 5471)) (n := 12)
    (lo := (21575983 / 125000000)) (hi := (34521573 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2971 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2971 / 2500) = 1/(2500 / 2971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5332 : Bounds (21575983 / 125000000) (34521573 / 200000000) (Real.log (2971 / 2500)) := by
  have h := reflection_log_5332_neg
  have he : Real.log (2971 / 2500) = -Real.log (2500 / 2971) := by
    rw [show ((2971 / 2500) : ℝ) = ((2500 / 2971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5333_neg : (208747671 / 1000000000) ≤ -Real.log (2029 / 2500) ∧
    -Real.log (2029 / 2500) ≤ (26093459 / 125000000) := by
  have h := checkLog_sound (w := (471 / 4529)) (n := 12)
    (lo := (208747671 / 1000000000)) (hi := (26093459 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2029) = 1/(2029 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5333 : Bounds (-26093459 / 125000000) (-208747671 / 1000000000) (Real.log (2029 / 2500)) := by
  have h := reflection_log_5333_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5334_neg : (94191 / 500000000) ≤ -Real.log (2500000 / 2500471) ∧
    -Real.log (2500000 / 2500471) ≤ (188383 / 1000000000) := by
  have h := checkLog_sound (w := (471 / 5000471)) (n := 12)
    (lo := (94191 / 500000000)) (hi := (188383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500471 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500471 / 2500000) = 1/(2500000 / 2500471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5334 : Bounds (94191 / 500000000) (188383 / 1000000000) (Real.log (2500471 / 2500000)) := by
  have h := reflection_log_5334_neg
  have he : Real.log (2500471 / 2500000) = -Real.log (2500000 / 2500471) := by
    rw [show ((2500471 / 2500000) : ℝ) = ((2500000 / 2500471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5335_neg : (188417 / 1000000000) ≤ -Real.log (2499529 / 2500000) ∧
    -Real.log (2499529 / 2500000) ≤ (94209 / 500000000) := by
  have h := checkLog_sound (w := (471 / 4999529)) (n := 12)
    (lo := (188417 / 1000000000)) (hi := (94209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499529) = 1/(2499529 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5335 : Bounds (-94209 / 500000000) (-188417 / 1000000000) (Real.log (2499529 / 2500000)) := by
  have h := reflection_log_5335_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5336_neg : (45223733 / 500000000) ≤ -Real.log (125000 / 136833) ∧
    -Real.log (125000 / 136833) ≤ (90447467 / 1000000000) := by
  have h := checkLog_sound (w := (11833 / 261833)) (n := 12)
    (lo := (45223733 / 500000000)) (hi := (90447467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136833 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136833 / 125000) = 1/(125000 / 136833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5336 : Bounds (45223733 / 500000000) (90447467 / 1000000000) (Real.log (136833 / 125000)) := by
  have h := reflection_log_5336_neg
  have he : Real.log (136833 / 125000) = -Real.log (125000 / 136833) := by
    rw [show ((136833 / 125000) : ℝ) = ((125000 / 136833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5337_neg : (99449133 / 1000000000) ≤ -Real.log (113167 / 125000) ∧
    -Real.log (113167 / 125000) ≤ (49724567 / 500000000) := by
  have h := checkLog_sound (w := (11833 / 238167)) (n := 12)
    (lo := (99449133 / 1000000000)) (hi := (49724567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113167) = 1/(113167 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5337 : Bounds (-49724567 / 500000000) (-99449133 / 1000000000) (Real.log (113167 / 125000)) := by
  have h := reflection_log_5337_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5338_neg : (45332887 / 500000000) ≤ -Real.log (1000000 / 1094903) ∧
    -Real.log (1000000 / 1094903) ≤ (3626631 / 40000000) := by
  have h := checkLog_sound (w := (94903 / 2094903)) (n := 12)
    (lo := (45332887 / 500000000)) (hi := (3626631 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094903 / 1000000) = 1/(1000000 / 1094903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5338 : Bounds (45332887 / 500000000) (3626631 / 40000000) (Real.log (1094903 / 1000000)) := by
  have h := reflection_log_5338_neg
  have he : Real.log (1094903 / 1000000) = -Real.log (1000000 / 1094903) := by
    rw [show ((1094903 / 1000000) : ℝ) = ((1000000 / 1094903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5339_neg : (49856579 / 500000000) ≤ -Real.log (905097 / 1000000) ∧
    -Real.log (905097 / 1000000) ≤ (99713159 / 1000000000) := by
  have h := checkLog_sound (w := (94903 / 1905097)) (n := 12)
    (lo := (49856579 / 500000000)) (hi := (99713159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905097) = 1/(905097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5339 : Bounds (-99713159 / 1000000000) (-49856579 / 500000000) (Real.log (905097 / 1000000)) := by
  have h := reflection_log_5339_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5340_neg : (9047383 / 1000000000) ≤ -Real.log (990993420591 / 1000000000000) ∧
    -Real.log (990993420591 / 1000000000000) ≤ (1130923 / 125000000) := by
  have h := checkLog_sound (w := (9006579409 / 1990993420591)) (n := 12)
    (lo := (9047383 / 1000000000)) (hi := (1130923 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990993420591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990993420591) = 1/(990993420591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5340 : Bounds (-1130923 / 125000000) (-9047383 / 1000000000) (Real.log (990993420591 / 1000000000000)) := by
  have h := reflection_log_5340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5341_neg : (4500833 / 500000000) ≤ -Real.log (15484980111 / 15625000000) ∧
    -Real.log (15484980111 / 15625000000) ≤ (9001667 / 1000000000) := by
  have h := checkLog_sound (w := (140019889 / 31109980111)) (n := 12)
    (lo := (4500833 / 500000000)) (hi := (9001667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15484980111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15484980111) = 1/(15484980111 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5341 : Bounds (-9001667 / 1000000000) (-4500833 / 500000000) (Real.log (15484980111 / 15625000000)) := by
  have h := reflection_log_5341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5342_neg : (949483 / 5000000) ≤ -Real.log (250000000000 / 302281142029) ∧
    -Real.log (250000000000 / 302281142029) ≤ (189896601 / 1000000000) := by
  have h := checkLog_sound (w := (52281142029 / 552281142029)) (n := 12)
    (lo := (949483 / 5000000)) (hi := (189896601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302281142029 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302281142029 / 250000000000) = 1/(250000000000 / 302281142029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5342 : Bounds (949483 / 5000000) (189896601 / 1000000000) (Real.log (302281142029 / 250000000000)) := by
  have h := reflection_log_5342_neg
  have he : Real.log (302281142029 / 250000000000) = -Real.log (250000000000 / 302281142029) := by
    rw [show ((302281142029 / 250000000000) : ℝ) = ((250000000000 / 302281142029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5343_neg : (190378933 / 1000000000) ≤ -Real.log (1562500000 / 1890168609) ∧
    -Real.log (1562500000 / 1890168609) ≤ (95189467 / 500000000) := by
  have h := checkLog_sound (w := (327668609 / 3452668609)) (n := 12)
    (lo := (190378933 / 1000000000)) (hi := (95189467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1890168609 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1890168609 / 1562500000) = 1/(1562500000 / 1890168609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5343 : Bounds (190378933 / 1000000000) (95189467 / 500000000) (Real.log (1890168609 / 1562500000)) := by
  have h := reflection_log_5343_neg
  have he : Real.log (1890168609 / 1562500000) = -Real.log (1562500000 / 1890168609) := by
    rw [show ((1890168609 / 1562500000) : ℝ) = ((1562500000 / 1890168609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5344_neg : (381148179 / 1000000000) ≤ -Real.log (100000000000 / 146396451891) ∧
    -Real.log (100000000000 / 146396451891) ≤ (19057409 / 50000000) := by
  have h := checkLog_sound (w := (46396451891 / 246396451891)) (n := 12)
    (lo := (381148179 / 1000000000)) (hi := (19057409 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146396451891 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146396451891 / 100000000000) = 1/(100000000000 / 146396451891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5344 : Bounds (381148179 / 1000000000) (19057409 / 50000000) (Real.log (146396451891 / 100000000000)) := by
  have h := reflection_log_5344_neg
  have he : Real.log (146396451891 / 100000000000) = -Real.log (100000000000 / 146396451891) := by
    rw [show ((146396451891 / 100000000000) : ℝ) = ((100000000000 / 146396451891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5345_neg : (76271107 / 200000000) ≤ -Real.log (250000000000 / 366067028093) ∧
    -Real.log (250000000000 / 366067028093) ≤ (23834721 / 62500000) := by
  have h := checkLog_sound (w := (116067028093 / 616067028093)) (n := 12)
    (lo := (76271107 / 200000000)) (hi := (23834721 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366067028093 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366067028093 / 250000000000) = 1/(250000000000 / 366067028093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5345 : Bounds (76271107 / 200000000) (23834721 / 62500000) (Real.log (366067028093 / 250000000000)) := by
  have h := reflection_log_5345_neg
  have he : Real.log (366067028093 / 250000000000) = -Real.log (250000000000 / 366067028093) := by
    rw [show ((366067028093 / 250000000000) : ℝ) = ((250000000000 / 366067028093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5346_neg : (172692007 / 1000000000) ≤ -Real.log (2000 / 2377) ∧
    -Real.log (2000 / 2377) ≤ (21586501 / 125000000) := by
  have h := checkLog_sound (w := (377 / 4377)) (n := 12)
    (lo := (172692007 / 1000000000)) (hi := (21586501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2377 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2377 / 2000) = 1/(2000 / 2377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5346 : Bounds (172692007 / 1000000000) (21586501 / 125000000) (Real.log (2377 / 2000)) := by
  have h := reflection_log_5346_neg
  have he : Real.log (2377 / 2000) = -Real.log (2000 / 2377) := by
    rw [show ((2377 / 2000) : ℝ) = ((2000 / 2377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5347_neg : (52217723 / 250000000) ≤ -Real.log (1623 / 2000) ∧
    -Real.log (1623 / 2000) ≤ (208870893 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 3623)) (n := 12)
    (lo := (52217723 / 250000000)) (hi := (208870893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1623) = 1/(1623 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5347 : Bounds (-208870893 / 1000000000) (-52217723 / 250000000) (Real.log (1623 / 2000)) := by
  have h := reflection_log_5347_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5348_neg : (94241 / 500000000) ≤ -Real.log (2000000 / 2000377) ∧
    -Real.log (2000000 / 2000377) ≤ (188483 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 4000377)) (n := 12)
    (lo := (94241 / 500000000)) (hi := (188483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000377 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000377 / 2000000) = 1/(2000000 / 2000377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5348 : Bounds (94241 / 500000000) (188483 / 1000000000) (Real.log (2000377 / 2000000)) := by
  have h := reflection_log_5348_neg
  have he : Real.log (2000377 / 2000000) = -Real.log (2000000 / 2000377) := by
    rw [show ((2000377 / 2000000) : ℝ) = ((2000000 / 2000377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5349_neg : (188517 / 1000000000) ≤ -Real.log (1999623 / 2000000) ∧
    -Real.log (1999623 / 2000000) ≤ (94259 / 500000000) := by
  have h := checkLog_sound (w := (377 / 3999623)) (n := 12)
    (lo := (188517 / 1000000000)) (hi := (94259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999623) = 1/(1999623 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5349 : Bounds (-94259 / 500000000) (-188517 / 1000000000) (Real.log (1999623 / 2000000)) := by
  have h := reflection_log_5349_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5350_neg : (18098811 / 200000000) ≤ -Real.log (200000 / 218943) ∧
    -Real.log (200000 / 218943) ≤ (11311757 / 125000000) := by
  have h := checkLog_sound (w := (18943 / 418943)) (n := 12)
    (lo := (18098811 / 200000000)) (hi := (11311757 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218943 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218943 / 200000) = 1/(200000 / 218943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5350 : Bounds (18098811 / 200000000) (11311757 / 125000000) (Real.log (218943 / 200000)) := by
  have h := reflection_log_5350_neg
  have he : Real.log (218943 / 200000) = -Real.log (200000 / 218943) := by
    rw [show ((218943 / 200000) : ℝ) = ((200000 / 218943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5351_neg : (99505467 / 1000000000) ≤ -Real.log (181057 / 200000) ∧
    -Real.log (181057 / 200000) ≤ (24876367 / 250000000) := by
  have h := checkLog_sound (w := (18943 / 381057)) (n := 12)
    (lo := (99505467 / 1000000000)) (hi := (24876367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181057) = 1/(181057 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5351 : Bounds (-24876367 / 250000000) (-99505467 / 1000000000) (Real.log (181057 / 200000)) := by
  have h := reflection_log_5351_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5352_neg : (90712353 / 1000000000) ≤ -Real.log (500000 / 547477) ∧
    -Real.log (500000 / 547477) ≤ (45356177 / 500000000) := by
  have h := checkLog_sound (w := (47477 / 1047477)) (n := 12)
    (lo := (90712353 / 1000000000)) (hi := (45356177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547477 / 500000) = 1/(500000 / 547477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5352 : Bounds (90712353 / 1000000000) (45356177 / 500000000) (Real.log (547477 / 500000)) := by
  have h := reflection_log_5352_neg
  have he : Real.log (547477 / 500000) = -Real.log (500000 / 547477) := by
    rw [show ((547477 / 500000) : ℝ) = ((500000 / 547477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5353_neg : (99769507 / 1000000000) ≤ -Real.log (452523 / 500000) ∧
    -Real.log (452523 / 500000) ≤ (24942377 / 250000000) := by
  have h := checkLog_sound (w := (47477 / 952523)) (n := 12)
    (lo := (99769507 / 1000000000)) (hi := (24942377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452523) = 1/(452523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5353 : Bounds (-24942377 / 250000000) (-99769507 / 1000000000) (Real.log (452523 / 500000)) := by
  have h := reflection_log_5353_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5354_neg : (4528577 / 500000000) ≤ -Real.log (247745934471 / 250000000000) ∧
    -Real.log (247745934471 / 250000000000) ≤ (1811431 / 200000000) := by
  have h := checkLog_sound (w := (2254065529 / 497745934471)) (n := 12)
    (lo := (4528577 / 500000000)) (hi := (1811431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247745934471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247745934471) = 1/(247745934471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5354 : Bounds (-1811431 / 200000000) (-4528577 / 500000000) (Real.log (247745934471 / 250000000000)) := by
  have h := reflection_log_5354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5355_neg : (2252853 / 250000000) ≤ -Real.log (39641162751 / 40000000000) ∧
    -Real.log (39641162751 / 40000000000) ≤ (9011413 / 1000000000) := by
  have h := checkLog_sound (w := (358837249 / 79641162751)) (n := 12)
    (lo := (2252853 / 250000000)) (hi := (9011413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39641162751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39641162751) = 1/(39641162751 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5355 : Bounds (-9011413 / 1000000000) (-2252853 / 250000000) (Real.log (39641162751 / 40000000000)) := by
  have h := reflection_log_5355_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5356_neg : (189999523 / 1000000000) ≤ -Real.log (500000000000 / 604624510513) ∧
    -Real.log (500000000000 / 604624510513) ≤ (47499881 / 250000000) := by
  have h := checkLog_sound (w := (104624510513 / 1104624510513)) (n := 12)
    (lo := (189999523 / 1000000000)) (hi := (47499881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604624510513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604624510513 / 500000000000) = 1/(500000000000 / 604624510513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5356 : Bounds (189999523 / 1000000000) (47499881 / 250000000) (Real.log (604624510513 / 500000000000)) := by
  have h := reflection_log_5356_neg
  have he : Real.log (604624510513 / 500000000000) = -Real.log (500000000000 / 604624510513) := by
    rw [show ((604624510513 / 500000000000) : ℝ) = ((500000000000 / 604624510513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5357_neg : (190481861 / 1000000000) ≤ -Real.log (125000000000 / 151229053551) ∧
    -Real.log (125000000000 / 151229053551) ≤ (95240931 / 500000000) := by
  have h := checkLog_sound (w := (26229053551 / 276229053551)) (n := 12)
    (lo := (190481861 / 1000000000)) (hi := (95240931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151229053551 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151229053551 / 125000000000) = 1/(125000000000 / 151229053551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5357 : Bounds (190481861 / 1000000000) (95240931 / 500000000) (Real.log (151229053551 / 125000000000)) := by
  have h := reflection_log_5357_neg
  have he : Real.log (151229053551 / 125000000000) = -Real.log (125000000000 / 151229053551) := by
    rw [show ((151229053551 / 125000000000) : ℝ) = ((125000000000 / 151229053551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5358_neg : (76271107 / 200000000) ≤ -Real.log (100000000000 / 146426811237) ∧
    -Real.log (100000000000 / 146426811237) ≤ (23834721 / 62500000) := by
  have h := checkLog_sound (w := (46426811237 / 246426811237)) (n := 12)
    (lo := (76271107 / 200000000)) (hi := (23834721 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146426811237 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146426811237 / 100000000000) = 1/(100000000000 / 146426811237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5358 : Bounds (76271107 / 200000000) (23834721 / 62500000) (Real.log (146426811237 / 100000000000)) := by
  have h := reflection_log_5358_neg
  have he : Real.log (146426811237 / 100000000000) = -Real.log (100000000000 / 146426811237) := by
    rw [show ((146426811237 / 100000000000) : ℝ) = ((100000000000 / 146426811237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5359_neg : (381562899 / 1000000000) ≤ -Real.log (500000000000 / 732285890327) ∧
    -Real.log (500000000000 / 732285890327) ≤ (3815629 / 10000000) := by
  have h := checkLog_sound (w := (232285890327 / 1232285890327)) (n := 12)
    (lo := (381562899 / 1000000000)) (hi := (3815629 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732285890327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732285890327 / 500000000000) = 1/(500000000000 / 732285890327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5359 : Bounds (381562899 / 1000000000) (3815629 / 10000000) (Real.log (732285890327 / 500000000000)) := by
  have h := reflection_log_5359_neg
  have he : Real.log (732285890327 / 500000000000) = -Real.log (500000000000 / 732285890327) := by
    rw [show ((732285890327 / 500000000000) : ℝ) = ((500000000000 / 732285890327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5360_neg : (172776143 / 1000000000) ≤ -Real.log (5000 / 5943) ∧
    -Real.log (5000 / 5943) ≤ (10798509 / 62500000) := by
  have h := checkLog_sound (w := (943 / 10943)) (n := 12)
    (lo := (172776143 / 1000000000)) (hi := (10798509 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5943 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5943 / 5000) = 1/(5000 / 5943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5360 : Bounds (172776143 / 1000000000) (10798509 / 62500000) (Real.log (5943 / 5000)) := by
  have h := reflection_log_5360_neg
  have he : Real.log (5943 / 5000) = -Real.log (5000 / 5943) := by
    rw [show ((5943 / 5000) : ℝ) = ((5000 / 5943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5361_neg : (13062133 / 62500000) ≤ -Real.log (4057 / 5000) ∧
    -Real.log (4057 / 5000) ≤ (208994129 / 1000000000) := by
  have h := checkLog_sound (w := (943 / 9057)) (n := 12)
    (lo := (13062133 / 62500000)) (hi := (208994129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4057) = 1/(4057 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5361 : Bounds (-208994129 / 1000000000) (-13062133 / 62500000) (Real.log (4057 / 5000)) := by
  have h := reflection_log_5361_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5362_neg : (94291 / 500000000) ≤ -Real.log (5000000 / 5000943) ∧
    -Real.log (5000000 / 5000943) ≤ (188583 / 1000000000) := by
  have h := checkLog_sound (w := (943 / 10000943)) (n := 12)
    (lo := (94291 / 500000000)) (hi := (188583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000943 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000943 / 5000000) = 1/(5000000 / 5000943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5362 : Bounds (94291 / 500000000) (188583 / 1000000000) (Real.log (5000943 / 5000000)) := by
  have h := reflection_log_5362_neg
  have he : Real.log (5000943 / 5000000) = -Real.log (5000000 / 5000943) := by
    rw [show ((5000943 / 5000000) : ℝ) = ((5000000 / 5000943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5363_neg : (188617 / 1000000000) ≤ -Real.log (4999057 / 5000000) ∧
    -Real.log (4999057 / 5000000) ≤ (94309 / 500000000) := by
  have h := checkLog_sound (w := (943 / 9999057)) (n := 12)
    (lo := (188617 / 1000000000)) (hi := (94309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999057) = 1/(4999057 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5363 : Bounds (-94309 / 500000000) (-188617 / 1000000000) (Real.log (4999057 / 5000000)) := by
  have h := reflection_log_5363_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5364_neg : (90540641 / 1000000000) ≤ -Real.log (500000 / 547383) ∧
    -Real.log (500000 / 547383) ≤ (45270321 / 500000000) := by
  have h := checkLog_sound (w := (47383 / 1047383)) (n := 12)
    (lo := (90540641 / 1000000000)) (hi := (45270321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547383 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547383 / 500000) = 1/(500000 / 547383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5364 : Bounds (90540641 / 1000000000) (45270321 / 500000000) (Real.log (547383 / 500000)) := by
  have h := reflection_log_5364_neg
  have he : Real.log (547383 / 500000) = -Real.log (500000 / 547383) := by
    rw [show ((547383 / 500000) : ℝ) = ((500000 / 547383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5365_neg : (19912361 / 200000000) ≤ -Real.log (452617 / 500000) ∧
    -Real.log (452617 / 500000) ≤ (49780903 / 500000000) := by
  have h := checkLog_sound (w := (47383 / 952617)) (n := 12)
    (lo := (19912361 / 200000000)) (hi := (49780903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452617) = 1/(452617 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5365 : Bounds (-49780903 / 500000000) (-19912361 / 200000000) (Real.log (452617 / 500000)) := by
  have h := reflection_log_5365_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5366_neg : (90758929 / 1000000000) ≤ -Real.log (200000 / 219001) ∧
    -Real.log (200000 / 219001) ≤ (9075893 / 100000000) := by
  have h := checkLog_sound (w := (19001 / 419001)) (n := 12)
    (lo := (90758929 / 1000000000)) (hi := (9075893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219001 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219001 / 200000) = 1/(200000 / 219001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5366 : Bounds (90758929 / 1000000000) (9075893 / 100000000) (Real.log (219001 / 200000)) := by
  have h := reflection_log_5366_neg
  have he : Real.log (219001 / 200000) = -Real.log (200000 / 219001) := by
    rw [show ((219001 / 200000) : ℝ) = ((200000 / 219001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5367_neg : (4991293 / 50000000) ≤ -Real.log (180999 / 200000) ∧
    -Real.log (180999 / 200000) ≤ (99825861 / 1000000000) := by
  have h := checkLog_sound (w := (19001 / 380999)) (n := 12)
    (lo := (4991293 / 50000000)) (hi := (99825861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180999) = 1/(180999 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5367 : Bounds (-99825861 / 1000000000) (-4991293 / 50000000) (Real.log (180999 / 200000)) := by
  have h := reflection_log_5367_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5368_neg : (906693 / 100000000) ≤ -Real.log (39638961999 / 40000000000) ∧
    -Real.log (39638961999 / 40000000000) ≤ (9066931 / 1000000000) := by
  have h := checkLog_sound (w := (361038001 / 79638961999)) (n := 12)
    (lo := (906693 / 100000000)) (hi := (9066931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39638961999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39638961999) = 1/(39638961999 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5368 : Bounds (-9066931 / 1000000000) (-906693 / 100000000) (Real.log (39638961999 / 40000000000)) := by
  have h := reflection_log_5368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5369_neg : (9021163 / 1000000000) ≤ -Real.log (247754851311 / 250000000000) ∧
    -Real.log (247754851311 / 250000000000) ≤ (2255291 / 250000000) := by
  have h := checkLog_sound (w := (2245148689 / 497754851311)) (n := 12)
    (lo := (9021163 / 1000000000)) (hi := (2255291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247754851311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247754851311) = 1/(247754851311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5369 : Bounds (-2255291 / 250000000) (-9021163 / 1000000000) (Real.log (247754851311 / 250000000000)) := by
  have h := reflection_log_5369_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5370_neg : (95051223 / 500000000) ≤ -Real.log (25000000000 / 30234337199) ∧
    -Real.log (25000000000 / 30234337199) ≤ (190102447 / 1000000000) := by
  have h := checkLog_sound (w := (5234337199 / 55234337199)) (n := 12)
    (lo := (95051223 / 500000000)) (hi := (190102447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30234337199 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30234337199 / 25000000000) = 1/(25000000000 / 30234337199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5370 : Bounds (95051223 / 500000000) (190102447 / 1000000000) (Real.log (30234337199 / 25000000000)) := by
  have h := reflection_log_5370_neg
  have he : Real.log (30234337199 / 25000000000) = -Real.log (25000000000 / 30234337199) := by
    rw [show ((30234337199 / 25000000000) : ℝ) = ((25000000000 / 30234337199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5371_neg : (190584789 / 1000000000) ≤ -Real.log (100000000000 / 120995696109) ∧
    -Real.log (100000000000 / 120995696109) ≤ (19058479 / 100000000) := by
  have h := checkLog_sound (w := (20995696109 / 220995696109)) (n := 12)
    (lo := (190584789 / 1000000000)) (hi := (19058479 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120995696109 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120995696109 / 100000000000) = 1/(100000000000 / 120995696109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5371 : Bounds (190584789 / 1000000000) (19058479 / 100000000) (Real.log (120995696109 / 100000000000)) := by
  have h := reflection_log_5371_neg
  have he : Real.log (120995696109 / 100000000000) = -Real.log (100000000000 / 120995696109) := by
    rw [show ((120995696109 / 100000000000) : ℝ) = ((100000000000 / 120995696109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5372_neg : (381562899 / 1000000000) ≤ -Real.log (250000000000 / 366142945163) ∧
    -Real.log (250000000000 / 366142945163) ≤ (3815629 / 10000000) := by
  have h := checkLog_sound (w := (116142945163 / 616142945163)) (n := 12)
    (lo := (381562899 / 1000000000)) (hi := (3815629 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366142945163 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366142945163 / 250000000000) = 1/(250000000000 / 366142945163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5372 : Bounds (381562899 / 1000000000) (3815629 / 10000000) (Real.log (366142945163 / 250000000000)) := by
  have h := reflection_log_5372_neg
  have he : Real.log (366142945163 / 250000000000) = -Real.log (250000000000 / 366142945163) := by
    rw [show ((366142945163 / 250000000000) : ℝ) = ((250000000000 / 366142945163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5373_neg : (11930321 / 31250000) ≤ -Real.log (250000000000 / 366218880947) ∧
    -Real.log (250000000000 / 366218880947) ≤ (381770273 / 1000000000) := by
  have h := checkLog_sound (w := (116218880947 / 616218880947)) (n := 12)
    (lo := (11930321 / 31250000)) (hi := (381770273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366218880947 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366218880947 / 250000000000) = 1/(250000000000 / 366218880947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5373 : Bounds (11930321 / 31250000) (381770273 / 1000000000) (Real.log (366218880947 / 250000000000)) := by
  have h := reflection_log_5373_neg
  have he : Real.log (366218880947 / 250000000000) = -Real.log (250000000000 / 366218880947) := by
    rw [show ((366218880947 / 250000000000) : ℝ) = ((250000000000 / 366218880947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5374_neg : (172860273 / 1000000000) ≤ -Real.log (10000 / 11887) ∧
    -Real.log (10000 / 11887) ≤ (86430137 / 500000000) := by
  have h := checkLog_sound (w := (1887 / 21887)) (n := 12)
    (lo := (172860273 / 1000000000)) (hi := (86430137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11887 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11887 / 10000) = 1/(10000 / 11887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5374 : Bounds (172860273 / 1000000000) (86430137 / 500000000) (Real.log (11887 / 10000)) := by
  have h := reflection_log_5374_neg
  have he : Real.log (11887 / 10000) = -Real.log (10000 / 11887) := by
    rw [show ((11887 / 10000) : ℝ) = ((10000 / 11887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5375_neg : (209117379 / 1000000000) ≤ -Real.log (8113 / 10000) ∧
    -Real.log (8113 / 10000) ≤ (10455869 / 50000000) := by
  have h := checkLog_sound (w := (1887 / 18113)) (n := 12)
    (lo := (209117379 / 1000000000)) (hi := (10455869 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8113) = 1/(8113 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5375 : Bounds (-10455869 / 50000000) (-209117379 / 1000000000) (Real.log (8113 / 10000)) := by
  have h := reflection_log_5375_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


