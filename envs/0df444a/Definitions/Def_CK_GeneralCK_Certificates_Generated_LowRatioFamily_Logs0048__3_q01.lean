-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0048__3_q01
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0048__3_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:22:39.082257+00:00
-- url     : https://prove2.me/theorems/253c0b38-2d42-4c44-bf26-4a5ed46210b7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0048 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0050) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0048 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0049, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0050) (piece 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0048__3_q00

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0049 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3136_neg : (47396973 / 250000000) ≤ -Real.log (8273 / 10000) ∧
    -Real.log (8273 / 10000) ≤ (189587893 / 1000000000) := by
  have h := checkLog_sound (w := (1727 / 18273)) (n := 12)
    (lo := (47396973 / 250000000)) (hi := (189587893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8273) = 1/(8273 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3136 : Bounds (-189587893 / 1000000000) (-47396973 / 250000000) (Real.log (8273 / 10000)) := by
  have h := reflection_log_3136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3137_neg : (34537 / 200000000) ≤ -Real.log (10000000 / 10001727) ∧
    -Real.log (10000000 / 10001727) ≤ (86343 / 500000000) := by
  have h := checkLog_sound (w := (1727 / 20001727)) (n := 12)
    (lo := (34537 / 200000000)) (hi := (86343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001727 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001727 / 10000000) = 1/(10000000 / 10001727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3137 : Bounds (34537 / 200000000) (86343 / 500000000) (Real.log (10001727 / 10000000)) := by
  have h := reflection_log_3137_neg
  have he : Real.log (10001727 / 10000000) = -Real.log (10000000 / 10001727) := by
    rw [show ((10001727 / 10000000) : ℝ) = ((10000000 / 10001727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3138_neg : (86357 / 500000000) ≤ -Real.log (9998273 / 10000000) ∧
    -Real.log (9998273 / 10000000) ≤ (34543 / 200000000) := by
  have h := checkLog_sound (w := (1727 / 19998273)) (n := 12)
    (lo := (86357 / 500000000)) (hi := (34543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998273) = 1/(9998273 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3138 : Bounds (-34543 / 200000000) (-86357 / 500000000) (Real.log (9998273 / 10000000)) := by
  have h := reflection_log_3138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3139_neg : (2597753 / 31250000) ≤ -Real.log (1000000 / 1086681) ∧
    -Real.log (1000000 / 1086681) ≤ (83128097 / 1000000000) := by
  have h := checkLog_sound (w := (86681 / 2086681)) (n := 12)
    (lo := (2597753 / 31250000)) (hi := (83128097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086681 / 1000000) = 1/(1000000 / 1086681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3139 : Bounds (2597753 / 31250000) (83128097 / 1000000000) (Real.log (1086681 / 1000000)) := by
  have h := reflection_log_3139_neg
  have he : Real.log (1086681 / 1000000) = -Real.log (1000000 / 1086681) := by
    rw [show ((1086681 / 1000000) : ℝ) = ((1000000 / 1086681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3140_neg : (90670061 / 1000000000) ≤ -Real.log (913319 / 1000000) ∧
    -Real.log (913319 / 1000000) ≤ (45335031 / 500000000) := by
  have h := checkLog_sound (w := (86681 / 1913319)) (n := 12)
    (lo := (90670061 / 1000000000)) (hi := (45335031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913319) = 1/(913319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3140 : Bounds (-45335031 / 500000000) (-90670061 / 1000000000) (Real.log (913319 / 1000000)) := by
  have h := reflection_log_3140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3141_neg : (83334207 / 1000000000) ≤ -Real.log (200000 / 217381) ∧
    -Real.log (200000 / 217381) ≤ (1302097 / 15625000) := by
  have h := checkLog_sound (w := (17381 / 417381)) (n := 12)
    (lo := (83334207 / 1000000000)) (hi := (1302097 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217381 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217381 / 200000) = 1/(200000 / 217381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3141 : Bounds (83334207 / 1000000000) (1302097 / 15625000) (Real.log (217381 / 200000)) := by
  have h := reflection_log_3141_neg
  have he : Real.log (217381 / 200000) = -Real.log (200000 / 217381) := by
    rw [show ((217381 / 200000) : ℝ) = ((200000 / 217381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3142_neg : (90915351 / 1000000000) ≤ -Real.log (182619 / 200000) ∧
    -Real.log (182619 / 200000) ≤ (11364419 / 125000000) := by
  have h := checkLog_sound (w := (17381 / 382619)) (n := 12)
    (lo := (90915351 / 1000000000)) (hi := (11364419 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182619) = 1/(182619 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3142 : Bounds (-11364419 / 125000000) (-90915351 / 1000000000) (Real.log (182619 / 200000)) := by
  have h := reflection_log_3142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3143_neg : (7581143 / 1000000000) ≤ -Real.log (39697900839 / 40000000000) ∧
    -Real.log (39697900839 / 40000000000) ≤ (947643 / 125000000) := by
  have h := checkLog_sound (w := (302099161 / 79697900839)) (n := 12)
    (lo := (7581143 / 1000000000)) (hi := (947643 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39697900839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39697900839) = 1/(39697900839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3143 : Bounds (-947643 / 125000000) (-7581143 / 1000000000) (Real.log (39697900839 / 40000000000)) := by
  have h := reflection_log_3143_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3144_neg : (1508393 / 200000000) ≤ -Real.log (992486404239 / 1000000000000) ∧
    -Real.log (992486404239 / 1000000000000) ≤ (3770983 / 500000000) := by
  have h := checkLog_sound (w := (7513595761 / 1992486404239)) (n := 12)
    (lo := (1508393 / 200000000)) (hi := (3770983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992486404239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992486404239) = 1/(992486404239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3144 : Bounds (-3770983 / 500000000) (-1508393 / 200000000) (Real.log (992486404239 / 1000000000000)) := by
  have h := reflection_log_3144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3145_neg : (86899079 / 500000000) ≤ -Real.log (250000000000 / 297453846903) ∧
    -Real.log (250000000000 / 297453846903) ≤ (173798159 / 1000000000) := by
  have h := checkLog_sound (w := (47453846903 / 547453846903)) (n := 12)
    (lo := (86899079 / 500000000)) (hi := (173798159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297453846903 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297453846903 / 250000000000) = 1/(250000000000 / 297453846903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3145 : Bounds (86899079 / 500000000) (173798159 / 1000000000) (Real.log (297453846903 / 250000000000)) := by
  have h := reflection_log_3145_neg
  have he : Real.log (297453846903 / 250000000000) = -Real.log (250000000000 / 297453846903) := by
    rw [show ((297453846903 / 250000000000) : ℝ) = ((250000000000 / 297453846903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3146_neg : (174249559 / 1000000000) ≤ -Real.log (100000000000 / 119035259201) ∧
    -Real.log (100000000000 / 119035259201) ≤ (4356239 / 25000000) := by
  have h := checkLog_sound (w := (19035259201 / 219035259201)) (n := 12)
    (lo := (174249559 / 1000000000)) (hi := (4356239 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119035259201 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119035259201 / 100000000000) = 1/(100000000000 / 119035259201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3146 : Bounds (174249559 / 1000000000) (4356239 / 25000000) (Real.log (119035259201 / 100000000000)) := by
  have h := reflection_log_3146_neg
  have he : Real.log (119035259201 / 100000000000) = -Real.log (100000000000 / 119035259201) := by
    rw [show ((119035259201 / 100000000000) : ℝ) = ((100000000000 / 119035259201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3147_neg : (34869053 / 100000000) ≤ -Real.log (250000000000 / 354302634759) ∧
    -Real.log (250000000000 / 354302634759) ≤ (348690531 / 1000000000) := by
  have h := checkLog_sound (w := (104302634759 / 604302634759)) (n := 12)
    (lo := (34869053 / 100000000)) (hi := (348690531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354302634759 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354302634759 / 250000000000) = 1/(250000000000 / 354302634759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3147 : Bounds (34869053 / 100000000) (348690531 / 1000000000) (Real.log (354302634759 / 250000000000)) := by
  have h := reflection_log_3147_neg
  have he : Real.log (354302634759 / 250000000000) = -Real.log (250000000000 / 354302634759) := by
    rw [show ((354302634759 / 250000000000) : ℝ) = ((250000000000 / 354302634759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3148_neg : (13955867 / 40000000) ≤ -Real.log (250000000000 / 354375679923) ∧
    -Real.log (250000000000 / 354375679923) ≤ (87224169 / 250000000) := by
  have h := checkLog_sound (w := (104375679923 / 604375679923)) (n := 12)
    (lo := (13955867 / 40000000)) (hi := (87224169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354375679923 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354375679923 / 250000000000) = 1/(250000000000 / 354375679923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3148 : Bounds (13955867 / 40000000) (87224169 / 250000000) (Real.log (354375679923 / 250000000000)) := by
  have h := reflection_log_3148_neg
  have he : Real.log (354375679923 / 250000000000) = -Real.log (250000000000 / 354375679923) := by
    rw [show ((354375679923 / 250000000000) : ℝ) = ((250000000000 / 354375679923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3149_neg : (39848513 / 250000000) ≤ -Real.log (625 / 733) ∧
    -Real.log (625 / 733) ≤ (159394053 / 1000000000) := by
  have h := checkLog_sound (w := (54 / 679)) (n := 12)
    (lo := (39848513 / 250000000)) (hi := (159394053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733 / 625) = 1/(625 / 733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3149 : Bounds (39848513 / 250000000) (159394053 / 1000000000) (Real.log (733 / 625)) := by
  have h := reflection_log_3149_neg
  have he : Real.log (733 / 625) = -Real.log (625 / 733) := by
    rw [show ((733 / 625) : ℝ) = ((625 / 733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3150_neg : (7588351 / 40000000) ≤ -Real.log (517 / 625) ∧
    -Real.log (517 / 625) ≤ (23713597 / 125000000) := by
  have h := checkLog_sound (w := (54 / 571)) (n := 12)
    (lo := (7588351 / 40000000)) (hi := (23713597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 517) = 1/(517 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3150 : Bounds (-23713597 / 125000000) (-7588351 / 40000000) (Real.log (517 / 625)) := by
  have h := reflection_log_3150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3151_neg : (34557 / 200000000) ≤ -Real.log (156250 / 156277) ∧
    -Real.log (156250 / 156277) ≤ (86393 / 500000000) := by
  have h := checkLog_sound (w := (27 / 312527)) (n := 12)
    (lo := (34557 / 200000000)) (hi := (86393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156277 / 156250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156277 / 156250) = 1/(156250 / 156277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3151 : Bounds (34557 / 200000000) (86393 / 500000000) (Real.log (156277 / 156250)) := by
  have h := reflection_log_3151_neg
  have he : Real.log (156277 / 156250) = -Real.log (156250 / 156277) := by
    rw [show ((156277 / 156250) : ℝ) = ((156250 / 156277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3152_neg : (86407 / 500000000) ≤ -Real.log (156223 / 156250) ∧
    -Real.log (156223 / 156250) ≤ (34563 / 200000000) := by
  have h := checkLog_sound (w := (27 / 312473)) (n := 12)
    (lo := (86407 / 500000000)) (hi := (34563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250 / 156223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250 / 156223) = 1/(156223 / 156250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3152 : Bounds (-34563 / 200000000) (-86407 / 500000000) (Real.log (156223 / 156250)) := by
  have h := reflection_log_3152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3153_neg : (83175027 / 1000000000) ≤ -Real.log (250000 / 271683) ∧
    -Real.log (250000 / 271683) ≤ (20793757 / 250000000) := by
  have h := checkLog_sound (w := (21683 / 521683)) (n := 12)
    (lo := (83175027 / 1000000000)) (hi := (20793757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271683 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271683 / 250000) = 1/(250000 / 271683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3153 : Bounds (83175027 / 1000000000) (20793757 / 250000000) (Real.log (271683 / 250000)) := by
  have h := reflection_log_3153_neg
  have he : Real.log (271683 / 250000) = -Real.log (250000 / 271683) := by
    rw [show ((271683 / 250000) : ℝ) = ((250000 / 271683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3154_neg : (90725903 / 1000000000) ≤ -Real.log (228317 / 250000) ∧
    -Real.log (228317 / 250000) ≤ (5670369 / 62500000) := by
  have h := checkLog_sound (w := (21683 / 478317)) (n := 12)
    (lo := (90725903 / 1000000000)) (hi := (5670369 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228317) = 1/(228317 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3154 : Bounds (-5670369 / 62500000) (-90725903 / 1000000000) (Real.log (228317 / 250000)) := by
  have h := reflection_log_3154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3155_neg : (10422641 / 125000000) ≤ -Real.log (250000 / 271739) ∧
    -Real.log (250000 / 271739) ≤ (83381129 / 1000000000) := by
  have h := checkLog_sound (w := (21739 / 521739)) (n := 12)
    (lo := (10422641 / 125000000)) (hi := (83381129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271739 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271739 / 250000) = 1/(250000 / 271739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3155 : Bounds (10422641 / 125000000) (83381129 / 1000000000) (Real.log (271739 / 250000)) := by
  have h := reflection_log_3155_neg
  have he : Real.log (271739 / 250000) = -Real.log (250000 / 271739) := by
    rw [show ((271739 / 250000) : ℝ) = ((250000 / 271739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3156_neg : (45485603 / 500000000) ≤ -Real.log (228261 / 250000) ∧
    -Real.log (228261 / 250000) ≤ (90971207 / 1000000000) := by
  have h := checkLog_sound (w := (21739 / 478261)) (n := 12)
    (lo := (45485603 / 500000000)) (hi := (90971207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228261) = 1/(228261 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3156 : Bounds (-90971207 / 1000000000) (-45485603 / 500000000) (Real.log (228261 / 250000)) := by
  have h := reflection_log_3156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3157_neg : (7590077 / 1000000000) ≤ -Real.log (62027415879 / 62500000000) ∧
    -Real.log (62027415879 / 62500000000) ≤ (3795039 / 500000000) := by
  have h := checkLog_sound (w := (472584121 / 124527415879)) (n := 12)
    (lo := (7590077 / 1000000000)) (hi := (3795039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62027415879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62027415879) = 1/(62027415879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3157 : Bounds (-3795039 / 500000000) (-7590077 / 1000000000) (Real.log (62027415879 / 62500000000)) := by
  have h := reflection_log_3157_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3158_neg : (1887719 / 250000000) ≤ -Real.log (62029847511 / 62500000000) ∧
    -Real.log (62029847511 / 62500000000) ≤ (7550877 / 1000000000) := by
  have h := checkLog_sound (w := (470152489 / 124529847511)) (n := 12)
    (lo := (1887719 / 250000000)) (hi := (7550877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62029847511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62029847511) = 1/(62029847511 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3158 : Bounds (-7550877 / 1000000000) (-1887719 / 250000000) (Real.log (62029847511 / 62500000000)) := by
  have h := reflection_log_3158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3159_neg : (173900931 / 1000000000) ≤ -Real.log (250000000000 / 297484418593) ∧
    -Real.log (250000000000 / 297484418593) ≤ (43475233 / 250000000) := by
  have h := checkLog_sound (w := (47484418593 / 547484418593)) (n := 12)
    (lo := (173900931 / 1000000000)) (hi := (43475233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297484418593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297484418593 / 250000000000) = 1/(250000000000 / 297484418593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3159 : Bounds (173900931 / 1000000000) (43475233 / 250000000) (Real.log (297484418593 / 250000000000)) := by
  have h := reflection_log_3159_neg
  have he : Real.log (297484418593 / 250000000000) = -Real.log (250000000000 / 297484418593) := by
    rw [show ((297484418593 / 250000000000) : ℝ) = ((250000000000 / 297484418593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3160_neg : (34870467 / 200000000) ≤ -Real.log (500000000000 / 595237469389) ∧
    -Real.log (500000000000 / 595237469389) ≤ (10897021 / 62500000) := by
  have h := checkLog_sound (w := (95237469389 / 1095237469389)) (n := 12)
    (lo := (34870467 / 200000000)) (hi := (10897021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595237469389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595237469389 / 500000000000) = 1/(500000000000 / 595237469389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3160 : Bounds (34870467 / 200000000) (10897021 / 62500000) (Real.log (595237469389 / 500000000000)) := by
  have h := reflection_log_3160_neg
  have he : Real.log (595237469389 / 500000000000) = -Real.log (500000000000 / 595237469389) := by
    rw [show ((595237469389 / 500000000000) : ℝ) = ((500000000000 / 595237469389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3161_neg : (13955867 / 40000000) ≤ -Real.log (100000000000 / 141750271969) ∧
    -Real.log (100000000000 / 141750271969) ≤ (87224169 / 250000000) := by
  have h := checkLog_sound (w := (41750271969 / 241750271969)) (n := 12)
    (lo := (13955867 / 40000000)) (hi := (87224169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141750271969 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141750271969 / 100000000000) = 1/(100000000000 / 141750271969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3161 : Bounds (13955867 / 40000000) (87224169 / 250000000) (Real.log (141750271969 / 100000000000)) := by
  have h := reflection_log_3161_neg
  have he : Real.log (141750271969 / 100000000000) = -Real.log (100000000000 / 141750271969) := by
    rw [show ((141750271969 / 100000000000) : ℝ) = ((100000000000 / 141750271969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3162_neg : (349102827 / 1000000000) ≤ -Real.log (250000000000 / 354448742747) ∧
    -Real.log (250000000000 / 354448742747) ≤ (87275707 / 250000000) := by
  have h := checkLog_sound (w := (104448742747 / 604448742747)) (n := 12)
    (lo := (349102827 / 1000000000)) (hi := (87275707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354448742747 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354448742747 / 250000000000) = 1/(250000000000 / 354448742747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3162 : Bounds (349102827 / 1000000000) (87275707 / 250000000) (Real.log (354448742747 / 250000000000)) := by
  have h := reflection_log_3162_neg
  have he : Real.log (354448742747 / 250000000000) = -Real.log (250000000000 / 354448742747) := by
    rw [show ((354448742747 / 250000000000) : ℝ) = ((250000000000 / 354448742747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3163_neg : (79739657 / 500000000) ≤ -Real.log (10000 / 11729) ∧
    -Real.log (10000 / 11729) ≤ (31895863 / 200000000) := by
  have h := checkLog_sound (w := (1729 / 21729)) (n := 12)
    (lo := (79739657 / 500000000)) (hi := (31895863 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11729 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11729 / 10000) = 1/(10000 / 11729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3163 : Bounds (79739657 / 500000000) (31895863 / 200000000) (Real.log (11729 / 10000)) := by
  have h := reflection_log_3163_neg
  have he : Real.log (11729 / 10000) = -Real.log (10000 / 11729) := by
    rw [show ((11729 / 10000) : ℝ) = ((10000 / 11729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3164_neg : (23728709 / 125000000) ≤ -Real.log (8271 / 10000) ∧
    -Real.log (8271 / 10000) ≤ (189829673 / 1000000000) := by
  have h := checkLog_sound (w := (1729 / 18271)) (n := 12)
    (lo := (23728709 / 125000000)) (hi := (189829673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8271) = 1/(8271 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3164 : Bounds (-189829673 / 1000000000) (-23728709 / 125000000) (Real.log (8271 / 10000)) := by
  have h := reflection_log_3164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3165_neg : (34577 / 200000000) ≤ -Real.log (10000000 / 10001729) ∧
    -Real.log (10000000 / 10001729) ≤ (86443 / 500000000) := by
  have h := checkLog_sound (w := (1729 / 20001729)) (n := 12)
    (lo := (34577 / 200000000)) (hi := (86443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001729 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001729 / 10000000) = 1/(10000000 / 10001729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3165 : Bounds (34577 / 200000000) (86443 / 500000000) (Real.log (10001729 / 10000000)) := by
  have h := reflection_log_3165_neg
  have he : Real.log (10001729 / 10000000) = -Real.log (10000000 / 10001729) := by
    rw [show ((10001729 / 10000000) : ℝ) = ((10000000 / 10001729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3166_neg : (86457 / 500000000) ≤ -Real.log (9998271 / 10000000) ∧
    -Real.log (9998271 / 10000000) ≤ (34583 / 200000000) := by
  have h := checkLog_sound (w := (1729 / 19998271)) (n := 12)
    (lo := (86457 / 500000000)) (hi := (34583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998271) = 1/(9998271 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3166 : Bounds (-34583 / 200000000) (-86457 / 500000000) (Real.log (9998271 / 10000000)) := by
  have h := reflection_log_3166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3167_neg : (20805489 / 250000000) ≤ -Real.log (1000000 / 1086783) ∧
    -Real.log (1000000 / 1086783) ≤ (83221957 / 1000000000) := by
  have h := checkLog_sound (w := (86783 / 2086783)) (n := 12)
    (lo := (20805489 / 250000000)) (hi := (83221957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086783 / 1000000) = 1/(1000000 / 1086783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3167 : Bounds (20805489 / 250000000) (83221957 / 1000000000) (Real.log (1086783 / 1000000)) := by
  have h := reflection_log_3167_neg
  have he : Real.log (1086783 / 1000000) = -Real.log (1000000 / 1086783) := by
    rw [show ((1086783 / 1000000) : ℝ) = ((1000000 / 1086783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3168_neg : (22695437 / 250000000) ≤ -Real.log (913217 / 1000000) ∧
    -Real.log (913217 / 1000000) ≤ (90781749 / 1000000000) := by
  have h := checkLog_sound (w := (86783 / 1913217)) (n := 12)
    (lo := (22695437 / 250000000)) (hi := (90781749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913217) = 1/(913217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3168 : Bounds (-90781749 / 1000000000) (-22695437 / 250000000) (Real.log (913217 / 1000000)) := by
  have h := reflection_log_3168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3169_neg : (83428047 / 1000000000) ≤ -Real.log (1000000 / 1087007) ∧
    -Real.log (1000000 / 1087007) ≤ (5214253 / 62500000) := by
  have h := checkLog_sound (w := (87007 / 2087007)) (n := 12)
    (lo := (83428047 / 1000000000)) (hi := (5214253 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087007 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087007 / 1000000) = 1/(1000000 / 1087007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3169 : Bounds (83428047 / 1000000000) (5214253 / 62500000) (Real.log (1087007 / 1000000)) := by
  have h := reflection_log_3169_neg
  have he : Real.log (1087007 / 1000000) = -Real.log (1000000 / 1087007) := by
    rw [show ((1087007 / 1000000) : ℝ) = ((1000000 / 1087007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3170_neg : (18205413 / 200000000) ≤ -Real.log (912993 / 1000000) ∧
    -Real.log (912993 / 1000000) ≤ (45513533 / 500000000) := by
  have h := checkLog_sound (w := (87007 / 1912993)) (n := 12)
    (lo := (18205413 / 200000000)) (hi := (45513533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912993) = 1/(912993 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3170 : Bounds (-45513533 / 500000000) (-18205413 / 200000000) (Real.log (912993 / 1000000)) := by
  have h := reflection_log_3170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3171_neg : (7599017 / 1000000000) ≤ -Real.log (992429781951 / 1000000000000) ∧
    -Real.log (992429781951 / 1000000000000) ≤ (3799509 / 500000000) := by
  have h := checkLog_sound (w := (7570218049 / 1992429781951)) (n := 12)
    (lo := (7599017 / 1000000000)) (hi := (3799509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992429781951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992429781951) = 1/(992429781951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3171 : Bounds (-3799509 / 500000000) (-7599017 / 1000000000) (Real.log (992429781951 / 1000000000000)) := by
  have h := reflection_log_3171_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3172_neg : (472487 / 62500000) ≤ -Real.log (992468710911 / 1000000000000) ∧
    -Real.log (992468710911 / 1000000000000) ≤ (7559793 / 1000000000) := by
  have h := checkLog_sound (w := (7531289089 / 1992468710911)) (n := 12)
    (lo := (472487 / 62500000)) (hi := (7559793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992468710911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992468710911) = 1/(992468710911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3172 : Bounds (-7559793 / 1000000000) (-472487 / 62500000) (Real.log (992468710911 / 1000000000000)) := by
  have h := reflection_log_3172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3173_neg : (21750463 / 125000000) ≤ -Real.log (125000000000 / 148757496849) ∧
    -Real.log (125000000000 / 148757496849) ≤ (34800741 / 200000000) := by
  have h := checkLog_sound (w := (23757496849 / 273757496849)) (n := 12)
    (lo := (21750463 / 125000000)) (hi := (34800741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148757496849 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148757496849 / 125000000000) = 1/(125000000000 / 148757496849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3173 : Bounds (21750463 / 125000000) (34800741 / 200000000) (Real.log (148757496849 / 125000000000)) := by
  have h := reflection_log_3173_neg
  have he : Real.log (148757496849 / 125000000000) = -Real.log (125000000000 / 148757496849) := by
    rw [show ((148757496849 / 125000000000) : ℝ) = ((125000000000 / 148757496849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3174_neg : (174455113 / 1000000000) ≤ -Real.log (500000000000 / 595298649607) ∧
    -Real.log (500000000000 / 595298649607) ≤ (87227557 / 500000000) := by
  have h := checkLog_sound (w := (95298649607 / 1095298649607)) (n := 12)
    (lo := (174455113 / 1000000000)) (hi := (87227557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595298649607 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595298649607 / 500000000000) = 1/(500000000000 / 595298649607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3174 : Bounds (174455113 / 1000000000) (87227557 / 500000000) (Real.log (595298649607 / 500000000000)) := by
  have h := reflection_log_3174_neg
  have he : Real.log (595298649607 / 500000000000) = -Real.log (500000000000 / 595298649607) := by
    rw [show ((595298649607 / 500000000000) : ℝ) = ((500000000000 / 595298649607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3175_neg : (349102827 / 1000000000) ≤ -Real.log (500000000000 / 708897485493) ∧
    -Real.log (500000000000 / 708897485493) ≤ (87275707 / 250000000) := by
  have h := checkLog_sound (w := (208897485493 / 1208897485493)) (n := 12)
    (lo := (349102827 / 1000000000)) (hi := (87275707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708897485493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708897485493 / 500000000000) = 1/(500000000000 / 708897485493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3175 : Bounds (349102827 / 1000000000) (87275707 / 250000000) (Real.log (708897485493 / 500000000000)) := by
  have h := reflection_log_3175_neg
  have he : Real.log (708897485493 / 500000000000) = -Real.log (500000000000 / 708897485493) := by
    rw [show ((708897485493 / 500000000000) : ℝ) = ((500000000000 / 708897485493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3176_neg : (174654493 / 500000000) ≤ -Real.log (125000000000 / 177260911619) ∧
    -Real.log (125000000000 / 177260911619) ≤ (349308987 / 1000000000) := by
  have h := checkLog_sound (w := (52260911619 / 302260911619)) (n := 12)
    (lo := (174654493 / 500000000)) (hi := (349308987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177260911619 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177260911619 / 125000000000) = 1/(125000000000 / 177260911619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3176 : Bounds (174654493 / 500000000) (349308987 / 1000000000) (Real.log (177260911619 / 125000000000)) := by
  have h := reflection_log_3176_neg
  have he : Real.log (177260911619 / 125000000000) = -Real.log (125000000000 / 177260911619) := by
    rw [show ((177260911619 / 125000000000) : ℝ) = ((125000000000 / 177260911619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3177_neg : (159564569 / 1000000000) ≤ -Real.log (1000 / 1173) ∧
    -Real.log (1000 / 1173) ≤ (15956457 / 100000000) := by
  have h := checkLog_sound (w := (173 / 2173)) (n := 12)
    (lo := (159564569 / 1000000000)) (hi := (15956457 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1173 / 1000) = 1/(1000 / 1173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3177 : Bounds (159564569 / 1000000000) (15956457 / 100000000) (Real.log (1173 / 1000)) := by
  have h := reflection_log_3177_neg
  have he : Real.log (1173 / 1000) = -Real.log (1000 / 1173) := by
    rw [show ((1173 / 1000) : ℝ) = ((1000 / 1173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3178_neg : (189950583 / 1000000000) ≤ -Real.log (827 / 1000) ∧
    -Real.log (827 / 1000) ≤ (23743823 / 125000000) := by
  have h := checkLog_sound (w := (173 / 1827)) (n := 12)
    (lo := (189950583 / 1000000000)) (hi := (23743823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 827) = 1/(827 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3178 : Bounds (-23743823 / 125000000) (-189950583 / 1000000000) (Real.log (827 / 1000)) := by
  have h := reflection_log_3178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3179_neg : (34597 / 200000000) ≤ -Real.log (1000000 / 1000173) ∧
    -Real.log (1000000 / 1000173) ≤ (86493 / 500000000) := by
  have h := checkLog_sound (w := (173 / 2000173)) (n := 12)
    (lo := (34597 / 200000000)) (hi := (86493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000173 / 1000000) = 1/(1000000 / 1000173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3179 : Bounds (34597 / 200000000) (86493 / 500000000) (Real.log (1000173 / 1000000)) := by
  have h := reflection_log_3179_neg
  have he : Real.log (1000173 / 1000000) = -Real.log (1000000 / 1000173) := by
    rw [show ((1000173 / 1000000) : ℝ) = ((1000000 / 1000173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3180_neg : (86507 / 500000000) ≤ -Real.log (999827 / 1000000) ∧
    -Real.log (999827 / 1000000) ≤ (34603 / 200000000) := by
  have h := checkLog_sound (w := (173 / 1999827)) (n := 12)
    (lo := (86507 / 500000000)) (hi := (34603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999827) = 1/(999827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3180 : Bounds (-34603 / 200000000) (-86507 / 500000000) (Real.log (999827 / 1000000)) := by
  have h := reflection_log_3180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3181_neg : (41634441 / 500000000) ≤ -Real.log (500000 / 543417) ∧
    -Real.log (500000 / 543417) ≤ (83268883 / 1000000000) := by
  have h := checkLog_sound (w := (43417 / 1043417)) (n := 12)
    (lo := (41634441 / 500000000)) (hi := (83268883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543417 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543417 / 500000) = 1/(500000 / 543417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3181 : Bounds (41634441 / 500000000) (83268883 / 1000000000) (Real.log (543417 / 500000)) := by
  have h := reflection_log_3181_neg
  have he : Real.log (543417 / 500000) = -Real.log (500000 / 543417) := by
    rw [show ((543417 / 500000) : ℝ) = ((500000 / 543417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3182_neg : (22709399 / 250000000) ≤ -Real.log (456583 / 500000) ∧
    -Real.log (456583 / 500000) ≤ (90837597 / 1000000000) := by
  have h := checkLog_sound (w := (43417 / 956583)) (n := 12)
    (lo := (22709399 / 250000000)) (hi := (90837597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456583) = 1/(456583 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3182 : Bounds (-90837597 / 1000000000) (-22709399 / 250000000) (Real.log (456583 / 500000)) := by
  have h := reflection_log_3182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3183_neg : (20868741 / 250000000) ≤ -Real.log (500000 / 543529) ∧
    -Real.log (500000 / 543529) ≤ (16694993 / 200000000) := by
  have h := checkLog_sound (w := (43529 / 1043529)) (n := 12)
    (lo := (20868741 / 250000000)) (hi := (16694993 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543529 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543529 / 500000) = 1/(500000 / 543529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3183 : Bounds (20868741 / 250000000) (16694993 / 200000000) (Real.log (543529 / 500000)) := by
  have h := reflection_log_3183_neg
  have he : Real.log (543529 / 500000) = -Real.log (500000 / 543529) := by
    rw [show ((543529 / 500000) : ℝ) = ((500000 / 543529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3184_neg : (91082927 / 1000000000) ≤ -Real.log (456471 / 500000) ∧
    -Real.log (456471 / 500000) ≤ (5692683 / 62500000) := by
  have h := checkLog_sound (w := (43529 / 956471)) (n := 12)
    (lo := (91082927 / 1000000000)) (hi := (5692683 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456471) = 1/(456471 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3184 : Bounds (-5692683 / 62500000) (-91082927 / 1000000000) (Real.log (456471 / 500000)) := by
  have h := reflection_log_3184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3185_neg : (3803981 / 500000000) ≤ -Real.log (248105226159 / 250000000000) ∧
    -Real.log (248105226159 / 250000000000) ≤ (7607963 / 1000000000) := by
  have h := checkLog_sound (w := (1894773841 / 498105226159)) (n := 12)
    (lo := (3803981 / 500000000)) (hi := (7607963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248105226159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248105226159) = 1/(248105226159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3185 : Bounds (-7607963 / 1000000000) (-3803981 / 500000000) (Real.log (248105226159 / 250000000000)) := by
  have h := reflection_log_3185_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3186_neg : (3784357 / 500000000) ≤ -Real.log (248114964111 / 250000000000) ∧
    -Real.log (248114964111 / 250000000000) ≤ (1513743 / 200000000) := by
  have h := checkLog_sound (w := (1885035889 / 498114964111)) (n := 12)
    (lo := (3784357 / 500000000)) (hi := (1513743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248114964111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248114964111) = 1/(248114964111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3186 : Bounds (-1513743 / 200000000) (-3784357 / 500000000) (Real.log (248114964111 / 250000000000)) := by
  have h := reflection_log_3186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3187_neg : (174106479 / 1000000000) ≤ -Real.log (100000000000 / 119018228887) ∧
    -Real.log (100000000000 / 119018228887) ≤ (2176331 / 12500000) := by
  have h := checkLog_sound (w := (19018228887 / 219018228887)) (n := 12)
    (lo := (174106479 / 1000000000)) (hi := (2176331 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119018228887 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119018228887 / 100000000000) = 1/(100000000000 / 119018228887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3187 : Bounds (174106479 / 1000000000) (2176331 / 12500000) (Real.log (119018228887 / 100000000000)) := by
  have h := reflection_log_3187_neg
  have he : Real.log (119018228887 / 100000000000) = -Real.log (100000000000 / 119018228887) := by
    rw [show ((119018228887 / 100000000000) : ℝ) = ((100000000000 / 119018228887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3188_neg : (174557891 / 1000000000) ≤ -Real.log (25000000000 / 29767991833) ∧
    -Real.log (25000000000 / 29767991833) ≤ (43639473 / 250000000) := by
  have h := checkLog_sound (w := (4767991833 / 54767991833)) (n := 12)
    (lo := (174557891 / 1000000000)) (hi := (43639473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29767991833 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29767991833 / 25000000000) = 1/(25000000000 / 29767991833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3188 : Bounds (174557891 / 1000000000) (43639473 / 250000000) (Real.log (29767991833 / 25000000000)) := by
  have h := reflection_log_3188_neg
  have he : Real.log (29767991833 / 25000000000) = -Real.log (25000000000 / 29767991833) := by
    rw [show ((29767991833 / 25000000000) : ℝ) = ((25000000000 / 29767991833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3189_neg : (174654493 / 500000000) ≤ -Real.log (20000000000 / 28361745859) ∧
    -Real.log (20000000000 / 28361745859) ≤ (349308987 / 1000000000) := by
  have h := checkLog_sound (w := (8361745859 / 48361745859)) (n := 12)
    (lo := (174654493 / 500000000)) (hi := (349308987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28361745859 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28361745859 / 20000000000) = 1/(20000000000 / 28361745859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3189 : Bounds (174654493 / 500000000) (349308987 / 1000000000) (Real.log (28361745859 / 20000000000)) := by
  have h := reflection_log_3189_neg
  have he : Real.log (28361745859 / 20000000000) = -Real.log (20000000000 / 28361745859) := by
    rw [show ((28361745859 / 20000000000) : ℝ) = ((20000000000 / 28361745859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3190_neg : (349515153 / 1000000000) ≤ -Real.log (250000000000 / 354594921403) ∧
    -Real.log (250000000000 / 354594921403) ≤ (174757577 / 500000000) := by
  have h := checkLog_sound (w := (104594921403 / 604594921403)) (n := 12)
    (lo := (349515153 / 1000000000)) (hi := (174757577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354594921403 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354594921403 / 250000000000) = 1/(250000000000 / 354594921403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3190 : Bounds (349515153 / 1000000000) (174757577 / 500000000) (Real.log (354594921403 / 250000000000)) := by
  have h := reflection_log_3190_neg
  have he : Real.log (354594921403 / 250000000000) = -Real.log (250000000000 / 354594921403) := by
    rw [show ((354594921403 / 250000000000) : ℝ) = ((250000000000 / 354594921403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3191_neg : (159649817 / 1000000000) ≤ -Real.log (10000 / 11731) ∧
    -Real.log (10000 / 11731) ≤ (79824909 / 500000000) := by
  have h := checkLog_sound (w := (1731 / 21731)) (n := 12)
    (lo := (159649817 / 1000000000)) (hi := (79824909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11731 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11731 / 10000) = 1/(10000 / 11731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3191 : Bounds (159649817 / 1000000000) (79824909 / 500000000) (Real.log (11731 / 10000)) := by
  have h := reflection_log_3191_neg
  have he : Real.log (11731 / 10000) = -Real.log (10000 / 11731) := by
    rw [show ((11731 / 10000) : ℝ) = ((10000 / 11731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3192_neg : (19007151 / 100000000) ≤ -Real.log (8269 / 10000) ∧
    -Real.log (8269 / 10000) ≤ (190071511 / 1000000000) := by
  have h := checkLog_sound (w := (1731 / 18269)) (n := 12)
    (lo := (19007151 / 100000000)) (hi := (190071511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8269) = 1/(8269 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3192 : Bounds (-190071511 / 1000000000) (-19007151 / 100000000) (Real.log (8269 / 10000)) := by
  have h := reflection_log_3192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3193_neg : (34617 / 200000000) ≤ -Real.log (10000000 / 10001731) ∧
    -Real.log (10000000 / 10001731) ≤ (86543 / 500000000) := by
  have h := checkLog_sound (w := (1731 / 20001731)) (n := 12)
    (lo := (34617 / 200000000)) (hi := (86543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001731 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001731 / 10000000) = 1/(10000000 / 10001731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3193 : Bounds (34617 / 200000000) (86543 / 500000000) (Real.log (10001731 / 10000000)) := by
  have h := reflection_log_3193_neg
  have he : Real.log (10001731 / 10000000) = -Real.log (10000000 / 10001731) := by
    rw [show ((10001731 / 10000000) : ℝ) = ((10000000 / 10001731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3194_neg : (86557 / 500000000) ≤ -Real.log (9998269 / 10000000) ∧
    -Real.log (9998269 / 10000000) ≤ (34623 / 200000000) := by
  have h := checkLog_sound (w := (1731 / 19998269)) (n := 12)
    (lo := (86557 / 500000000)) (hi := (34623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998269) = 1/(9998269 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3194 : Bounds (-34623 / 200000000) (-86557 / 500000000) (Real.log (9998269 / 10000000)) := by
  have h := reflection_log_3194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3195_neg : (41657443 / 500000000) ≤ -Real.log (250000 / 271721) ∧
    -Real.log (250000 / 271721) ≤ (83314887 / 1000000000) := by
  have h := checkLog_sound (w := (21721 / 521721)) (n := 12)
    (lo := (41657443 / 500000000)) (hi := (83314887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271721 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271721 / 250000) = 1/(250000 / 271721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3195 : Bounds (41657443 / 500000000) (83314887 / 1000000000) (Real.log (271721 / 250000)) := by
  have h := reflection_log_3195_neg
  have he : Real.log (271721 / 250000) = -Real.log (250000 / 271721) := by
    rw [show ((271721 / 250000) : ℝ) = ((250000 / 271721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3196_neg : (1420193 / 15625000) ≤ -Real.log (228279 / 250000) ∧
    -Real.log (228279 / 250000) ≤ (90892353 / 1000000000) := by
  have h := checkLog_sound (w := (21721 / 478279)) (n := 12)
    (lo := (1420193 / 15625000)) (hi := (90892353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228279) = 1/(228279 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3196 : Bounds (-90892353 / 1000000000) (-1420193 / 15625000) (Real.log (228279 / 250000)) := by
  have h := reflection_log_3196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3197_neg : (83520959 / 1000000000) ≤ -Real.log (250000 / 271777) ∧
    -Real.log (250000 / 271777) ≤ (261003 / 3125000) := by
  have h := checkLog_sound (w := (21777 / 521777)) (n := 12)
    (lo := (83520959 / 1000000000)) (hi := (261003 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271777 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271777 / 250000) = 1/(250000 / 271777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3197 : Bounds (83520959 / 1000000000) (261003 / 3125000) (Real.log (271777 / 250000)) := by
  have h := reflection_log_3197_neg
  have he : Real.log (271777 / 250000) = -Real.log (250000 / 271777) := by
    rw [show ((271777 / 250000) : ℝ) = ((250000 / 271777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3198_neg : (2848053 / 31250000) ≤ -Real.log (228223 / 250000) ∧
    -Real.log (228223 / 250000) ≤ (91137697 / 1000000000) := by
  have h := checkLog_sound (w := (21777 / 478223)) (n := 12)
    (lo := (2848053 / 31250000)) (hi := (91137697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228223) = 1/(228223 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3198 : Bounds (-91137697 / 1000000000) (-2848053 / 31250000) (Real.log (228223 / 250000)) := by
  have h := reflection_log_3198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3199_neg : (7616737 / 1000000000) ≤ -Real.log (62025762271 / 62500000000) ∧
    -Real.log (62025762271 / 62500000000) ≤ (3808369 / 500000000) := by
  have h := checkLog_sound (w := (474237729 / 124525762271)) (n := 12)
    (lo := (7616737 / 1000000000)) (hi := (3808369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62025762271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62025762271) = 1/(62025762271 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3199 : Bounds (-3808369 / 500000000) (-7616737 / 1000000000) (Real.log (62025762271 / 62500000000)) := by
  have h := reflection_log_3199_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


