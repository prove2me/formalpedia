-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0238__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0238__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T00:09:19.093794+00:00
-- url     : https://prove2.me/theorems/918298a5-c73a-4854-8ec4-7af1e1200abc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0238 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0239, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0238 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0239, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0240)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0238 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0239, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0240)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0238 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0239, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0240) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0238 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0239, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0240).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0238 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15232_neg : (124016813 / 250000000) ≤ -Real.log (4000 / 6569) ∧
    -Real.log (4000 / 6569) ≤ (496067253 / 1000000000) := by
  have h := checkLog_sound (w := (2569 / 10569)) (n := 12)
    (lo := (124016813 / 250000000)) (hi := (496067253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6569 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6569 / 4000) = 1/(4000 / 6569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15232 : Bounds (124016813 / 250000000) (496067253 / 1000000000) (Real.log (6569 / 4000)) := by
  have h := reflection_log_15232_neg
  have he : Real.log (6569 / 4000) = -Real.log (4000 / 6569) := by
    rw [show ((6569 / 4000) : ℝ) = ((4000 / 6569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15233_neg : (1027920859 / 1000000000) ≤ -Real.log (1431 / 4000) ∧
    -Real.log (1431 / 4000) ≤ (1027920861 / 1000000000) := by
  have h := checkLog_sound (w := (569 / 3431)) (n := 12)
    (lo := (334773679 / 1000000000)) (hi := (4184671 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2000 / 1431) = 1/(1431 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15233 : Bounds (-1027920861 / 1000000000) (-1027920859 / 1000000000) (Real.log (1431 / 4000)) := by
  have h := reflection_log_15233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15234_neg : (248315477 / 500000000) ≤ -Real.log (125000 / 205397) ∧
    -Real.log (125000 / 205397) ≤ (99326191 / 200000000) := by
  have h := checkLog_sound (w := (80397 / 330397)) (n := 12)
    (lo := (248315477 / 500000000)) (hi := (99326191 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205397 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205397 / 125000) = 1/(125000 / 205397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15234 : Bounds (248315477 / 500000000) (99326191 / 200000000) (Real.log (205397 / 125000)) := by
  have h := reflection_log_15234_neg
  have he : Real.log (205397 / 125000) = -Real.log (125000 / 205397) := by
    rw [show ((205397 / 125000) : ℝ) = ((125000 / 205397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15235_neg : (206102523 / 200000000) ≤ -Real.log (44603 / 125000) ∧
    -Real.log (44603 / 125000) ≤ (1030512617 / 1000000000) := by
  have h := checkLog_sound (w := (17897 / 107103)) (n := 12)
    (lo := (67473087 / 200000000)) (hi := (84341359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44603) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 44603) = 1/(44603 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15235 : Bounds (-1030512617 / 1000000000) (-206102523 / 200000000) (Real.log (44603 / 125000)) := by
  have h := reflection_log_15235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15236_neg : (533881661 / 1000000000) ≤ -Real.log (9161322391 / 15625000000) ∧
    -Real.log (9161322391 / 15625000000) ≤ (266940831 / 500000000) := by
  have h := checkLog_sound (w := (6463677609 / 24786322391)) (n := 12)
    (lo := (533881661 / 1000000000)) (hi := (266940831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9161322391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9161322391) = 1/(9161322391 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15236 : Bounds (-266940831 / 500000000) (-533881661 / 1000000000) (Real.log (9161322391 / 15625000000)) := by
  have h := reflection_log_15236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15237_neg : (531853607 / 1000000000) ≤ -Real.log (9400239 / 16000000) ∧
    -Real.log (9400239 / 16000000) ≤ (66481701 / 125000000) := by
  have h := checkLog_sound (w := (6599761 / 25400239)) (n := 12)
    (lo := (531853607 / 1000000000)) (hi := (66481701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 9400239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 9400239) = 1/(9400239 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15237 : Bounds (-66481701 / 125000000) (-531853607 / 1000000000) (Real.log (9400239 / 16000000)) := by
  have h := reflection_log_15237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15238_neg : (95249257 / 62500000) ≤ -Real.log (250000000000 / 1147624039133) ∧
    -Real.log (250000000000 / 1147624039133) ≤ (304797623 / 200000000) := by
  have h := checkLog_sound (w := (147624039133 / 2147624039133)) (n := 12)
    (lo := (17211719 / 125000000)) (hi := (137693753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147624039133 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1147624039133 / 1000000000000) = 1/(250000000000 / 1147624039133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15238 : Bounds (95249257 / 62500000) (304797623 / 200000000) (Real.log (1147624039133 / 250000000000)) := by
  have h := reflection_log_15238_neg
  have he : Real.log (1147624039133 / 250000000000) = -Real.log (250000000000 / 1147624039133) := by
    rw [show ((1147624039133 / 250000000000) : ℝ) = ((250000000000 / 1147624039133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15239_neg : (1527143569 / 1000000000) ≤ -Real.log (125000000000 / 575625518463) ∧
    -Real.log (125000000000 / 575625518463) ≤ (381785893 / 250000000) := by
  have h := checkLog_sound (w := (75625518463 / 1075625518463)) (n := 12)
    (lo := (140849209 / 1000000000)) (hi := (14084921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575625518463 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(575625518463 / 500000000000) = 1/(125000000000 / 575625518463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15239 : Bounds (1527143569 / 1000000000) (381785893 / 250000000) (Real.log (575625518463 / 125000000000)) := by
  have h := reflection_log_15239_neg
  have he : Real.log (575625518463 / 125000000000) = -Real.log (125000000000 / 575625518463) := by
    rw [show ((575625518463 / 125000000000) : ℝ) = ((125000000000 / 575625518463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15240_neg : (26671639 / 5000000) ≤ -Real.log (250000000000 / 51833333333333) ∧
    -Real.log (250000000000 / 51833333333333) ≤ (10418609 / 1953125) := by
  have h := checkLog_sound (w := (19833333333333 / 83833333333333)) (n := 12)
    (lo := (24114877 / 50000000)) (hi := (482297541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51833333333333 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(51833333333333 / 32000000000000) = 1/(250000000000 / 51833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15240 : Bounds (26671639 / 5000000) (10418609 / 1953125) (Real.log (51833333333333 / 250000000000)) := by
  have h := reflection_log_15240_neg
  have he : Real.log (51833333333333 / 250000000000) = -Real.log (250000000000 / 51833333333333) := by
    rw [show ((51833333333333 / 250000000000) : ℝ) = ((250000000000 / 51833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15241_neg : (2677740843 / 500000000) ≤ -Real.log (100000000000 / 21176595744681) ∧
    -Real.log (100000000000 / 21176595744681) ≤ (2677740847 / 500000000) := by
  have h := checkLog_sound (w := (8376595744681 / 33976595744681)) (n := 12)
    (lo := (251725713 / 500000000)) (hi := (503451427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21176595744681 / 12800000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(21176595744681 / 12800000000000) = 1/(100000000000 / 21176595744681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15241 : Bounds (2677740843 / 500000000) (2677740847 / 500000000) (Real.log (21176595744681 / 100000000000)) := by
  have h := reflection_log_15241_neg
  have he : Real.log (21176595744681 / 100000000000) = -Real.log (100000000000 / 21176595744681) := by
    rw [show ((21176595744681 / 100000000000) : ℝ) = ((100000000000 / 21176595744681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15242_neg : (86067071 / 125000000) ≤ -Real.log (2500 / 4977) ∧
    -Real.log (2500 / 4977) ≤ (688536569 / 1000000000) := by
  have h := checkLog_sound (w := (2477 / 7477)) (n := 12)
    (lo := (86067071 / 125000000)) (hi := (688536569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4977 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4977 / 2500) = 1/(2500 / 4977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15242 : Bounds (86067071 / 125000000) (688536569 / 1000000000) (Real.log (4977 / 2500)) := by
  have h := reflection_log_15242_neg
  have he : Real.log (4977 / 2500) = -Real.log (2500 / 4977) := by
    rw [show ((4977 / 2500) : ℝ) = ((2500 / 4977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15243_neg : (4688551791 / 1000000000) ≤ -Real.log (23 / 2500) ∧
    -Real.log (23 / 2500) ≤ (2344275899 / 500000000) := by
  have h := checkLog_sound (w := (257 / 993)) (n := 12)
    (lo := (529668711 / 1000000000)) (hi := (66208589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 368) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 368) = 1/(23 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15243 : Bounds (-2344275899 / 500000000) (-4688551791 / 1000000000) (Real.log (23 / 2500)) := by
  have h := reflection_log_15243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15244_neg : (990309 / 1000000000) ≤ -Real.log (2500000 / 2502477) ∧
    -Real.log (2500000 / 2502477) ≤ (99031 / 100000000) := by
  have h := checkLog_sound (w := (2477 / 5002477)) (n := 12)
    (lo := (990309 / 1000000000)) (hi := (99031 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502477 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502477 / 2500000) = 1/(2500000 / 2502477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15244 : Bounds (990309 / 1000000000) (99031 / 100000000) (Real.log (2502477 / 2500000)) := by
  have h := reflection_log_15244_neg
  have he : Real.log (2502477 / 2500000) = -Real.log (2500000 / 2502477) := by
    rw [show ((2502477 / 2500000) : ℝ) = ((2500000 / 2502477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15245_neg : (991291 / 1000000000) ≤ -Real.log (2497523 / 2500000) ∧
    -Real.log (2497523 / 2500000) ≤ (247823 / 250000000) := by
  have h := checkLog_sound (w := (2477 / 4997523)) (n := 12)
    (lo := (991291 / 1000000000)) (hi := (247823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497523) = 1/(2497523 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15245 : Bounds (-247823 / 250000000) (-991291 / 1000000000) (Real.log (2497523 / 2500000)) := by
  have h := reflection_log_15245_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15246_neg : (496247477 / 1000000000) ≤ -Real.log (500000 / 821273) ∧
    -Real.log (500000 / 821273) ≤ (248123739 / 500000000) := by
  have h := checkLog_sound (w := (321273 / 1321273)) (n := 12)
    (lo := (496247477 / 1000000000)) (hi := (248123739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821273 / 500000) = 1/(500000 / 821273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15246 : Bounds (496247477 / 1000000000) (248123739 / 500000000) (Real.log (821273 / 500000)) := by
  have h := reflection_log_15246_neg
  have he : Real.log (821273 / 500000) = -Real.log (500000 / 821273) := by
    rw [show ((821273 / 500000) : ℝ) = ((500000 / 821273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15247_neg : (205749719 / 200000000) ≤ -Real.log (178727 / 500000) ∧
    -Real.log (178727 / 500000) ≤ (1028748597 / 1000000000) := by
  have h := checkLog_sound (w := (71273 / 428727)) (n := 12)
    (lo := (67120283 / 200000000)) (hi := (41950177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178727) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 178727) = 1/(178727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15247 : Bounds (-1028748597 / 1000000000) (-205749719 / 200000000) (Real.log (178727 / 500000)) := by
  have h := reflection_log_15247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15248_neg : (496811077 / 1000000000) ≤ -Real.log (62500 / 102717) ∧
    -Real.log (62500 / 102717) ≤ (248405539 / 500000000) := by
  have h := checkLog_sound (w := (40217 / 165217)) (n := 12)
    (lo := (496811077 / 1000000000)) (hi := (248405539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102717 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102717 / 62500) = 1/(62500 / 102717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15248 : Bounds (496811077 / 1000000000) (248405539 / 500000000) (Real.log (102717 / 62500)) := by
  have h := reflection_log_15248_neg
  have he : Real.log (102717 / 62500) = -Real.log (62500 / 102717) := by
    rw [show ((102717 / 62500) : ℝ) = ((62500 / 102717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15249_neg : (412537 / 400000) ≤ -Real.log (22283 / 62500) ∧
    -Real.log (22283 / 62500) ≤ (515671251 / 500000000) := by
  have h := checkLog_sound (w := (8967 / 53533)) (n := 12)
    (lo := (8454883 / 25000000)) (hi := (338195321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22283) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 22283) = 1/(22283 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15249 : Bounds (-515671251 / 500000000) (-412537 / 400000) (Real.log (22283 / 62500)) := by
  have h := reflection_log_15249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15250_neg : (534531423 / 1000000000) ≤ -Real.log (2288842911 / 3906250000) ∧
    -Real.log (2288842911 / 3906250000) ≤ (16704107 / 31250000) := by
  have h := checkLog_sound (w := (1617407089 / 6195092911)) (n := 12)
    (lo := (534531423 / 1000000000)) (hi := (16704107 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2288842911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2288842911) = 1/(2288842911 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15250 : Bounds (-16704107 / 31250000) (-534531423 / 1000000000) (Real.log (2288842911 / 3906250000)) := by
  have h := reflection_log_15250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15251_neg : (532501119 / 1000000000) ≤ -Real.log (146783659471 / 250000000000) ∧
    -Real.log (146783659471 / 250000000000) ≤ (832033 / 1562500) := by
  have h := checkLog_sound (w := (103216340529 / 396783659471)) (n := 12)
    (lo := (532501119 / 1000000000)) (hi := (832033 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 146783659471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 146783659471) = 1/(146783659471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15251 : Bounds (-832033 / 1562500) (-532501119 / 1000000000) (Real.log (146783659471 / 250000000000)) := by
  have h := reflection_log_15251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15252_neg : (190624509 / 125000000) ≤ -Real.log (12500000000 / 57439069083) ∧
    -Real.log (12500000000 / 57439069083) ≤ (60999843 / 40000000) := by
  have h := checkLog_sound (w := (7439069083 / 107439069083)) (n := 12)
    (lo := (8668857 / 62500000)) (hi := (138701713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57439069083 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(57439069083 / 50000000000) = 1/(12500000000 / 57439069083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15252 : Bounds (190624509 / 125000000) (60999843 / 40000000) (Real.log (57439069083 / 12500000000)) := by
  have h := reflection_log_15252_neg
  have he : Real.log (57439069083 / 12500000000) = -Real.log (12500000000 / 57439069083) := by
    rw [show ((57439069083 / 12500000000) : ℝ) = ((12500000000 / 57439069083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15253_neg : (191019197 / 125000000) ≤ -Real.log (500000000000 / 2304828793251) ∧
    -Real.log (500000000000 / 2304828793251) ≤ (1528153579 / 1000000000) := by
  have h := checkLog_sound (w := (304828793251 / 4304828793251)) (n := 12)
    (lo := (8866201 / 62500000)) (hi := (141859217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2304828793251 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2304828793251 / 2000000000000) = 1/(500000000000 / 2304828793251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15253 : Bounds (191019197 / 125000000) (1528153579 / 1000000000) (Real.log (2304828793251 / 500000000000)) := by
  have h := reflection_log_15253_neg
  have he : Real.log (2304828793251 / 500000000000) = -Real.log (500000000000 / 2304828793251) := by
    rw [show ((2304828793251 / 500000000000) : ℝ) = ((500000000000 / 2304828793251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15254_neg : (2677740843 / 500000000) ≤ -Real.log (125000000000 / 26470744680851) ∧
    -Real.log (125000000000 / 26470744680851) ≤ (2677740847 / 500000000) := by
  have h := checkLog_sound (w := (10470744680851 / 42470744680851)) (n := 12)
    (lo := (251725713 / 500000000)) (hi := (503451427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26470744680851 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(26470744680851 / 16000000000000) = 1/(125000000000 / 26470744680851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15254 : Bounds (2677740843 / 500000000) (2677740847 / 500000000) (Real.log (26470744680851 / 125000000000)) := by
  have h := reflection_log_15254_neg
  have he : Real.log (26470744680851 / 125000000000) = -Real.log (125000000000 / 26470744680851) := by
    rw [show ((26470744680851 / 125000000000) : ℝ) = ((125000000000 / 26470744680851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15255_neg : (5377088359 / 1000000000) ≤ -Real.log (250000000000 / 54097826086957) ∧
    -Real.log (250000000000 / 54097826086957) ≤ (5377088367 / 1000000000) := by
  have h := checkLog_sound (w := (22097826086957 / 86097826086957)) (n := 12)
    (lo := (525058099 / 1000000000)) (hi := (5250581 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54097826086957 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(54097826086957 / 32000000000000) = 1/(250000000000 / 54097826086957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15255 : Bounds (5377088359 / 1000000000) (5377088367 / 1000000000) (Real.log (54097826086957 / 250000000000)) := by
  have h := reflection_log_15255_neg
  have he : Real.log (54097826086957 / 250000000000) = -Real.log (250000000000 / 54097826086957) := by
    rw [show ((54097826086957 / 250000000000) : ℝ) = ((250000000000 / 54097826086957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15256_neg : (27545481 / 40000000) ≤ -Real.log (1000 / 1991) ∧
    -Real.log (1000 / 1991) ≤ (344318513 / 500000000) := by
  have h := checkLog_sound (w := (991 / 2991)) (n := 12)
    (lo := (27545481 / 40000000)) (hi := (344318513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1991 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1991 / 1000) = 1/(1000 / 1991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15256 : Bounds (27545481 / 40000000) (344318513 / 500000000) (Real.log (1991 / 1000)) := by
  have h := reflection_log_15256_neg
  have he : Real.log (1991 / 1000) = -Real.log (1000 / 1991) := by
    rw [show ((1991 / 1000) : ℝ) = ((1000 / 1991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15257_neg : (2355265349 / 500000000) ≤ -Real.log (9 / 1000) ∧
    -Real.log (9 / 1000) ≤ (942106141 / 200000000) := by
  have h := checkLog_sound (w := (53 / 197)) (n := 12)
    (lo := (275823809 / 500000000)) (hi := (551647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 72) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 72) = 1/(9 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15257 : Bounds (-942106141 / 200000000) (-2355265349 / 500000000) (Real.log (9 / 1000)) := by
  have h := reflection_log_15257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15258_neg : (990509 / 1000000000) ≤ -Real.log (1000000 / 1000991) ∧
    -Real.log (1000000 / 1000991) ≤ (99051 / 100000000) := by
  have h := checkLog_sound (w := (991 / 2000991)) (n := 12)
    (lo := (990509 / 1000000000)) (hi := (99051 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000991 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000991 / 1000000) = 1/(1000000 / 1000991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15258 : Bounds (990509 / 1000000000) (99051 / 100000000) (Real.log (1000991 / 1000000)) := by
  have h := reflection_log_15258_neg
  have he : Real.log (1000991 / 1000000) = -Real.log (1000000 / 1000991) := by
    rw [show ((1000991 / 1000000) : ℝ) = ((1000000 / 1000991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15259_neg : (991491 / 1000000000) ≤ -Real.log (999009 / 1000000) ∧
    -Real.log (999009 / 1000000) ≤ (247873 / 250000000) := by
  have h := checkLog_sound (w := (991 / 1999009)) (n := 12)
    (lo := (991491 / 1000000000)) (hi := (247873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999009) = 1/(999009 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15259 : Bounds (-247873 / 250000000) (-991491 / 1000000000) (Real.log (999009 / 1000000)) := by
  have h := reflection_log_15259_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15260_neg : (496428277 / 1000000000) ≤ -Real.log (1000000 / 1642843) ∧
    -Real.log (1000000 / 1642843) ≤ (248214139 / 500000000) := by
  have h := checkLog_sound (w := (642843 / 2642843)) (n := 12)
    (lo := (496428277 / 1000000000)) (hi := (248214139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1642843 / 1000000) = 1/(1000000 / 1642843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15260 : Bounds (496428277 / 1000000000) (248214139 / 500000000) (Real.log (1642843 / 1000000)) := by
  have h := reflection_log_15260_neg
  have he : Real.log (1642843 / 1000000) = -Real.log (1000000 / 1642843) := by
    rw [show ((1642843 / 1000000) : ℝ) = ((1000000 / 1642843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15261_neg : (1029579817 / 1000000000) ≤ -Real.log (357157 / 1000000) ∧
    -Real.log (357157 / 1000000) ≤ (1029579819 / 1000000000) := by
  have h := checkLog_sound (w := (142843 / 857157)) (n := 12)
    (lo := (336432637 / 1000000000)) (hi := (168216319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 357157) = 1/(357157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15261 : Bounds (-1029579819 / 1000000000) (-1029579817 / 1000000000) (Real.log (357157 / 1000000)) := by
  have h := reflection_log_15261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15262_neg : (3882753 / 7812500) ≤ -Real.log (100000 / 164377) ∧
    -Real.log (100000 / 164377) ≤ (99398477 / 200000000) := by
  have h := checkLog_sound (w := (64377 / 264377)) (n := 12)
    (lo := (3882753 / 7812500)) (hi := (99398477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164377 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164377 / 100000) = 1/(100000 / 164377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15262 : Bounds (3882753 / 7812500) (99398477 / 200000000) (Real.log (164377 / 100000)) := by
  have h := reflection_log_15262_neg
  have he : Real.log (164377 / 100000) = -Real.log (100000 / 164377) := by
    rw [show ((164377 / 100000) : ℝ) = ((100000 / 164377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15263_neg : (2015974 / 1953125) ≤ -Real.log (35623 / 100000) ∧
    -Real.log (35623 / 100000) ≤ (103217869 / 100000000) := by
  have h := checkLog_sound (w := (14377 / 85623)) (n := 12)
    (lo := (84757877 / 250000000)) (hi := (339031509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35623) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35623) = 1/(35623 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15263 : Bounds (-103217869 / 100000000) (-2015974 / 1953125) (Real.log (35623 / 100000)) := by
  have h := reflection_log_15263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15264_neg : (107037261 / 200000000) ≤ -Real.log (5855601871 / 10000000000) ∧
    -Real.log (5855601871 / 10000000000) ≤ (267593153 / 500000000) := by
  have h := checkLog_sound (w := (4144398129 / 15855601871)) (n := 12)
    (lo := (107037261 / 200000000)) (hi := (267593153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5855601871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5855601871) = 1/(5855601871 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15264 : Bounds (-267593153 / 500000000) (-107037261 / 200000000) (Real.log (5855601871 / 10000000000)) := by
  have h := reflection_log_15264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15265_neg : (26657577 / 50000000) ≤ -Real.log (586752877351 / 1000000000000) ∧
    -Real.log (586752877351 / 1000000000000) ≤ (533151541 / 1000000000) := by
  have h := checkLog_sound (w := (413247122649 / 1586752877351)) (n := 12)
    (lo := (26657577 / 50000000)) (hi := (533151541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 586752877351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 586752877351) = 1/(586752877351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15265 : Bounds (-533151541 / 1000000000) (-26657577 / 50000000) (Real.log (586752877351 / 1000000000000)) := by
  have h := reflection_log_15265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15266_neg : (763004047 / 500000000) ≤ -Real.log (50000000000 / 229988912439) ∧
    -Real.log (50000000000 / 229988912439) ≤ (1526008097 / 1000000000) := by
  have h := checkLog_sound (w := (29988912439 / 429988912439)) (n := 12)
    (lo := (69856867 / 500000000)) (hi := (27942747 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229988912439 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(229988912439 / 200000000000) = 1/(50000000000 / 229988912439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15266 : Bounds (763004047 / 500000000) (1526008097 / 1000000000) (Real.log (229988912439 / 50000000000)) := by
  have h := reflection_log_15266_neg
  have he : Real.log (229988912439 / 50000000000) = -Real.log (50000000000 / 229988912439) := by
    rw [show ((229988912439 / 50000000000) : ℝ) = ((50000000000 / 229988912439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15267_neg : (11946649 / 7812500) ≤ -Real.log (500000000000 / 2307175139657) ∧
    -Real.log (500000000000 / 2307175139657) ≤ (61166843 / 40000000) := by
  have h := checkLog_sound (w := (307175139657 / 4307175139657)) (n := 12)
    (lo := (17859589 / 125000000)) (hi := (142876713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2307175139657 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2307175139657 / 2000000000000) = 1/(500000000000 / 2307175139657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15267 : Bounds (11946649 / 7812500) (61166843 / 40000000) (Real.log (2307175139657 / 500000000000)) := by
  have h := reflection_log_15267_neg
  have he : Real.log (2307175139657 / 500000000000) = -Real.log (500000000000 / 2307175139657) := by
    rw [show ((2307175139657 / 500000000000) : ℝ) = ((500000000000 / 2307175139657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15268_neg : (5377088359 / 1000000000) ≤ -Real.log (500000000000 / 108195652173913) ∧
    -Real.log (500000000000 / 108195652173913) ≤ (5377088367 / 1000000000) := by
  have h := checkLog_sound (w := (44195652173913 / 172195652173913)) (n := 12)
    (lo := (525058099 / 1000000000)) (hi := (5250581 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108195652173913 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(108195652173913 / 64000000000000) = 1/(500000000000 / 108195652173913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15268 : Bounds (5377088359 / 1000000000) (5377088367 / 1000000000) (Real.log (108195652173913 / 500000000000)) := by
  have h := reflection_log_15268_neg
  have he : Real.log (108195652173913 / 500000000000) = -Real.log (500000000000 / 108195652173913) := by
    rw [show ((108195652173913 / 500000000000) : ℝ) = ((500000000000 / 108195652173913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15269_neg : (2699583861 / 500000000) ≤ -Real.log (62500000000 / 13826388888889) ∧
    -Real.log (62500000000 / 13826388888889) ≤ (539916773 / 100000000) := by
  have h := checkLog_sound (w := (5826388888889 / 21826388888889)) (n := 12)
    (lo := (273568731 / 500000000)) (hi := (547137463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13826388888889 / 8000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(13826388888889 / 8000000000000) = 1/(62500000000 / 13826388888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15269 : Bounds (2699583861 / 500000000) (539916773 / 100000000) (Real.log (13826388888889 / 62500000000)) := by
  have h := reflection_log_15269_neg
  have he : Real.log (13826388888889 / 62500000000) = -Real.log (62500000000 / 13826388888889) := by
    rw [show ((13826388888889 / 62500000000) : ℝ) = ((62500000000 / 13826388888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15270_neg : (10761523 / 15625000) ≤ -Real.log (1250 / 2489) ∧
    -Real.log (1250 / 2489) ≤ (688737473 / 1000000000) := by
  have h := checkLog_sound (w := (1239 / 3739)) (n := 12)
    (lo := (10761523 / 15625000)) (hi := (688737473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2489 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2489 / 1250) = 1/(1250 / 2489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15270 : Bounds (10761523 / 15625000) (688737473 / 1000000000) (Real.log (2489 / 1250)) := by
  have h := reflection_log_15270_neg
  have he : Real.log (2489 / 1250) = -Real.log (1250 / 2489) := by
    rw [show ((2489 / 1250) : ℝ) = ((1250 / 2489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15271_neg : (2366501777 / 500000000) ≤ -Real.log (11 / 1250) ∧
    -Real.log (11 / 1250) ≤ (4733003561 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 977)) (n := 12)
    (lo := (287060237 / 500000000)) (hi := (22964819 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 352) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 352) = 1/(11 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15271 : Bounds (-4733003561 / 1000000000) (-2366501777 / 500000000) (Real.log (11 / 1250)) := by
  have h := reflection_log_15271_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15272_neg : (990709 / 1000000000) ≤ -Real.log (1250000 / 1251239) ∧
    -Real.log (1250000 / 1251239) ≤ (99071 / 100000000) := by
  have h := checkLog_sound (w := (1239 / 2501239)) (n := 12)
    (lo := (990709 / 1000000000)) (hi := (99071 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251239 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251239 / 1250000) = 1/(1250000 / 1251239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15272 : Bounds (990709 / 1000000000) (99071 / 100000000) (Real.log (1251239 / 1250000)) := by
  have h := reflection_log_15272_neg
  have he : Real.log (1251239 / 1250000) = -Real.log (1250000 / 1251239) := by
    rw [show ((1251239 / 1250000) : ℝ) = ((1250000 / 1251239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15273_neg : (991691 / 1000000000) ≤ -Real.log (1248761 / 1250000) ∧
    -Real.log (1248761 / 1250000) ≤ (247923 / 250000000) := by
  have h := checkLog_sound (w := (1239 / 2498761)) (n := 12)
    (lo := (991691 / 1000000000)) (hi := (247923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1248761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1248761) = 1/(1248761 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15273 : Bounds (-247923 / 250000000) (-991691 / 1000000000) (Real.log (1248761 / 1250000)) := by
  have h := reflection_log_15273_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15274_neg : (99321809 / 200000000) ≤ -Real.log (50000 / 82157) ∧
    -Real.log (50000 / 82157) ≤ (248304523 / 500000000) := by
  have h := checkLog_sound (w := (32157 / 132157)) (n := 12)
    (lo := (99321809 / 200000000)) (hi := (248304523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82157 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82157 / 50000) = 1/(50000 / 82157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15274 : Bounds (99321809 / 200000000) (248304523 / 500000000) (Real.log (82157 / 50000)) := by
  have h := reflection_log_15274_neg
  have he : Real.log (82157 / 50000) = -Real.log (50000 / 82157) := by
    rw [show ((82157 / 50000) : ℝ) = ((50000 / 82157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15275_neg : (103041173 / 100000000) ≤ -Real.log (17843 / 50000) ∧
    -Real.log (17843 / 50000) ≤ (257602933 / 250000000) := by
  have h := checkLog_sound (w := (7157 / 42843)) (n := 12)
    (lo := (6745291 / 20000000)) (hi := (337264551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17843) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 17843) = 1/(17843 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15275 : Bounds (-257602933 / 250000000) (-103041173 / 100000000) (Real.log (17843 / 50000)) := by
  have h := reflection_log_15275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15276_neg : (248586829 / 500000000) ≤ -Real.log (250000 / 411017) ∧
    -Real.log (250000 / 411017) ≤ (497173659 / 1000000000) := by
  have h := checkLog_sound (w := (161017 / 661017)) (n := 12)
    (lo := (248586829 / 500000000)) (hi := (497173659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411017 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411017 / 250000) = 1/(250000 / 411017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15276 : Bounds (248586829 / 500000000) (497173659 / 1000000000) (Real.log (411017 / 250000)) := by
  have h := reflection_log_15276_neg
  have he : Real.log (411017 / 250000) = -Real.log (250000 / 411017) := by
    rw [show ((411017 / 250000) : ℝ) = ((250000 / 411017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15277_neg : (1033015577 / 1000000000) ≤ -Real.log (88983 / 250000) ∧
    -Real.log (88983 / 250000) ≤ (1033015579 / 1000000000) := by
  have h := checkLog_sound (w := (36017 / 213983)) (n := 12)
    (lo := (339868397 / 1000000000)) (hi := (169934199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88983) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 88983) = 1/(88983 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15277 : Bounds (-1033015579 / 1000000000) (-1033015577 / 1000000000) (Real.log (88983 / 250000)) := by
  have h := reflection_log_15277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15278_neg : (535841919 / 1000000000) ≤ -Real.log (36573525711 / 62500000000) ∧
    -Real.log (36573525711 / 62500000000) ≤ (837253 / 1562500) := by
  have h := checkLog_sound (w := (25926474289 / 99073525711)) (n := 12)
    (lo := (535841919 / 1000000000)) (hi := (837253 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36573525711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36573525711) = 1/(36573525711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15278 : Bounds (-837253 / 1562500) (-535841919 / 1000000000) (Real.log (36573525711 / 62500000000)) := by
  have h := reflection_log_15278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15279_neg : (106760537 / 200000000) ≤ -Real.log (1465927351 / 2500000000) ∧
    -Real.log (1465927351 / 2500000000) ≤ (266901343 / 500000000) := by
  have h := checkLog_sound (w := (1034072649 / 3965927351)) (n := 12)
    (lo := (106760537 / 200000000)) (hi := (266901343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1465927351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1465927351) = 1/(1465927351 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15279 : Bounds (-266901343 / 500000000) (-106760537 / 200000000) (Real.log (1465927351 / 2500000000)) := by
  have h := reflection_log_15279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15280_neg : (61080831 / 40000000) ≤ -Real.log (500000000000 / 2302219357731) ∧
    -Real.log (500000000000 / 2302219357731) ≤ (763510389 / 500000000) := by
  have h := checkLog_sound (w := (302219357731 / 4302219357731)) (n := 12)
    (lo := (28145283 / 200000000)) (hi := (8795401 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2302219357731 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2302219357731 / 2000000000000) = 1/(500000000000 / 2302219357731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15280 : Bounds (61080831 / 40000000) (763510389 / 500000000) (Real.log (2302219357731 / 500000000000)) := by
  have h := reflection_log_15280_neg
  have he : Real.log (2302219357731 / 500000000000) = -Real.log (500000000000 / 2302219357731) := by
    rw [show ((2302219357731 / 500000000000) : ℝ) = ((500000000000 / 2302219357731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15281_neg : (765094617 / 500000000) ≤ -Real.log (500000000000 / 2309525414967) ∧
    -Real.log (500000000000 / 2309525414967) ≤ (1530189237 / 1000000000) := by
  have h := checkLog_sound (w := (309525414967 / 4309525414967)) (n := 12)
    (lo := (71947437 / 500000000)) (hi := (1151159 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2309525414967 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2309525414967 / 2000000000000) = 1/(500000000000 / 2309525414967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15281 : Bounds (765094617 / 500000000) (1530189237 / 1000000000) (Real.log (2309525414967 / 500000000000)) := by
  have h := reflection_log_15281_neg
  have he : Real.log (2309525414967 / 500000000000) = -Real.log (500000000000 / 2309525414967) := by
    rw [show ((2309525414967 / 500000000000) : ℝ) = ((500000000000 / 2309525414967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15282_neg : (2699583861 / 500000000) ≤ -Real.log (500000000000 / 110611111111111) ∧
    -Real.log (500000000000 / 110611111111111) ≤ (539916773 / 100000000) := by
  have h := checkLog_sound (w := (46611111111111 / 174611111111111)) (n := 12)
    (lo := (273568731 / 500000000)) (hi := (547137463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110611111111111 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(110611111111111 / 64000000000000) = 1/(500000000000 / 110611111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15282 : Bounds (2699583861 / 500000000) (539916773 / 100000000) (Real.log (110611111111111 / 500000000000)) := by
  have h := reflection_log_15282_neg
  have he : Real.log (110611111111111 / 500000000000) = -Real.log (500000000000 / 110611111111111) := by
    rw [show ((110611111111111 / 500000000000) : ℝ) = ((500000000000 / 110611111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15283_neg : (216869641 / 40000000) ≤ -Real.log (125000000000 / 28284090909091) ∧
    -Real.log (125000000000 / 28284090909091) ≤ (5421741033 / 1000000000) := by
  have h := checkLog_sound (w := (12284090909091 / 44284090909091)) (n := 12)
    (lo := (113942153 / 200000000)) (hi := (284855383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28284090909091 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(28284090909091 / 16000000000000) = 1/(125000000000 / 28284090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15283 : Bounds (216869641 / 40000000) (5421741033 / 1000000000) (Real.log (28284090909091 / 125000000000)) := by
  have h := reflection_log_15283_neg
  have he : Real.log (28284090909091 / 125000000000) = -Real.log (125000000000 / 28284090909091) := by
    rw [show ((28284090909091 / 125000000000) : ℝ) = ((125000000000 / 28284090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15284_neg : (172209477 / 250000000) ≤ -Real.log (5000 / 9957) ∧
    -Real.log (5000 / 9957) ≤ (688837909 / 1000000000) := by
  have h := checkLog_sound (w := (4957 / 14957)) (n := 12)
    (lo := (172209477 / 250000000)) (hi := (688837909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9957 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9957 / 5000) = 1/(5000 / 9957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15284 : Bounds (172209477 / 250000000) (688837909 / 1000000000) (Real.log (9957 / 5000)) := by
  have h := reflection_log_15284_neg
  have he : Real.log (9957 / 5000) = -Real.log (5000 / 9957) := by
    rw [show ((9957 / 5000) : ℝ) = ((5000 / 9957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15285_neg : (297249567 / 62500000) ≤ -Real.log (43 / 5000) ∧
    -Real.log (43 / 5000) ≤ (4755993079 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 969)) (n := 12)
    (lo := (74638749 / 125000000)) (hi := (597109993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 344) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 344) = 1/(43 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15285 : Bounds (-4755993079 / 1000000000) (-297249567 / 62500000) (Real.log (43 / 5000)) := by
  have h := reflection_log_15285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15286_neg : (247727 / 250000000) ≤ -Real.log (5000000 / 5004957) ∧
    -Real.log (5000000 / 5004957) ≤ (990909 / 1000000000) := by
  have h := checkLog_sound (w := (4957 / 10004957)) (n := 12)
    (lo := (247727 / 250000000)) (hi := (990909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004957 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004957 / 5000000) = 1/(5000000 / 5004957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15286 : Bounds (247727 / 250000000) (990909 / 1000000000) (Real.log (5004957 / 5000000)) := by
  have h := reflection_log_15286_neg
  have he : Real.log (5004957 / 5000000) = -Real.log (5000000 / 5004957) := by
    rw [show ((5004957 / 5000000) : ℝ) = ((5000000 / 5004957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15287_neg : (991891 / 1000000000) ≤ -Real.log (4995043 / 5000000) ∧
    -Real.log (4995043 / 5000000) ≤ (247973 / 250000000) := by
  have h := checkLog_sound (w := (4957 / 9995043)) (n := 12)
    (lo := (991891 / 1000000000)) (hi := (247973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995043) = 1/(4995043 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15287 : Bounds (-247973 / 250000000) (-991891 / 1000000000) (Real.log (4995043 / 5000000)) := by
  have h := reflection_log_15287_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15288_neg : (496790997 / 1000000000) ≤ -Real.log (1000000 / 1643439) ∧
    -Real.log (1000000 / 1643439) ≤ (248395499 / 500000000) := by
  have h := checkLog_sound (w := (643439 / 2643439)) (n := 12)
    (lo := (496790997 / 1000000000)) (hi := (248395499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1643439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1643439 / 1000000) = 1/(1000000 / 1643439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15288 : Bounds (496790997 / 1000000000) (248395499 / 500000000) (Real.log (1643439 / 1000000)) := by
  have h := reflection_log_15288_neg
  have he : Real.log (1643439 / 1000000) = -Real.log (1000000 / 1643439) := by
    rw [show ((1643439 / 1000000) : ℝ) = ((1000000 / 1643439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15289_neg : (206249989 / 200000000) ≤ -Real.log (356561 / 1000000) ∧
    -Real.log (356561 / 1000000) ≤ (1031249947 / 1000000000) := by
  have h := checkLog_sound (w := (143439 / 856561)) (n := 12)
    (lo := (67620553 / 200000000)) (hi := (169051383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 356561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 356561) = 1/(356561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15289 : Bounds (-1031249947 / 1000000000) (-206249989 / 200000000) (Real.log (356561 / 1000000)) := by
  have h := reflection_log_15289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15290_neg : (99471223 / 200000000) ≤ -Real.log (62500 / 102773) ∧
    -Real.log (62500 / 102773) ≤ (124339029 / 250000000) := by
  have h := checkLog_sound (w := (40273 / 165273)) (n := 12)
    (lo := (99471223 / 200000000)) (hi := (124339029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102773 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102773 / 62500) = 1/(62500 / 102773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15290 : Bounds (99471223 / 200000000) (124339029 / 250000000) (Real.log (102773 / 62500)) := by
  have h := reflection_log_15290_neg
  have he : Real.log (102773 / 62500) = -Real.log (62500 / 102773) := by
    rw [show ((102773 / 62500) : ℝ) = ((62500 / 102773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15291_neg : (103385879 / 100000000) ≤ -Real.log (22227 / 62500) ∧
    -Real.log (22227 / 62500) ≤ (129232349 / 125000000) := by
  have h := checkLog_sound (w := (9023 / 53477)) (n := 12)
    (lo := (34071161 / 100000000)) (hi := (340711611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 22227) = 1/(22227 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15291 : Bounds (-129232349 / 125000000) (-103385879 / 100000000) (Real.log (22227 / 62500)) := by
  have h := reflection_log_15291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15292_neg : (268251337 / 500000000) ≤ -Real.log (2284335471 / 3906250000) ∧
    -Real.log (2284335471 / 3906250000) ≤ (21460107 / 40000000) := by
  have h := checkLog_sound (w := (1621914529 / 6190585471)) (n := 12)
    (lo := (268251337 / 500000000)) (hi := (21460107 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2284335471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2284335471) = 1/(2284335471 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15292 : Bounds (-21460107 / 40000000) (-268251337 / 500000000) (Real.log (2284335471 / 3906250000)) := by
  have h := reflection_log_15292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15293_neg : (133614737 / 250000000) ≤ -Real.log (585986253279 / 1000000000000) ∧
    -Real.log (585986253279 / 1000000000000) ≤ (534458949 / 1000000000) := by
  have h := checkLog_sound (w := (414013746721 / 1585986253279)) (n := 12)
    (lo := (133614737 / 250000000)) (hi := (534458949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 585986253279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 585986253279) = 1/(585986253279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15293 : Bounds (-534458949 / 1000000000) (-133614737 / 250000000) (Real.log (585986253279 / 1000000000000)) := by
  have h := reflection_log_15293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15294_neg : (764020471 / 500000000) ≤ -Real.log (500000000000 / 2304569204147) ∧
    -Real.log (500000000000 / 2304569204147) ≤ (305608189 / 200000000) := by
  have h := checkLog_sound (w := (304569204147 / 4304569204147)) (n := 12)
    (lo := (70873291 / 500000000)) (hi := (141746583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2304569204147 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2304569204147 / 2000000000000) = 1/(500000000000 / 2304569204147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15294 : Bounds (764020471 / 500000000) (305608189 / 200000000) (Real.log (2304569204147 / 500000000000)) := by
  have h := reflection_log_15294_neg
  have he : Real.log (2304569204147 / 500000000000) = -Real.log (500000000000 / 2304569204147) := by
    rw [show ((2304569204147 / 500000000000) : ℝ) = ((500000000000 / 2304569204147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15295_neg : (306242981 / 200000000) ≤ -Real.log (6250000000 / 28898693031) ∧
    -Real.log (6250000000 / 28898693031) ≤ (382803727 / 250000000) := by
  have h := checkLog_sound (w := (3898693031 / 53898693031)) (n := 12)
    (lo := (28984109 / 200000000)) (hi := (72460273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28898693031 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(28898693031 / 25000000000) = 1/(6250000000 / 28898693031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15295 : Bounds (306242981 / 200000000) (382803727 / 250000000) (Real.log (28898693031 / 6250000000)) := by
  have h := reflection_log_15295_neg
  have he : Real.log (28898693031 / 6250000000) = -Real.log (6250000000 / 28898693031) := by
    rw [show ((28898693031 / 6250000000) : ℝ) = ((6250000000 / 28898693031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0239 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15296_neg : (216869641 / 40000000) ≤ -Real.log (500000000000 / 113136363636363) ∧
    -Real.log (500000000000 / 113136363636363) ≤ (5421741033 / 1000000000) := by
  have h := checkLog_sound (w := (49136363636363 / 177136363636363)) (n := 12)
    (lo := (113942153 / 200000000)) (hi := (284855383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113136363636363 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(113136363636363 / 64000000000000) = 1/(500000000000 / 113136363636363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15296 : Bounds (216869641 / 40000000) (5421741033 / 1000000000) (Real.log (113136363636363 / 500000000000)) := by
  have h := reflection_log_15296_neg
  have he : Real.log (113136363636363 / 500000000000) = -Real.log (500000000000 / 113136363636363) := by
    rw [show ((113136363636363 / 500000000000) : ℝ) = ((500000000000 / 113136363636363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15297_neg : (272241549 / 50000000) ≤ -Real.log (250000000000 / 57889534883721) ∧
    -Real.log (250000000000 / 57889534883721) ≤ (1361207747 / 250000000) := by
  have h := checkLog_sound (w := (25889534883721 / 89889534883721)) (n := 12)
    (lo := (7410009 / 12500000)) (hi := (592800721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57889534883721 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(57889534883721 / 32000000000000) = 1/(250000000000 / 57889534883721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15297 : Bounds (272241549 / 50000000) (1361207747 / 250000000) (Real.log (57889534883721 / 250000000000)) := by
  have h := reflection_log_15297_neg
  have he : Real.log (57889534883721 / 250000000000) = -Real.log (250000000000 / 57889534883721) := by
    rw [show ((57889534883721 / 250000000000) : ℝ) = ((250000000000 / 57889534883721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15298_neg : (137787667 / 200000000) ≤ -Real.log (2500 / 4979) ∧
    -Real.log (2500 / 4979) ≤ (21529323 / 31250000) := by
  have h := checkLog_sound (w := (2479 / 7479)) (n := 12)
    (lo := (137787667 / 200000000)) (hi := (21529323 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4979 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4979 / 2500) = 1/(2500 / 4979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15298 : Bounds (137787667 / 200000000) (21529323 / 31250000) (Real.log (4979 / 2500)) := by
  have h := reflection_log_15298_neg
  have he : Real.log (4979 / 2500) = -Real.log (2500 / 4979) := by
    rw [show ((4979 / 2500) : ℝ) = ((2500 / 4979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15299_neg : (4779523569 / 1000000000) ≤ -Real.log (21 / 2500) ∧
    -Real.log (21 / 2500) ≤ (597440447 / 125000000) := by
  have h := checkLog_sound (w := (289 / 961)) (n := 12)
    (lo := (620640489 / 1000000000)) (hi := (62064049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 336) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 336) = 1/(21 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15299 : Bounds (-597440447 / 125000000) (-4779523569 / 1000000000) (Real.log (21 / 2500)) := by
  have h := reflection_log_15299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15300_neg : (247777 / 250000000) ≤ -Real.log (2500000 / 2502479) ∧
    -Real.log (2500000 / 2502479) ≤ (991109 / 1000000000) := by
  have h := checkLog_sound (w := (2479 / 5002479)) (n := 12)
    (lo := (247777 / 250000000)) (hi := (991109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502479 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502479 / 2500000) = 1/(2500000 / 2502479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15300 : Bounds (247777 / 250000000) (991109 / 1000000000) (Real.log (2502479 / 2500000)) := by
  have h := reflection_log_15300_neg
  have he : Real.log (2502479 / 2500000) = -Real.log (2500000 / 2502479) := by
    rw [show ((2502479 / 2500000) : ℝ) = ((2500000 / 2502479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15301_neg : (992091 / 1000000000) ≤ -Real.log (2497521 / 2500000) ∧
    -Real.log (2497521 / 2500000) ≤ (248023 / 250000000) := by
  have h := checkLog_sound (w := (2479 / 4997521)) (n := 12)
    (lo := (992091 / 1000000000)) (hi := (248023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497521) = 1/(2497521 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15301 : Bounds (-248023 / 250000000) (-992091 / 1000000000) (Real.log (2497521 / 2500000)) := by
  have h := reflection_log_15301_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15302_neg : (124243381 / 250000000) ≤ -Real.log (1000000 / 1643739) ∧
    -Real.log (1000000 / 1643739) ≤ (19878941 / 40000000) := by
  have h := checkLog_sound (w := (643739 / 2643739)) (n := 12)
    (lo := (124243381 / 250000000)) (hi := (19878941 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1643739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1643739 / 1000000) = 1/(1000000 / 1643739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15302 : Bounds (124243381 / 250000000) (19878941 / 40000000) (Real.log (1643739 / 1000000)) := by
  have h := reflection_log_15302_neg
  have he : Real.log (1643739 / 1000000) = -Real.log (1000000 / 1643739) := by
    rw [show ((1643739 / 1000000) : ℝ) = ((1000000 / 1643739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15303_neg : (103209167 / 100000000) ≤ -Real.log (356261 / 1000000) ∧
    -Real.log (356261 / 1000000) ≤ (129011459 / 125000000) := by
  have h := checkLog_sound (w := (143739 / 856261)) (n := 12)
    (lo := (33894449 / 100000000)) (hi := (338944491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 356261) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 356261) = 1/(356261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15303 : Bounds (-129011459 / 125000000) (-103209167 / 100000000) (Real.log (356261 / 1000000)) := by
  have h := reflection_log_15303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15304_neg : (124384787 / 250000000) ≤ -Real.log (1000000 / 1644669) ∧
    -Real.log (1000000 / 1644669) ≤ (497539149 / 1000000000) := by
  have h := checkLog_sound (w := (644669 / 2644669)) (n := 12)
    (lo := (124384787 / 250000000)) (hi := (497539149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1644669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1644669 / 1000000) = 1/(1000000 / 1644669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15304 : Bounds (124384787 / 250000000) (497539149 / 1000000000) (Real.log (1644669 / 1000000)) := by
  have h := reflection_log_15304_neg
  have he : Real.log (1644669 / 1000000) = -Real.log (1000000 / 1644669) := by
    rw [show ((1644669 / 1000000) : ℝ) = ((1000000 / 1644669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15305_neg : (129338191 / 125000000) ≤ -Real.log (355331 / 1000000) ∧
    -Real.log (355331 / 1000000) ≤ (103470553 / 100000000) := by
  have h := checkLog_sound (w := (144669 / 855331)) (n := 12)
    (lo := (85389587 / 250000000)) (hi := (341558349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355331) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 355331) = 1/(355331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15305 : Bounds (-103470553 / 100000000) (-129338191 / 125000000) (Real.log (355331 / 1000000)) := by
  have h := reflection_log_15305_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15306_neg : (537166381 / 1000000000) ≤ -Real.log (584401880439 / 1000000000000) ∧
    -Real.log (584401880439 / 1000000000000) ≤ (268583191 / 500000000) := by
  have h := checkLog_sound (w := (415598119561 / 1584401880439)) (n := 12)
    (lo := (537166381 / 1000000000)) (hi := (268583191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 584401880439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 584401880439) = 1/(584401880439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15306 : Bounds (-268583191 / 500000000) (-537166381 / 1000000000) (Real.log (584401880439 / 1000000000000)) := by
  have h := reflection_log_15306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15307_neg : (107023629 / 200000000) ≤ -Real.log (585600099879 / 1000000000000) ∧
    -Real.log (585600099879 / 1000000000000) ≤ (267559073 / 500000000) := by
  have h := checkLog_sound (w := (414399900121 / 1585600099879)) (n := 12)
    (lo := (107023629 / 200000000)) (hi := (267559073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 585600099879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 585600099879) = 1/(585600099879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15307 : Bounds (-267559073 / 500000000) (-107023629 / 200000000) (Real.log (585600099879 / 1000000000000)) := by
  have h := reflection_log_15307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15308_neg : (764532597 / 500000000) ≤ -Real.log (500000000000 / 2306930873713) ∧
    -Real.log (500000000000 / 2306930873713) ≤ (1529065197 / 1000000000) := by
  have h := checkLog_sound (w := (306930873713 / 4306930873713)) (n := 12)
    (lo := (71385417 / 500000000)) (hi := (28554167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2306930873713 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2306930873713 / 2000000000000) = 1/(500000000000 / 2306930873713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15308 : Bounds (764532597 / 500000000) (1529065197 / 1000000000) (Real.log (2306930873713 / 500000000000)) := by
  have h := reflection_log_15308_neg
  have he : Real.log (2306930873713 / 500000000000) = -Real.log (500000000000 / 2306930873713) := by
    rw [show ((2306930873713 / 500000000000) : ℝ) = ((500000000000 / 2306930873713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15309_neg : (383061169 / 250000000) ≤ -Real.log (250000000000 / 1157138696033) ∧
    -Real.log (250000000000 / 1157138696033) ≤ (1532244679 / 1000000000) := by
  have h := checkLog_sound (w := (157138696033 / 2157138696033)) (n := 12)
    (lo := (36487579 / 250000000)) (hi := (145950317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157138696033 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1157138696033 / 1000000000000) = 1/(250000000000 / 1157138696033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15309 : Bounds (383061169 / 250000000) (1532244679 / 1000000000) (Real.log (1157138696033 / 250000000000)) := by
  have h := reflection_log_15309_neg
  have he : Real.log (1157138696033 / 250000000000) = -Real.log (250000000000 / 1157138696033) := by
    rw [show ((1157138696033 / 250000000000) : ℝ) = ((250000000000 / 1157138696033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15310_neg : (272241549 / 50000000) ≤ -Real.log (500000000000 / 115779069767441) ∧
    -Real.log (500000000000 / 115779069767441) ≤ (1361207747 / 250000000) := by
  have h := checkLog_sound (w := (51779069767441 / 179779069767441)) (n := 12)
    (lo := (7410009 / 12500000)) (hi := (592800721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115779069767441 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(115779069767441 / 64000000000000) = 1/(500000000000 / 115779069767441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15310 : Bounds (272241549 / 50000000) (1361207747 / 250000000) (Real.log (115779069767441 / 500000000000)) := by
  have h := reflection_log_15310_neg
  have he : Real.log (115779069767441 / 500000000000) = -Real.log (500000000000 / 115779069767441) := by
    rw [show ((115779069767441 / 500000000000) : ℝ) = ((500000000000 / 115779069767441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15311_neg : (341778869 / 62500000) ≤ -Real.log (25000000000 / 5927380952381) ∧
    -Real.log (25000000000 / 5927380952381) ≤ (683557739 / 125000000) := by
  have h := checkLog_sound (w := (2727380952381 / 9127380952381)) (n := 12)
    (lo := (154107911 / 250000000)) (hi := (123286329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5927380952381 / 3200000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(5927380952381 / 3200000000000) = 1/(25000000000 / 5927380952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15311 : Bounds (341778869 / 62500000) (683557739 / 125000000) (Real.log (5927380952381 / 25000000000)) := by
  have h := reflection_log_15311_neg
  have he : Real.log (5927380952381 / 25000000000) = -Real.log (25000000000 / 5927380952381) := by
    rw [show ((5927380952381 / 25000000000) : ℝ) = ((25000000000 / 5927380952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15312_neg : (21532461 / 31250000) ≤ -Real.log (5000 / 9959) ∧
    -Real.log (5000 / 9959) ≤ (689038753 / 1000000000) := by
  have h := checkLog_sound (w := (4959 / 14959)) (n := 12)
    (lo := (21532461 / 31250000)) (hi := (689038753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9959 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9959 / 5000) = 1/(5000 / 9959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15312 : Bounds (21532461 / 31250000) (689038753 / 1000000000) (Real.log (9959 / 5000)) := by
  have h := reflection_log_15312_neg
  have he : Real.log (9959 / 5000) = -Real.log (5000 / 9959) := by
    rw [show ((9959 / 5000) : ℝ) = ((5000 / 9959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15313_neg : (4803621121 / 1000000000) ≤ -Real.log (41 / 5000) ∧
    -Real.log (41 / 5000) ≤ (600452641 / 125000000) := by
  have h := checkLog_sound (w := (297 / 953)) (n := 12)
    (lo := (644738041 / 1000000000)) (hi := (322369021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 328) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 328) = 1/(41 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15313 : Bounds (-600452641 / 125000000) (-4803621121 / 1000000000) (Real.log (41 / 5000)) := by
  have h := reflection_log_15313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15314_neg : (247827 / 250000000) ≤ -Real.log (5000000 / 5004959) ∧
    -Real.log (5000000 / 5004959) ≤ (991309 / 1000000000) := by
  have h := checkLog_sound (w := (4959 / 10004959)) (n := 12)
    (lo := (247827 / 250000000)) (hi := (991309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004959 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004959 / 5000000) = 1/(5000000 / 5004959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15314 : Bounds (247827 / 250000000) (991309 / 1000000000) (Real.log (5004959 / 5000000)) := by
  have h := reflection_log_15314_neg
  have he : Real.log (5004959 / 5000000) = -Real.log (5000000 / 5004959) := by
    rw [show ((5004959 / 5000000) : ℝ) = ((5000000 / 5004959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15315_neg : (248073 / 250000000) ≤ -Real.log (4995041 / 5000000) ∧
    -Real.log (4995041 / 5000000) ≤ (992293 / 1000000000) := by
  have h := checkLog_sound (w := (4959 / 9995041)) (n := 12)
    (lo := (248073 / 250000000)) (hi := (992293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995041) = 1/(4995041 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15315 : Bounds (-992293 / 1000000000) (-248073 / 250000000) (Real.log (4995041 / 5000000)) := by
  have h := reflection_log_15315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15316_neg : (497156627 / 1000000000) ≤ -Real.log (25000 / 41101) ∧
    -Real.log (25000 / 41101) ≤ (124289157 / 250000000) := by
  have h := checkLog_sound (w := (16101 / 66101)) (n := 12)
    (lo := (497156627 / 1000000000)) (hi := (124289157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41101 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41101 / 25000) = 1/(25000 / 41101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15316 : Bounds (497156627 / 1000000000) (124289157 / 250000000) (Real.log (41101 / 25000)) := by
  have h := reflection_log_15316_neg
  have he : Real.log (41101 / 25000) = -Real.log (25000 / 41101) := by
    rw [show ((41101 / 25000) : ℝ) = ((25000 / 41101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15317_neg : (1032936913 / 1000000000) ≤ -Real.log (8899 / 25000) ∧
    -Real.log (8899 / 25000) ≤ (206587383 / 200000000) := by
  have h := checkLog_sound (w := (3601 / 21399)) (n := 12)
    (lo := (339789733 / 1000000000)) (hi := (169894867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 8899) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 8899) = 1/(8899 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15317 : Bounds (-206587383 / 200000000) (-1032936913 / 1000000000) (Real.log (8899 / 25000)) := by
  have h := reflection_log_15317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15318_neg : (248861377 / 500000000) ≤ -Real.log (1000000 / 1644971) ∧
    -Real.log (1000000 / 1644971) ≤ (99544551 / 200000000) := by
  have h := checkLog_sound (w := (644971 / 2644971)) (n := 12)
    (lo := (248861377 / 500000000)) (hi := (99544551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1644971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1644971 / 1000000) = 1/(1000000 / 1644971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15318 : Bounds (248861377 / 500000000) (99544551 / 200000000) (Real.log (1644971 / 1000000)) := by
  have h := reflection_log_15318_neg
  have he : Real.log (1644971 / 1000000) = -Real.log (1000000 / 1644971) := by
    rw [show ((1644971 / 1000000) : ℝ) = ((1000000 / 1644971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15319_neg : (517777901 / 500000000) ≤ -Real.log (355029 / 1000000) ∧
    -Real.log (355029 / 1000000) ≤ (258888951 / 250000000) := by
  have h := checkLog_sound (w := (144971 / 855029)) (n := 12)
    (lo := (171204311 / 500000000)) (hi := (342408623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 355029) = 1/(355029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15319 : Bounds (-258888951 / 250000000) (-517777901 / 500000000) (Real.log (355029 / 1000000)) := by
  have h := reflection_log_15319_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15320_neg : (537833047 / 1000000000) ≤ -Real.log (584012409159 / 1000000000000) ∧
    -Real.log (584012409159 / 1000000000000) ≤ (67229131 / 125000000) := by
  have h := checkLog_sound (w := (415987590841 / 1584012409159)) (n := 12)
    (lo := (537833047 / 1000000000)) (hi := (67229131 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 584012409159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 584012409159) = 1/(584012409159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15320 : Bounds (-67229131 / 125000000) (-537833047 / 1000000000) (Real.log (584012409159 / 1000000000000)) := by
  have h := reflection_log_15320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15321_neg : (267890143 / 500000000) ≤ -Real.log (365757799 / 625000000) ∧
    -Real.log (365757799 / 625000000) ≤ (535780287 / 1000000000) := by
  have h := checkLog_sound (w := (259242201 / 990757799)) (n := 12)
    (lo := (267890143 / 500000000)) (hi := (535780287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 365757799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 365757799) = 1/(365757799 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15321 : Bounds (-535780287 / 1000000000) (-267890143 / 500000000) (Real.log (365757799 / 625000000)) := by
  have h := reflection_log_15321_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15322_neg : (76504677 / 50000000) ≤ -Real.log (250000000000 / 1154652208113) ∧
    -Real.log (250000000000 / 1154652208113) ≤ (1530093543 / 1000000000) := by
  have h := checkLog_sound (w := (154652208113 / 2154652208113)) (n := 12)
    (lo := (7189959 / 50000000)) (hi := (143799181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154652208113 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1154652208113 / 1000000000000) = 1/(250000000000 / 1154652208113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15322 : Bounds (76504677 / 50000000) (1530093543 / 1000000000) (Real.log (1154652208113 / 250000000000)) := by
  have h := reflection_log_15322_neg
  have he : Real.log (1154652208113 / 250000000000) = -Real.log (250000000000 / 1154652208113) := by
    rw [show ((1154652208113 / 250000000000) : ℝ) = ((250000000000 / 1154652208113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15323_neg : (383319639 / 250000000) ≤ -Real.log (20000000000 / 92666852567) ∧
    -Real.log (20000000000 / 92666852567) ≤ (1533278559 / 1000000000) := by
  have h := checkLog_sound (w := (12666852567 / 172666852567)) (n := 12)
    (lo := (36746049 / 250000000)) (hi := (146984197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92666852567 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(92666852567 / 80000000000) = 1/(20000000000 / 92666852567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15323 : Bounds (383319639 / 250000000) (1533278559 / 1000000000) (Real.log (92666852567 / 20000000000)) := by
  have h := reflection_log_15323_neg
  have he : Real.log (92666852567 / 20000000000) = -Real.log (20000000000 / 92666852567) := by
    rw [show ((92666852567 / 20000000000) : ℝ) = ((20000000000 / 92666852567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15324_neg : (341778869 / 62500000) ≤ -Real.log (500000000000 / 118547619047619) ∧
    -Real.log (500000000000 / 118547619047619) ≤ (683557739 / 125000000) := by
  have h := checkLog_sound (w := (54547619047619 / 182547619047619)) (n := 12)
    (lo := (154107911 / 250000000)) (hi := (123286329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118547619047619 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(118547619047619 / 64000000000000) = 1/(500000000000 / 118547619047619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15324 : Bounds (341778869 / 62500000) (683557739 / 125000000) (Real.log (118547619047619 / 500000000000)) := by
  have h := reflection_log_15324_neg
  have he : Real.log (118547619047619 / 500000000000) = -Real.log (500000000000 / 118547619047619) := by
    rw [show ((118547619047619 / 500000000000) : ℝ) = ((500000000000 / 118547619047619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15325_neg : (5492659873 / 1000000000) ≤ -Real.log (125000000000 / 30362804878049) ∧
    -Real.log (125000000000 / 30362804878049) ≤ (5492659881 / 1000000000) := by
  have h := checkLog_sound (w := (14362804878049 / 46362804878049)) (n := 12)
    (lo := (640629613 / 1000000000)) (hi := (320314807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30362804878049 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(30362804878049 / 16000000000000) = 1/(125000000000 / 30362804878049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15325 : Bounds (5492659873 / 1000000000) (5492659881 / 1000000000) (Real.log (30362804878049 / 125000000000)) := by
  have h := reflection_log_15325_neg
  have he : Real.log (30362804878049 / 125000000000) = -Real.log (125000000000 / 30362804878049) := by
    rw [show ((30362804878049 / 125000000000) : ℝ) = ((125000000000 / 30362804878049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15326_neg : (689139159 / 1000000000) ≤ -Real.log (125 / 249) ∧
    -Real.log (125 / 249) ≤ (17228479 / 25000000) := by
  have h := checkLog_sound (w := (62 / 187)) (n := 12)
    (lo := (689139159 / 1000000000)) (hi := (17228479 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249 / 125) = 1/(125 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15326 : Bounds (689139159 / 1000000000) (17228479 / 25000000) (Real.log (249 / 125)) := by
  have h := reflection_log_15326_neg
  have he : Real.log (249 / 125) = -Real.log (125 / 249) := by
    rw [show ((249 / 125) : ℝ) = ((125 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15327_neg : (4828313733 / 1000000000) ≤ -Real.log (1 / 125) ∧
    -Real.log (1 / 125) ≤ (241415687 / 50000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 64) = 1/(1 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15327 : Bounds (-241415687 / 50000000) (-4828313733 / 1000000000) (Real.log (1 / 125)) := by
  have h := reflection_log_15327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15328_neg : (247877 / 250000000) ≤ -Real.log (31250 / 31281) ∧
    -Real.log (31250 / 31281) ≤ (991509 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 62531)) (n := 12)
    (lo := (247877 / 250000000)) (hi := (991509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31281 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31281 / 31250) = 1/(31250 / 31281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15328 : Bounds (247877 / 250000000) (991509 / 1000000000) (Real.log (31281 / 31250)) := by
  have h := reflection_log_15328_neg
  have he : Real.log (31281 / 31250) = -Real.log (31250 / 31281) := by
    rw [show ((31281 / 31250) : ℝ) = ((31250 / 31281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15329_neg : (248123 / 250000000) ≤ -Real.log (31219 / 31250) ∧
    -Real.log (31219 / 31250) ≤ (992493 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 62469)) (n := 12)
    (lo := (248123 / 250000000)) (hi := (992493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31219) = 1/(31219 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15329 : Bounds (-992493 / 1000000000) (-248123 / 250000000) (Real.log (31219 / 31250)) := by
  have h := reflection_log_15329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15330_neg : (31083769 / 62500000) ≤ -Real.log (500000 / 822171) ∧
    -Real.log (500000 / 822171) ≤ (99468061 / 200000000) := by
  have h := checkLog_sound (w := (322171 / 1322171)) (n := 12)
    (lo := (31083769 / 62500000)) (hi := (99468061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822171 / 500000) = 1/(500000 / 822171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15330 : Bounds (31083769 / 62500000) (99468061 / 200000000) (Real.log (822171 / 500000)) := by
  have h := reflection_log_15330_neg
  have he : Real.log (822171 / 500000) = -Real.log (500000 / 822171) := by
    rw [show ((822171 / 500000) : ℝ) = ((500000 / 822171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15331_neg : (1033785683 / 1000000000) ≤ -Real.log (177829 / 500000) ∧
    -Real.log (177829 / 500000) ≤ (206757137 / 200000000) := by
  have h := checkLog_sound (w := (72171 / 427829)) (n := 12)
    (lo := (340638503 / 1000000000)) (hi := (42579813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177829) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177829) = 1/(177829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15331 : Bounds (-206757137 / 200000000) (-1033785683 / 1000000000) (Real.log (177829 / 500000)) := by
  have h := reflection_log_15331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15332_neg : (99581387 / 200000000) ≤ -Real.log (500000 / 822637) ∧
    -Real.log (500000 / 822637) ≤ (62238367 / 125000000) := by
  have h := checkLog_sound (w := (322637 / 1322637)) (n := 12)
    (lo := (99581387 / 200000000)) (hi := (62238367 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822637 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822637 / 500000) = 1/(500000 / 822637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15332 : Bounds (99581387 / 200000000) (62238367 / 125000000) (Real.log (822637 / 500000)) := by
  have h := reflection_log_15332_neg
  have he : Real.log (822637 / 500000) = -Real.log (500000 / 822637) := by
    rw [show ((822637 / 500000) : ℝ) = ((500000 / 822637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15333_neg : (1036409617 / 1000000000) ≤ -Real.log (177363 / 500000) ∧
    -Real.log (177363 / 500000) ≤ (1036409619 / 1000000000) := by
  have h := checkLog_sound (w := (72637 / 427363)) (n := 12)
    (lo := (343262437 / 1000000000)) (hi := (171631219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177363) = 1/(177363 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15333 : Bounds (-1036409619 / 1000000000) (-1036409617 / 1000000000) (Real.log (177363 / 500000)) := by
  have h := reflection_log_15333_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15334_neg : (269251341 / 500000000) ≤ -Real.log (145905366231 / 250000000000) ∧
    -Real.log (145905366231 / 250000000000) ≤ (538502683 / 1000000000) := by
  have h := checkLog_sound (w := (104094633769 / 395905366231)) (n := 12)
    (lo := (269251341 / 500000000)) (hi := (538502683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145905366231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145905366231) = 1/(145905366231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15334 : Bounds (-538502683 / 1000000000) (-269251341 / 500000000) (Real.log (145905366231 / 250000000000)) := by
  have h := reflection_log_15334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15335_neg : (536445379 / 1000000000) ≤ -Real.log (146205846759 / 250000000000) ∧
    -Real.log (146205846759 / 250000000000) ≤ (26822269 / 50000000) := by
  have h := checkLog_sound (w := (103794153241 / 396205846759)) (n := 12)
    (lo := (536445379 / 1000000000)) (hi := (26822269 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 146205846759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 146205846759) = 1/(146205846759 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15335 : Bounds (-26822269 / 50000000) (-536445379 / 1000000000) (Real.log (146205846759 / 250000000000)) := by
  have h := reflection_log_15335_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15336_neg : (1531125987 / 1000000000) ≤ -Real.log (125000000000 / 577922470463) ∧
    -Real.log (125000000000 / 577922470463) ≤ (153112599 / 100000000) := by
  have h := checkLog_sound (w := (77922470463 / 1077922470463)) (n := 12)
    (lo := (144831627 / 1000000000)) (hi := (36207907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577922470463 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(577922470463 / 500000000000) = 1/(125000000000 / 577922470463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15336 : Bounds (1531125987 / 1000000000) (153112599 / 100000000) (Real.log (577922470463 / 125000000000)) := by
  have h := reflection_log_15336_neg
  have he : Real.log (577922470463 / 125000000000) = -Real.log (125000000000 / 577922470463) := by
    rw [show ((577922470463 / 125000000000) : ℝ) = ((125000000000 / 577922470463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15337_neg : (1534316553 / 1000000000) ≤ -Real.log (31250000000 / 144942328727) ∧
    -Real.log (31250000000 / 144942328727) ≤ (383579139 / 250000000) := by
  have h := checkLog_sound (w := (19942328727 / 269942328727)) (n := 12)
    (lo := (148022193 / 1000000000)) (hi := (74011097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144942328727 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(144942328727 / 125000000000) = 1/(31250000000 / 144942328727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15337 : Bounds (1534316553 / 1000000000) (383579139 / 250000000) (Real.log (144942328727 / 31250000000)) := by
  have h := reflection_log_15337_neg
  have he : Real.log (144942328727 / 31250000000) = -Real.log (31250000000 / 144942328727) := by
    rw [show ((144942328727 / 31250000000) : ℝ) = ((31250000000 / 144942328727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15338_neg : (5492659873 / 1000000000) ≤ -Real.log (100000000000 / 24290243902439) ∧
    -Real.log (100000000000 / 24290243902439) ≤ (5492659881 / 1000000000) := by
  have h := checkLog_sound (w := (11490243902439 / 37090243902439)) (n := 12)
    (lo := (640629613 / 1000000000)) (hi := (320314807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24290243902439 / 12800000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(24290243902439 / 12800000000000) = 1/(100000000000 / 24290243902439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15338 : Bounds (5492659873 / 1000000000) (5492659881 / 1000000000) (Real.log (24290243902439 / 100000000000)) := by
  have h := reflection_log_15338_neg
  have he : Real.log (24290243902439 / 100000000000) = -Real.log (100000000000 / 24290243902439) := by
    rw [show ((24290243902439 / 100000000000) : ℝ) = ((100000000000 / 24290243902439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15339_neg : (1379363223 / 250000000) ≤ -Real.log (1 / 249) ∧
    -Real.log (1 / 249) ≤ (55174529 / 10000000) := by
  have h := checkLog_sound (w := (121 / 377)) (n := 12)
    (lo := (83177829 / 125000000)) (hi := (665422633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 128) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(249 / 128) = 1/(1 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15339 : Bounds (1379363223 / 250000000) (55174529 / 10000000) (Real.log (249 / 1)) := by
  have h := reflection_log_15339_neg
  have he : Real.log (249 / 1) = -Real.log (1 / 249) := by
    rw [show ((249 / 1) : ℝ) = ((1 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15340_neg : (137847911 / 200000000) ≤ -Real.log (5000 / 9961) ∧
    -Real.log (5000 / 9961) ≤ (172309889 / 250000000) := by
  have h := checkLog_sound (w := (4961 / 14961)) (n := 12)
    (lo := (137847911 / 200000000)) (hi := (172309889 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9961 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9961 / 5000) = 1/(5000 / 9961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15340 : Bounds (137847911 / 200000000) (172309889 / 250000000) (Real.log (9961 / 5000)) := by
  have h := reflection_log_15340_neg
  have he : Real.log (9961 / 5000) = -Real.log (5000 / 9961) := by
    rw [show ((9961 / 5000) : ℝ) = ((5000 / 9961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15341_neg : (4853631541 / 1000000000) ≤ -Real.log (39 / 5000) ∧
    -Real.log (39 / 5000) ≤ (4853631549 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 1249)) (n := 12)
    (lo := (1601281 / 1000000000)) (hi := (800641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 624) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 624) = 1/(39 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15341 : Bounds (-4853631549 / 1000000000) (-4853631541 / 1000000000) (Real.log (39 / 5000)) := by
  have h := reflection_log_15341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15342_neg : (247927 / 250000000) ≤ -Real.log (5000000 / 5004961) ∧
    -Real.log (5000000 / 5004961) ≤ (991709 / 1000000000) := by
  have h := checkLog_sound (w := (4961 / 10004961)) (n := 12)
    (lo := (247927 / 250000000)) (hi := (991709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004961 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004961 / 5000000) = 1/(5000000 / 5004961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15342 : Bounds (247927 / 250000000) (991709 / 1000000000) (Real.log (5004961 / 5000000)) := by
  have h := reflection_log_15342_neg
  have he : Real.log (5004961 / 5000000) = -Real.log (5000000 / 5004961) := by
    rw [show ((5004961 / 5000000) : ℝ) = ((5000000 / 5004961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15343_neg : (248173 / 250000000) ≤ -Real.log (4995039 / 5000000) ∧
    -Real.log (4995039 / 5000000) ≤ (992693 / 1000000000) := by
  have h := checkLog_sound (w := (4961 / 9995039)) (n := 12)
    (lo := (248173 / 250000000)) (hi := (992693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995039) = 1/(4995039 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15343 : Bounds (-992693 / 1000000000) (-248173 / 250000000) (Real.log (4995039 / 5000000)) := by
  have h := reflection_log_15343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15344_neg : (497525163 / 1000000000) ≤ -Real.log (500000 / 822323) ∧
    -Real.log (500000 / 822323) ≤ (124381291 / 250000000) := by
  have h := checkLog_sound (w := (322323 / 1322323)) (n := 12)
    (lo := (497525163 / 1000000000)) (hi := (124381291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822323 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822323 / 500000) = 1/(500000 / 822323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15344 : Bounds (497525163 / 1000000000) (124381291 / 250000000) (Real.log (822323 / 500000)) := by
  have h := reflection_log_15344_neg
  have he : Real.log (822323 / 500000) = -Real.log (500000 / 822323) := by
    rw [show ((822323 / 500000) : ℝ) = ((500000 / 822323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15345_neg : (517320401 / 500000000) ≤ -Real.log (177677 / 500000) ∧
    -Real.log (177677 / 500000) ≤ (258660201 / 250000000) := by
  have h := checkLog_sound (w := (72323 / 427677)) (n := 12)
    (lo := (170746811 / 500000000)) (hi := (341493623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177677) = 1/(177677 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15345 : Bounds (-258660201 / 250000000) (-517320401 / 500000000) (Real.log (177677 / 500000)) := by
  have h := reflection_log_15345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15346_neg : (49809169 / 100000000) ≤ -Real.log (500000 / 822789) ∧
    -Real.log (500000 / 822789) ≤ (498091691 / 1000000000) := by
  have h := checkLog_sound (w := (322789 / 1322789)) (n := 12)
    (lo := (49809169 / 100000000)) (hi := (498091691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822789 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822789 / 500000) = 1/(500000 / 822789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15346 : Bounds (49809169 / 100000000) (498091691 / 1000000000) (Real.log (822789 / 500000)) := by
  have h := reflection_log_15346_neg
  have he : Real.log (822789 / 500000) = -Real.log (500000 / 822789) := by
    rw [show ((822789 / 500000) : ℝ) = ((500000 / 822789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15347_neg : (129658373 / 125000000) ≤ -Real.log (177211 / 500000) ∧
    -Real.log (177211 / 500000) ≤ (518633493 / 500000000) := by
  have h := checkLog_sound (w := (72789 / 427211)) (n := 12)
    (lo := (86029951 / 250000000)) (hi := (68823961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177211) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177211) = 1/(177211 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15347 : Bounds (-518633493 / 500000000) (-129658373 / 125000000) (Real.log (177211 / 500000)) := by
  have h := reflection_log_15347_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15348_neg : (107835059 / 200000000) ≤ -Real.log (145807261479 / 250000000000) ∧
    -Real.log (145807261479 / 250000000000) ≤ (4212307 / 7812500) := by
  have h := checkLog_sound (w := (104192738521 / 395807261479)) (n := 12)
    (lo := (107835059 / 200000000)) (hi := (4212307 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145807261479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145807261479) = 1/(145807261479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15348 : Bounds (-4212307 / 7812500) (-107835059 / 200000000) (Real.log (145807261479 / 250000000000)) := by
  have h := reflection_log_15348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15349_neg : (537115639 / 1000000000) ≤ -Real.log (146107883671 / 250000000000) ∧
    -Real.log (146107883671 / 250000000000) ≤ (13427891 / 25000000) := by
  have h := checkLog_sound (w := (103892116329 / 396107883671)) (n := 12)
    (lo := (537115639 / 1000000000)) (hi := (13427891 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 146107883671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 146107883671) = 1/(146107883671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15349 : Bounds (-13427891 / 25000000) (-537115639 / 1000000000) (Real.log (146107883671 / 250000000000)) := by
  have h := reflection_log_15349_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15350_neg : (306433193 / 200000000) ≤ -Real.log (500000000000 / 2314095240239) ∧
    -Real.log (500000000000 / 2314095240239) ≤ (95760373 / 62500000) := by
  have h := checkLog_sound (w := (314095240239 / 4314095240239)) (n := 12)
    (lo := (29174321 / 200000000)) (hi := (72935803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2314095240239 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2314095240239 / 2000000000000) = 1/(500000000000 / 2314095240239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15350 : Bounds (306433193 / 200000000) (95760373 / 62500000) (Real.log (2314095240239 / 500000000000)) := by
  have h := reflection_log_15350_neg
  have he : Real.log (2314095240239 / 500000000000) = -Real.log (500000000000 / 2314095240239) := by
    rw [show ((2314095240239 / 500000000000) : ℝ) = ((500000000000 / 2314095240239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15351_neg : (767679337 / 500000000) ≤ -Real.log (500000000000 / 2321495279639) ∧
    -Real.log (500000000000 / 2321495279639) ≤ (1535358677 / 1000000000) := by
  have h := checkLog_sound (w := (321495279639 / 4321495279639)) (n := 12)
    (lo := (74532157 / 500000000)) (hi := (29812863 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2321495279639 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2321495279639 / 2000000000000) = 1/(500000000000 / 2321495279639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15351 : Bounds (767679337 / 500000000) (1535358677 / 1000000000) (Real.log (2321495279639 / 500000000000)) := by
  have h := reflection_log_15351_neg
  have he : Real.log (2321495279639 / 500000000000) = -Real.log (500000000000 / 2321495279639) := by
    rw [show ((2321495279639 / 500000000000) : ℝ) = ((500000000000 / 2321495279639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15352_neg : (5542871097 / 1000000000) ≤ -Real.log (500000000000 / 127705128205129) ∧
    -Real.log (500000000000 / 127705128205129) ≤ (1108574221 / 200000000) := by
  have h := checkLog_sound (w := (63705128205129 / 191705128205129)) (n := 12)
    (lo := (690840837 / 1000000000)) (hi := (345420419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127705128205129 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(127705128205129 / 64000000000000) = 1/(500000000000 / 127705128205129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15352 : Bounds (5542871097 / 1000000000) (1108574221 / 200000000) (Real.log (127705128205129 / 500000000000)) := by
  have h := reflection_log_15352_neg
  have he : Real.log (127705128205129 / 500000000000) = -Real.log (500000000000 / 127705128205129) := by
    rw [show ((127705128205129 / 500000000000) : ℝ) = ((500000000000 / 127705128205129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15353_neg : (344669971 / 500000000) ≤ -Real.log (2500 / 4981) ∧
    -Real.log (2500 / 4981) ≤ (689339943 / 1000000000) := by
  have h := checkLog_sound (w := (2481 / 7481)) (n := 12)
    (lo := (344669971 / 500000000)) (hi := (689339943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4981 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4981 / 2500) = 1/(2500 / 4981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15353 : Bounds (344669971 / 500000000) (689339943 / 1000000000) (Real.log (4981 / 2500)) := by
  have h := reflection_log_15353_neg
  have he : Real.log (4981 / 2500) = -Real.log (2500 / 4981) := by
    rw [show ((4981 / 2500) : ℝ) = ((2500 / 4981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15354_neg : (4879607027 / 1000000000) ≤ -Real.log (19 / 2500) ∧
    -Real.log (19 / 2500) ≤ (975921407 / 200000000) := by
  have h := checkLog_sound (w := (17 / 1233)) (n := 12)
    (lo := (27576767 / 1000000000)) (hi := (430887 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 608) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 608) = 1/(19 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15354 : Bounds (-975921407 / 200000000) (-4879607027 / 1000000000) (Real.log (19 / 2500)) := by
  have h := reflection_log_15354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15355_neg : (991907 / 1000000000) ≤ -Real.log (2500000 / 2502481) ∧
    -Real.log (2500000 / 2502481) ≤ (247977 / 250000000) := by
  have h := checkLog_sound (w := (2481 / 5002481)) (n := 12)
    (lo := (991907 / 1000000000)) (hi := (247977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502481 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502481 / 2500000) = 1/(2500000 / 2502481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15355 : Bounds (991907 / 1000000000) (247977 / 250000000) (Real.log (2502481 / 2500000)) := by
  have h := reflection_log_15355_neg
  have he : Real.log (2502481 / 2500000) = -Real.log (2500000 / 2502481) := by
    rw [show ((2502481 / 2500000) : ℝ) = ((2500000 / 2502481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15356_neg : (248223 / 250000000) ≤ -Real.log (2497519 / 2500000) ∧
    -Real.log (2497519 / 2500000) ≤ (992893 / 1000000000) := by
  have h := checkLog_sound (w := (2481 / 4997519)) (n := 12)
    (lo := (248223 / 250000000)) (hi := (992893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497519) = 1/(2497519 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15356 : Bounds (-992893 / 1000000000) (-248223 / 250000000) (Real.log (2497519 / 2500000)) := by
  have h := reflection_log_15356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15357_neg : (124427497 / 250000000) ≤ -Real.log (20000 / 32899) ∧
    -Real.log (20000 / 32899) ≤ (497709989 / 1000000000) := by
  have h := checkLog_sound (w := (12899 / 52899)) (n := 12)
    (lo := (124427497 / 250000000)) (hi := (497709989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32899 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32899 / 20000) = 1/(20000 / 32899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15357 : Bounds (124427497 / 250000000) (497709989 / 1000000000) (Real.log (32899 / 20000)) := by
  have h := reflection_log_15357_neg
  have he : Real.log (32899 / 20000) = -Real.log (20000 / 32899) := by
    rw [show ((32899 / 20000) : ℝ) = ((20000 / 32899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15358_neg : (1035496653 / 1000000000) ≤ -Real.log (7101 / 20000) ∧
    -Real.log (7101 / 20000) ≤ (207099331 / 200000000) := by
  have h := checkLog_sound (w := (2899 / 17101)) (n := 12)
    (lo := (342349473 / 1000000000)) (hi := (171174737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10000 / 7101) = 1/(7101 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15358 : Bounds (-207099331 / 200000000) (-1035496653 / 1000000000) (Real.log (7101 / 20000)) := by
  have h := reflection_log_15358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15359_neg : (249138509 / 500000000) ≤ -Real.log (1000000 / 1645883) ∧
    -Real.log (1000000 / 1645883) ≤ (498277019 / 1000000000) := by
  have h := checkLog_sound (w := (645883 / 2645883)) (n := 12)
    (lo := (249138509 / 500000000)) (hi := (498277019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1645883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1645883 / 1000000) = 1/(1000000 / 1645883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15359 : Bounds (249138509 / 500000000) (498277019 / 1000000000) (Real.log (1645883 / 1000000)) := by
  have h := reflection_log_15359_neg
  have he : Real.log (1645883 / 1000000) = -Real.log (1000000 / 1645883) := by
    rw [show ((1645883 / 1000000) : ℝ) = ((1000000 / 1645883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0240 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15360_neg : (1038127911 / 1000000000) ≤ -Real.log (354117 / 1000000) ∧
    -Real.log (354117 / 1000000) ≤ (1038127913 / 1000000000) := by
  have h := checkLog_sound (w := (145883 / 854117)) (n := 12)
    (lo := (344980731 / 1000000000)) (hi := (86245183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 354117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 354117) = 1/(354117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15360 : Bounds (-1038127913 / 1000000000) (-1038127911 / 1000000000) (Real.log (354117 / 1000000)) := by
  have h := reflection_log_15360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15361_neg : (539850893 / 1000000000) ≤ -Real.log (582835150311 / 1000000000000) ∧
    -Real.log (582835150311 / 1000000000000) ≤ (269925447 / 500000000) := by
  have h := checkLog_sound (w := (417164849689 / 1582835150311)) (n := 12)
    (lo := (539850893 / 1000000000)) (hi := (269925447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 582835150311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 582835150311) = 1/(582835150311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15361 : Bounds (-269925447 / 500000000) (-539850893 / 1000000000) (Real.log (582835150311 / 1000000000000)) := by
  have h := reflection_log_15361_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15362_neg : (107557333 / 200000000) ≤ -Real.log (233615799 / 400000000) ∧
    -Real.log (233615799 / 400000000) ≤ (268893333 / 500000000) := by
  have h := checkLog_sound (w := (166384201 / 633615799)) (n := 12)
    (lo := (107557333 / 200000000)) (hi := (268893333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 233615799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 233615799) = 1/(233615799 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15362 : Bounds (-268893333 / 500000000) (-107557333 / 200000000) (Real.log (233615799 / 400000000)) := by
  have h := reflection_log_15362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15363_neg : (1533206641 / 1000000000) ≤ -Real.log (100000000000 / 463300943529) ∧
    -Real.log (100000000000 / 463300943529) ≤ (383301661 / 250000000) := by
  have h := checkLog_sound (w := (63300943529 / 863300943529)) (n := 12)
    (lo := (146912281 / 1000000000)) (hi := (73456141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463300943529 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(463300943529 / 400000000000) = 1/(100000000000 / 463300943529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15363 : Bounds (1533206641 / 1000000000) (383301661 / 250000000) (Real.log (463300943529 / 100000000000)) := by
  have h := reflection_log_15363_neg
  have he : Real.log (463300943529 / 100000000000) = -Real.log (100000000000 / 463300943529) := by
    rw [show ((463300943529 / 100000000000) : ℝ) = ((100000000000 / 463300943529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15364_neg : (1536404929 / 1000000000) ≤ -Real.log (250000000000 / 1161962712889) ∧
    -Real.log (250000000000 / 1161962712889) ≤ (384101233 / 250000000) := by
  have h := checkLog_sound (w := (161962712889 / 2161962712889)) (n := 12)
    (lo := (150110569 / 1000000000)) (hi := (15011057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161962712889 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1161962712889 / 1000000000000) = 1/(250000000000 / 1161962712889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15364 : Bounds (1536404929 / 1000000000) (384101233 / 250000000) (Real.log (1161962712889 / 250000000000)) := by
  have h := reflection_log_15364_neg
  have he : Real.log (1161962712889 / 250000000000) = -Real.log (250000000000 / 1161962712889) := by
    rw [show ((1161962712889 / 250000000000) : ℝ) = ((250000000000 / 1161962712889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15365_neg : (5542871097 / 1000000000) ≤ -Real.log (62500000000 / 15963141025641) ∧
    -Real.log (62500000000 / 15963141025641) ≤ (1108574221 / 200000000) := by
  have h := checkLog_sound (w := (7963141025641 / 23963141025641)) (n := 12)
    (lo := (690840837 / 1000000000)) (hi := (345420419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15963141025641 / 8000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(15963141025641 / 8000000000000) = 1/(62500000000 / 15963141025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15365 : Bounds (5542871097 / 1000000000) (1108574221 / 200000000) (Real.log (15963141025641 / 62500000000)) := by
  have h := reflection_log_15365_neg
  have he : Real.log (15963141025641 / 62500000000) = -Real.log (62500000000 / 15963141025641) := by
    rw [show ((15963141025641 / 62500000000) : ℝ) = ((62500000000 / 15963141025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15366_neg : (5568946969 / 1000000000) ≤ -Real.log (250000000000 / 65539473684211) ∧
    -Real.log (250000000000 / 65539473684211) ≤ (2784473489 / 500000000) := by
  have h := checkLog_sound (w := (1539473684211 / 129539473684211)) (n := 12)
    (lo := (23769529 / 1000000000)) (hi := (2376953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65539473684211 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(65539473684211 / 64000000000000) = 1/(250000000000 / 65539473684211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15366 : Bounds (5568946969 / 1000000000) (2784473489 / 500000000) (Real.log (65539473684211 / 250000000000)) := by
  have h := reflection_log_15366_neg
  have he : Real.log (65539473684211 / 250000000000) = -Real.log (250000000000 / 65539473684211) := by
    rw [show ((65539473684211 / 250000000000) : ℝ) = ((250000000000 / 65539473684211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15367_neg : (344720159 / 500000000) ≤ -Real.log (5000 / 9963) ∧
    -Real.log (5000 / 9963) ≤ (689440319 / 1000000000) := by
  have h := checkLog_sound (w := (4963 / 14963)) (n := 12)
    (lo := (344720159 / 500000000)) (hi := (689440319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9963 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9963 / 5000) = 1/(5000 / 9963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15367 : Bounds (344720159 / 500000000) (689440319 / 1000000000) (Real.log (9963 / 5000)) := by
  have h := reflection_log_15367_neg
  have he : Real.log (9963 / 5000) = -Real.log (5000 / 9963) := by
    rw [show ((9963 / 5000) : ℝ) = ((5000 / 9963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15368_neg : (2453137637 / 500000000) ≤ -Real.log (37 / 5000) ∧
    -Real.log (37 / 5000) ≤ (2453137641 / 500000000) := by
  have h := checkLog_sound (w := (33 / 1217)) (n := 12)
    (lo := (27122507 / 500000000)) (hi := (10849003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 592) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 592) = 1/(37 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15368 : Bounds (-2453137641 / 500000000) (-2453137637 / 500000000) (Real.log (37 / 5000)) := by
  have h := reflection_log_15368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15369_neg : (992107 / 1000000000) ≤ -Real.log (5000000 / 5004963) ∧
    -Real.log (5000000 / 5004963) ≤ (248027 / 250000000) := by
  have h := checkLog_sound (w := (4963 / 10004963)) (n := 12)
    (lo := (992107 / 1000000000)) (hi := (248027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004963 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004963 / 5000000) = 1/(5000000 / 5004963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15369 : Bounds (992107 / 1000000000) (248027 / 250000000) (Real.log (5004963 / 5000000)) := by
  have h := reflection_log_15369_neg
  have he : Real.log (5004963 / 5000000) = -Real.log (5000000 / 5004963) := by
    rw [show ((5004963 / 5000000) : ℝ) = ((5000000 / 5004963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15370_neg : (248273 / 250000000) ≤ -Real.log (4995037 / 5000000) ∧
    -Real.log (4995037 / 5000000) ≤ (993093 / 1000000000) := by
  have h := checkLog_sound (w := (4963 / 9995037)) (n := 12)
    (lo := (248273 / 250000000)) (hi := (993093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995037) = 1/(4995037 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15370 : Bounds (-993093 / 1000000000) (-248273 / 250000000) (Real.log (4995037 / 5000000)) := by
  have h := reflection_log_15370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15371_neg : (99579199 / 200000000) ≤ -Real.log (125000 / 205657) ∧
    -Real.log (125000 / 205657) ≤ (124473999 / 250000000) := by
  have h := checkLog_sound (w := (80657 / 330657)) (n := 12)
    (lo := (99579199 / 200000000)) (hi := (124473999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205657 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205657 / 125000) = 1/(125000 / 205657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15371 : Bounds (99579199 / 200000000) (124473999 / 250000000) (Real.log (205657 / 125000)) := by
  have h := reflection_log_15371_neg
  have he : Real.log (205657 / 125000) = -Real.log (125000 / 205657) := by
    rw [show ((205657 / 125000) : ℝ) = ((125000 / 205657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15372_neg : (8290871 / 8000000) ≤ -Real.log (44343 / 125000) ∧
    -Real.log (44343 / 125000) ≤ (1036358877 / 1000000000) := by
  have h := checkLog_sound (w := (18157 / 106843)) (n := 12)
    (lo := (68642339 / 200000000)) (hi := (21450731 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44343) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 44343) = 1/(44343 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15372 : Bounds (-1036358877 / 1000000000) (-8290871 / 8000000) (Real.log (44343 / 125000)) := by
  have h := reflection_log_15372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15373_neg : (249231763 / 500000000) ≤ -Real.log (100000 / 164619) ∧
    -Real.log (100000 / 164619) ≤ (498463527 / 1000000000) := by
  have h := checkLog_sound (w := (64619 / 264619)) (n := 12)
    (lo := (249231763 / 500000000)) (hi := (498463527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164619 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164619 / 100000) = 1/(100000 / 164619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15373 : Bounds (249231763 / 500000000) (498463527 / 1000000000) (Real.log (164619 / 100000)) := by
  have h := reflection_log_15373_neg
  have he : Real.log (164619 / 100000) = -Real.log (100000 / 164619) := by
    rw [show ((164619 / 100000) : ℝ) = ((100000 / 164619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15374_neg : (32468601 / 31250000) ≤ -Real.log (35381 / 100000) ∧
    -Real.log (35381 / 100000) ≤ (519497617 / 500000000) := by
  have h := checkLog_sound (w := (14619 / 85381)) (n := 12)
    (lo := (86462013 / 250000000)) (hi := (345848053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35381) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35381) = 1/(35381 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15374 : Bounds (-519497617 / 500000000) (-32468601 / 31250000) (Real.log (35381 / 100000)) := by
  have h := reflection_log_15374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15375_neg : (270265853 / 500000000) ≤ -Real.log (5824384839 / 10000000000) ∧
    -Real.log (5824384839 / 10000000000) ≤ (540531707 / 1000000000) := by
  have h := checkLog_sound (w := (4175615161 / 15824384839)) (n := 12)
    (lo := (270265853 / 500000000)) (hi := (540531707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5824384839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5824384839) = 1/(5824384839 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15375 : Bounds (-540531707 / 1000000000) (-270265853 / 500000000) (Real.log (5824384839 / 10000000000)) := by
  have h := reflection_log_15375_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15376_neg : (538462881 / 1000000000) ≤ -Real.log (9119448351 / 15625000000) ∧
    -Real.log (9119448351 / 15625000000) ≤ (269231441 / 500000000) := by
  have h := checkLog_sound (w := (6505551649 / 24744448351)) (n := 12)
    (lo := (538462881 / 1000000000)) (hi := (269231441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9119448351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9119448351) = 1/(9119448351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15376 : Bounds (-269231441 / 500000000) (-538462881 / 1000000000) (Real.log (9119448351 / 15625000000)) := by
  have h := reflection_log_15376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15377_neg : (153425487 / 100000000) ≤ -Real.log (500000000000 / 2318934217351) ∧
    -Real.log (500000000000 / 2318934217351) ≤ (1534254873 / 1000000000) := by
  have h := checkLog_sound (w := (318934217351 / 4318934217351)) (n := 12)
    (lo := (14796051 / 100000000)) (hi := (147960511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2318934217351 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2318934217351 / 2000000000000) = 1/(500000000000 / 2318934217351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15377 : Bounds (153425487 / 100000000) (1534254873 / 1000000000) (Real.log (2318934217351 / 500000000000)) := by
  have h := reflection_log_15377_neg
  have he : Real.log (2318934217351 / 500000000000) = -Real.log (500000000000 / 2318934217351) := by
    rw [show ((2318934217351 / 500000000000) : ℝ) = ((500000000000 / 2318934217351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15378_neg : (768729379 / 500000000) ≤ -Real.log (500000000000 / 2326375738391) ∧
    -Real.log (500000000000 / 2326375738391) ≤ (1537458761 / 1000000000) := by
  have h := checkLog_sound (w := (326375738391 / 4326375738391)) (n := 12)
    (lo := (75582199 / 500000000)) (hi := (151164399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2326375738391 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2326375738391 / 2000000000000) = 1/(500000000000 / 2326375738391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15378 : Bounds (768729379 / 500000000) (1537458761 / 1000000000) (Real.log (2326375738391 / 500000000000)) := by
  have h := reflection_log_15378_neg
  have he : Real.log (2326375738391 / 500000000000) = -Real.log (500000000000 / 2326375738391) := by
    rw [show ((2326375738391 / 500000000000) : ℝ) = ((500000000000 / 2326375738391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15379_neg : (5568946969 / 1000000000) ≤ -Real.log (500000000000 / 131078947368421) ∧
    -Real.log (500000000000 / 131078947368421) ≤ (2784473489 / 500000000) := by
  have h := checkLog_sound (w := (3078947368421 / 259078947368421)) (n := 12)
    (lo := (23769529 / 1000000000)) (hi := (2376953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131078947368421 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(131078947368421 / 128000000000000) = 1/(500000000000 / 131078947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15379 : Bounds (5568946969 / 1000000000) (2784473489 / 500000000) (Real.log (131078947368421 / 500000000000)) := by
  have h := reflection_log_15379_neg
  have he : Real.log (131078947368421 / 500000000000) = -Real.log (500000000000 / 131078947368421) := by
    rw [show ((131078947368421 / 500000000000) : ℝ) = ((500000000000 / 131078947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15380_neg : (699464449 / 125000000) ≤ -Real.log (15625000000 / 4207347972973) ∧
    -Real.log (15625000000 / 4207347972973) ≤ (5595715601 / 1000000000) := by
  have h := checkLog_sound (w := (207347972973 / 8207347972973)) (n := 12)
    (lo := (6317269 / 125000000)) (hi := (50538153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4207347972973 / 4000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(4207347972973 / 4000000000000) = 1/(15625000000 / 4207347972973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15380 : Bounds (699464449 / 125000000) (5595715601 / 1000000000) (Real.log (4207347972973 / 15625000000)) := by
  have h := reflection_log_15380_neg
  have he : Real.log (4207347972973 / 15625000000) = -Real.log (15625000000 / 4207347972973) := by
    rw [show ((4207347972973 / 15625000000) : ℝ) = ((15625000000 / 4207347972973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15381_neg : (172385171 / 250000000) ≤ -Real.log (1250 / 2491) ∧
    -Real.log (1250 / 2491) ≤ (137908137 / 200000000) := by
  have h := checkLog_sound (w := (1241 / 3741)) (n := 12)
    (lo := (172385171 / 250000000)) (hi := (137908137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2491 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2491 / 1250) = 1/(1250 / 2491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15381 : Bounds (172385171 / 250000000) (137908137 / 200000000) (Real.log (2491 / 1250)) := by
  have h := reflection_log_15381_neg
  have he : Real.log (2491 / 1250) = -Real.log (1250 / 2491) := by
    rw [show ((2491 / 1250) : ℝ) = ((1250 / 2491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15382_neg : (4933674249 / 1000000000) ≤ -Real.log (9 / 1250) ∧
    -Real.log (9 / 1250) ≤ (4933674257 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 1201)) (n := 12)
    (lo := (81643989 / 1000000000)) (hi := (8164399 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 576) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 576) = 1/(9 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15382 : Bounds (-4933674257 / 1000000000) (-4933674249 / 1000000000) (Real.log (9 / 1250)) := by
  have h := reflection_log_15382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15383_neg : (992307 / 1000000000) ≤ -Real.log (1250000 / 1251241) ∧
    -Real.log (1250000 / 1251241) ≤ (248077 / 250000000) := by
  have h := checkLog_sound (w := (1241 / 2501241)) (n := 12)
    (lo := (992307 / 1000000000)) (hi := (248077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251241 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251241 / 1250000) = 1/(1250000 / 1251241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15383 : Bounds (992307 / 1000000000) (248077 / 250000000) (Real.log (1251241 / 1250000)) := by
  have h := reflection_log_15383_neg
  have he : Real.log (1251241 / 1250000) = -Real.log (1250000 / 1251241) := by
    rw [show ((1251241 / 1250000) : ℝ) = ((1250000 / 1251241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15384_neg : (993293 / 1000000000) ≤ -Real.log (1248759 / 1250000) ∧
    -Real.log (1248759 / 1250000) ≤ (496647 / 500000000) := by
  have h := checkLog_sound (w := (1241 / 2498759)) (n := 12)
    (lo := (993293 / 1000000000)) (hi := (496647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1248759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1248759) = 1/(1248759 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15384 : Bounds (-496647 / 500000000) (-993293 / 1000000000) (Real.log (1248759 / 1250000)) := by
  have h := reflection_log_15384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15385_neg : (498081967 / 1000000000) ≤ -Real.log (500000 / 822781) ∧
    -Real.log (500000 / 822781) ≤ (31130123 / 62500000) := by
  have h := checkLog_sound (w := (322781 / 1322781)) (n := 12)
    (lo := (498081967 / 1000000000)) (hi := (31130123 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822781 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822781 / 500000) = 1/(500000 / 822781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15385 : Bounds (498081967 / 1000000000) (31130123 / 62500000) (Real.log (822781 / 500000)) := by
  have h := reflection_log_15385_neg
  have he : Real.log (822781 / 500000) = -Real.log (500000 / 822781) := by
    rw [show ((822781 / 500000) : ℝ) = ((500000 / 822781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15386_neg : (1037221841 / 1000000000) ≤ -Real.log (177219 / 500000) ∧
    -Real.log (177219 / 500000) ≤ (1037221843 / 1000000000) := by
  have h := checkLog_sound (w := (72781 / 427219)) (n := 12)
    (lo := (344074661 / 1000000000)) (hi := (172037331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177219) = 1/(177219 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15386 : Bounds (-1037221843 / 1000000000) (-1037221841 / 1000000000) (Real.log (177219 / 500000)) := by
  have h := reflection_log_15386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15387_neg : (31165663 / 62500000) ≤ -Real.log (500000 / 823249) ∧
    -Real.log (500000 / 823249) ≤ (498650609 / 1000000000) := by
  have h := checkLog_sound (w := (323249 / 1323249)) (n := 12)
    (lo := (31165663 / 62500000)) (hi := (498650609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823249 / 500000) = 1/(500000 / 823249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15387 : Bounds (31165663 / 62500000) (498650609 / 1000000000) (Real.log (823249 / 500000)) := by
  have h := reflection_log_15387_neg
  have he : Real.log (823249 / 500000) = -Real.log (500000 / 823249) := by
    rw [show ((823249 / 500000) : ℝ) = ((500000 / 823249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15388_neg : (207973227 / 200000000) ≤ -Real.log (176751 / 500000) ∧
    -Real.log (176751 / 500000) ≤ (1039866137 / 1000000000) := by
  have h := checkLog_sound (w := (73249 / 426751)) (n := 12)
    (lo := (69343791 / 200000000)) (hi := (86679739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176751) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 176751) = 1/(176751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15388 : Bounds (-1039866137 / 1000000000) (-207973227 / 200000000) (Real.log (176751 / 500000)) := by
  have h := reflection_log_15388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15389_neg : (541215527 / 1000000000) ≤ -Real.log (145510083999 / 250000000000) ∧
    -Real.log (145510083999 / 250000000000) ≤ (67651941 / 125000000) := by
  have h := checkLog_sound (w := (104489916001 / 395510083999)) (n := 12)
    (lo := (541215527 / 1000000000)) (hi := (67651941 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145510083999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145510083999) = 1/(145510083999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15389 : Bounds (-67651941 / 125000000) (-541215527 / 1000000000) (Real.log (145510083999 / 250000000000)) := by
  have h := reflection_log_15389_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15390_neg : (4313119 / 8000000) ≤ -Real.log (145812426039 / 250000000000) ∧
    -Real.log (145812426039 / 250000000000) ≤ (134784969 / 250000000) := by
  have h := checkLog_sound (w := (104187573961 / 395812426039)) (n := 12)
    (lo := (4313119 / 8000000)) (hi := (134784969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145812426039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145812426039) = 1/(145812426039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15390 : Bounds (-134784969 / 250000000) (-4313119 / 8000000) (Real.log (145812426039 / 250000000000)) := by
  have h := reflection_log_15390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15391_neg : (11994561 / 7812500) ≤ -Real.log (250000000000 / 1160683956009) ∧
    -Real.log (250000000000 / 1160683956009) ≤ (1535303811 / 1000000000) := by
  have h := checkLog_sound (w := (160683956009 / 2160683956009)) (n := 12)
    (lo := (18626181 / 125000000)) (hi := (149009449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160683956009 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1160683956009 / 1000000000000) = 1/(250000000000 / 1160683956009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15391 : Bounds (11994561 / 7812500) (1535303811 / 1000000000) (Real.log (1160683956009 / 250000000000)) := by
  have h := reflection_log_15391_neg
  have he : Real.log (1160683956009 / 250000000000) = -Real.log (250000000000 / 1160683956009) := by
    rw [show ((1160683956009 / 250000000000) : ℝ) = ((250000000000 / 1160683956009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15392_neg : (769258371 / 500000000) ≤ -Real.log (25000000000 / 116441915463) ∧
    -Real.log (25000000000 / 116441915463) ≤ (307703349 / 200000000) := by
  have h := checkLog_sound (w := (16441915463 / 216441915463)) (n := 12)
    (lo := (76111191 / 500000000)) (hi := (152222383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116441915463 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(116441915463 / 100000000000) = 1/(25000000000 / 116441915463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15392 : Bounds (769258371 / 500000000) (307703349 / 200000000) (Real.log (116441915463 / 25000000000)) := by
  have h := reflection_log_15392_neg
  have he : Real.log (116441915463 / 25000000000) = -Real.log (25000000000 / 116441915463) := by
    rw [show ((116441915463 / 25000000000) : ℝ) = ((25000000000 / 116441915463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15393_neg : (699464449 / 125000000) ≤ -Real.log (100000000000 / 26927027027027) ∧
    -Real.log (100000000000 / 26927027027027) ≤ (5595715601 / 1000000000) := by
  have h := checkLog_sound (w := (1327027027027 / 52527027027027)) (n := 12)
    (lo := (6317269 / 125000000)) (hi := (50538153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26927027027027 / 25600000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(26927027027027 / 25600000000000) = 1/(100000000000 / 26927027027027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15393 : Bounds (699464449 / 125000000) (5595715601 / 1000000000) (Real.log (26927027027027 / 100000000000)) := by
  have h := reflection_log_15393_neg
  have he : Real.log (26927027027027 / 100000000000) = -Real.log (100000000000 / 26927027027027) := by
    rw [show ((26927027027027 / 100000000000) : ℝ) = ((100000000000 / 26927027027027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15394_neg : (5623214933 / 1000000000) ≤ -Real.log (500000000000 / 138388888888889) ∧
    -Real.log (500000000000 / 138388888888889) ≤ (2811607471 / 500000000) := by
  have h := checkLog_sound (w := (10388888888889 / 266388888888889)) (n := 12)
    (lo := (78037493 / 1000000000)) (hi := (39018747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138388888888889 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(138388888888889 / 128000000000000) = 1/(500000000000 / 138388888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15394 : Bounds (5623214933 / 1000000000) (2811607471 / 500000000) (Real.log (138388888888889 / 500000000000)) := by
  have h := reflection_log_15394_neg
  have he : Real.log (138388888888889 / 500000000000) = -Real.log (500000000000 / 138388888888889) := by
    rw [show ((138388888888889 / 500000000000) : ℝ) = ((500000000000 / 138388888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15395_neg : (689641041 / 1000000000) ≤ -Real.log (1000 / 1993) ∧
    -Real.log (1000 / 1993) ≤ (344820521 / 500000000) := by
  have h := checkLog_sound (w := (993 / 2993)) (n := 12)
    (lo := (689641041 / 1000000000)) (hi := (344820521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1993 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1993 / 1000) = 1/(1000 / 1993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15395 : Bounds (689641041 / 1000000000) (344820521 / 500000000) (Real.log (1993 / 1000)) := by
  have h := reflection_log_15395_neg
  have he : Real.log (1993 / 1000) = -Real.log (1000 / 1993) := by
    rw [show ((1993 / 1000) : ℝ) = ((1000 / 1993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15396_neg : (2480922563 / 500000000) ≤ -Real.log (7 / 1000) ∧
    -Real.log (7 / 1000) ≤ (2480922567 / 500000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(125 / 112) = 1/(7 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15396 : Bounds (-2480922567 / 500000000) (-2480922563 / 500000000) (Real.log (7 / 1000)) := by
  have h := reflection_log_15396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15397_neg : (992507 / 1000000000) ≤ -Real.log (1000000 / 1000993) ∧
    -Real.log (1000000 / 1000993) ≤ (248127 / 250000000) := by
  have h := checkLog_sound (w := (993 / 2000993)) (n := 12)
    (lo := (992507 / 1000000000)) (hi := (248127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000993 / 1000000) = 1/(1000000 / 1000993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15397 : Bounds (992507 / 1000000000) (248127 / 250000000) (Real.log (1000993 / 1000000)) := by
  have h := reflection_log_15397_neg
  have he : Real.log (1000993 / 1000000) = -Real.log (1000000 / 1000993) := by
    rw [show ((1000993 / 1000000) : ℝ) = ((1000000 / 1000993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15398_neg : (993493 / 1000000000) ≤ -Real.log (999007 / 1000000) ∧
    -Real.log (999007 / 1000000) ≤ (496747 / 500000000) := by
  have h := checkLog_sound (w := (993 / 1999007)) (n := 12)
    (lo := (993493 / 1000000000)) (hi := (496747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999007) = 1/(999007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15398 : Bounds (-496747 / 500000000) (-993493 / 1000000000) (Real.log (999007 / 1000000)) := by
  have h := reflection_log_15398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15399_neg : (498269119 / 1000000000) ≤ -Real.log (100000 / 164587) ∧
    -Real.log (100000 / 164587) ≤ (1557091 / 3125000) := by
  have h := checkLog_sound (w := (64587 / 264587)) (n := 12)
    (lo := (498269119 / 1000000000)) (hi := (1557091 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164587 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164587 / 100000) = 1/(100000 / 164587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15399 : Bounds (498269119 / 1000000000) (1557091 / 3125000) (Real.log (164587 / 100000)) := by
  have h := reflection_log_15399_neg
  have he : Real.log (164587 / 100000) = -Real.log (100000 / 164587) := by
    rw [show ((164587 / 100000) : ℝ) = ((100000 / 164587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15400_neg : (1038091201 / 1000000000) ≤ -Real.log (35413 / 100000) ∧
    -Real.log (35413 / 100000) ≤ (1038091203 / 1000000000) := by
  have h := checkLog_sound (w := (14587 / 85413)) (n := 12)
    (lo := (344944021 / 1000000000)) (hi := (172472011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35413) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35413) = 1/(35413 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15400 : Bounds (-1038091203 / 1000000000) (-1038091201 / 1000000000) (Real.log (35413 / 100000)) := by
  have h := reflection_log_15400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15401_neg : (498838261 / 1000000000) ≤ -Real.log (1000000 / 1646807) ∧
    -Real.log (1000000 / 1646807) ≤ (249419131 / 500000000) := by
  have h := checkLog_sound (w := (646807 / 2646807)) (n := 12)
    (lo := (498838261 / 1000000000)) (hi := (249419131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1646807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1646807 / 1000000) = 1/(1000000 / 1646807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15401 : Bounds (498838261 / 1000000000) (249419131 / 500000000) (Real.log (1646807 / 1000000)) := by
  have h := reflection_log_15401_neg
  have he : Real.log (1646807 / 1000000) = -Real.log (1000000 / 1646807) := by
    rw [show ((1646807 / 1000000) : ℝ) = ((1000000 / 1646807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15402_neg : (260185157 / 250000000) ≤ -Real.log (353193 / 1000000) ∧
    -Real.log (353193 / 1000000) ≤ (104074063 / 100000000) := by
  have h := checkLog_sound (w := (146807 / 853193)) (n := 12)
    (lo := (43449181 / 125000000)) (hi := (347593449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 353193) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 353193) = 1/(353193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15402 : Bounds (-104074063 / 100000000) (-260185157 / 250000000) (Real.log (353193 / 1000000)) := by
  have h := reflection_log_15402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15403_neg : (541902367 / 1000000000) ≤ -Real.log (581640704751 / 1000000000000) ∧
    -Real.log (581640704751 / 1000000000000) ≤ (16934449 / 31250000) := by
  have h := checkLog_sound (w := (418359295249 / 1581640704751)) (n := 12)
    (lo := (541902367 / 1000000000)) (hi := (16934449 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 581640704751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 581640704751) = 1/(581640704751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15403 : Bounds (-16934449 / 31250000) (-541902367 / 1000000000) (Real.log (581640704751 / 1000000000000)) := by
  have h := reflection_log_15403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15404_neg : (539822081 / 1000000000) ≤ -Real.log (5828519431 / 10000000000) ∧
    -Real.log (5828519431 / 10000000000) ≤ (269911041 / 500000000) := by
  have h := checkLog_sound (w := (4171480569 / 15828519431)) (n := 12)
    (lo := (539822081 / 1000000000)) (hi := (269911041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5828519431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5828519431) = 1/(5828519431 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15404 : Bounds (-269911041 / 500000000) (-539822081 / 1000000000) (Real.log (5828519431 / 10000000000)) := by
  have h := reflection_log_15404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15405_neg : (2400563 / 1562500) ≤ -Real.log (50000000000 / 232382176037) ∧
    -Real.log (50000000000 / 232382176037) ≤ (1536360323 / 1000000000) := by
  have h := checkLog_sound (w := (32382176037 / 432382176037)) (n := 12)
    (lo := (3751649 / 25000000)) (hi := (150065961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232382176037 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(232382176037 / 200000000000) = 1/(50000000000 / 232382176037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15405 : Bounds (2400563 / 1562500) (1536360323 / 1000000000) (Real.log (232382176037 / 50000000000)) := by
  have h := reflection_log_15405_neg
  have he : Real.log (232382176037 / 50000000000) = -Real.log (50000000000 / 232382176037) := by
    rw [show ((232382176037 / 50000000000) : ℝ) = ((50000000000 / 232382176037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15406_neg : (1539578889 / 1000000000) ≤ -Real.log (125000000000 / 582828297843) ∧
    -Real.log (125000000000 / 582828297843) ≤ (384894723 / 250000000) := by
  have h := checkLog_sound (w := (82828297843 / 1082828297843)) (n := 12)
    (lo := (153284529 / 1000000000)) (hi := (15328453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582828297843 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(582828297843 / 500000000000) = 1/(125000000000 / 582828297843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15406 : Bounds (1539578889 / 1000000000) (384894723 / 250000000) (Real.log (582828297843 / 125000000000)) := by
  have h := reflection_log_15406_neg
  have he : Real.log (582828297843 / 125000000000) = -Real.log (125000000000 / 582828297843) := by
    rw [show ((582828297843 / 125000000000) : ℝ) = ((125000000000 / 582828297843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15407_neg : (5623214933 / 1000000000) ≤ -Real.log (62500000000 / 17298611111111) ∧
    -Real.log (62500000000 / 17298611111111) ≤ (2811607471 / 500000000) := by
  have h := checkLog_sound (w := (1298611111111 / 33298611111111)) (n := 12)
    (lo := (78037493 / 1000000000)) (hi := (39018747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17298611111111 / 16000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(17298611111111 / 16000000000000) = 1/(62500000000 / 17298611111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15407 : Bounds (5623214933 / 1000000000) (2811607471 / 500000000) (Real.log (17298611111111 / 62500000000)) := by
  have h := reflection_log_15407_neg
  have he : Real.log (17298611111111 / 62500000000) = -Real.log (62500000000 / 17298611111111) := by
    rw [show ((17298611111111 / 62500000000) : ℝ) = ((62500000000 / 17298611111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15408_neg : (2825743083 / 500000000) ≤ -Real.log (500000000000 / 142357142857143) ∧
    -Real.log (500000000000 / 142357142857143) ≤ (226059447 / 40000000) := by
  have h := checkLog_sound (w := (14357142857143 / 270357142857143)) (n := 12)
    (lo := (53154363 / 500000000)) (hi := (106308727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142357142857143 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(142357142857143 / 128000000000000) = 1/(500000000000 / 142357142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15408 : Bounds (2825743083 / 500000000) (226059447 / 40000000) (Real.log (142357142857143 / 500000000000)) := by
  have h := reflection_log_15408_neg
  have he : Real.log (142357142857143 / 500000000000) = -Real.log (500000000000 / 142357142857143) := by
    rw [show ((142357142857143 / 500000000000) : ℝ) = ((500000000000 / 142357142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15409_neg : (689741387 / 1000000000) ≤ -Real.log (2500 / 4983) ∧
    -Real.log (2500 / 4983) ≤ (172435347 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 7483)) (n := 12)
    (lo := (689741387 / 1000000000)) (hi := (172435347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4983 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4983 / 2500) = 1/(2500 / 4983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15409 : Bounds (689741387 / 1000000000) (172435347 / 250000000) (Real.log (4983 / 2500)) := by
  have h := reflection_log_15409_neg
  have he : Real.log (4983 / 2500) = -Real.log (2500 / 4983) := by
    rw [show ((4983 / 2500) : ℝ) = ((2500 / 4983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15410_neg : (2495416331 / 500000000) ≤ -Real.log (17 / 2500) ∧
    -Real.log (17 / 2500) ≤ (499083267 / 100000000) := by
  have h := checkLog_sound (w := (81 / 1169)) (n := 12)
    (lo := (69401201 / 500000000)) (hi := (138802403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 544) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 544) = 1/(17 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15410 : Bounds (-499083267 / 100000000) (-2495416331 / 500000000) (Real.log (17 / 2500)) := by
  have h := reflection_log_15410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15411_neg : (992707 / 1000000000) ≤ -Real.log (2500000 / 2502483) ∧
    -Real.log (2500000 / 2502483) ≤ (248177 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 5002483)) (n := 12)
    (lo := (992707 / 1000000000)) (hi := (248177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502483 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502483 / 2500000) = 1/(2500000 / 2502483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15411 : Bounds (992707 / 1000000000) (248177 / 250000000) (Real.log (2502483 / 2500000)) := by
  have h := reflection_log_15411_neg
  have he : Real.log (2502483 / 2500000) = -Real.log (2500000 / 2502483) := by
    rw [show ((2502483 / 2500000) : ℝ) = ((2500000 / 2502483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15412_neg : (993693 / 1000000000) ≤ -Real.log (2497517 / 2500000) ∧
    -Real.log (2497517 / 2500000) ≤ (496847 / 500000000) := by
  have h := checkLog_sound (w := (2483 / 4997517)) (n := 12)
    (lo := (993693 / 1000000000)) (hi := (496847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497517) = 1/(2497517 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15412 : Bounds (-496847 / 500000000) (-993693 / 1000000000) (Real.log (2497517 / 2500000)) := by
  have h := reflection_log_15412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15413_neg : (124614363 / 250000000) ≤ -Real.log (50000 / 82309) ∧
    -Real.log (50000 / 82309) ≤ (498457453 / 1000000000) := by
  have h := checkLog_sound (w := (32309 / 132309)) (n := 12)
    (lo := (124614363 / 250000000)) (hi := (498457453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82309 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82309 / 50000) = 1/(50000 / 82309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15413 : Bounds (124614363 / 250000000) (498457453 / 1000000000) (Real.log (82309 / 50000)) := by
  have h := reflection_log_15413_neg
  have he : Real.log (82309 / 50000) = -Real.log (50000 / 82309) := by
    rw [show ((82309 / 50000) : ℝ) = ((50000 / 82309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15414_neg : (1038966969 / 1000000000) ≤ -Real.log (17691 / 50000) ∧
    -Real.log (17691 / 50000) ≤ (1038966971 / 1000000000) := by
  have h := checkLog_sound (w := (7309 / 42691)) (n := 12)
    (lo := (345819789 / 1000000000)) (hi := (34581979 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17691) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 17691) = 1/(17691 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15414 : Bounds (-1038966971 / 1000000000) (-1038966969 / 1000000000) (Real.log (17691 / 50000)) := by
  have h := reflection_log_15414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15415_neg : (249513243 / 500000000) ≤ -Real.log (1000000 / 1647117) ∧
    -Real.log (1000000 / 1647117) ≤ (499026487 / 1000000000) := by
  have h := checkLog_sound (w := (647117 / 2647117)) (n := 12)
    (lo := (249513243 / 500000000)) (hi := (499026487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647117 / 1000000) = 1/(1000000 / 1647117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15415 : Bounds (249513243 / 500000000) (499026487 / 1000000000) (Real.log (1647117 / 1000000)) := by
  have h := reflection_log_15415_neg
  have he : Real.log (1647117 / 1000000) = -Real.log (1000000 / 1647117) := by
    rw [show ((1647117 / 1000000) : ℝ) = ((1000000 / 1647117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15416_neg : (1041618721 / 1000000000) ≤ -Real.log (352883 / 1000000) ∧
    -Real.log (352883 / 1000000) ≤ (1041618723 / 1000000000) := by
  have h := checkLog_sound (w := (147117 / 852883)) (n := 12)
    (lo := (348471541 / 1000000000)) (hi := (174235771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352883) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 352883) = 1/(352883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15416 : Bounds (-1041618723 / 1000000000) (-1041618721 / 1000000000) (Real.log (352883 / 1000000)) := by
  have h := reflection_log_15416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15417_neg : (271296117 / 500000000) ≤ -Real.log (581239588311 / 1000000000000) ∧
    -Real.log (581239588311 / 1000000000000) ≤ (108518447 / 200000000) := by
  have h := checkLog_sound (w := (418760411689 / 1581239588311)) (n := 12)
    (lo := (271296117 / 500000000)) (hi := (108518447 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 581239588311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 581239588311) = 1/(581239588311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15417 : Bounds (-108518447 / 200000000) (-271296117 / 500000000) (Real.log (581239588311 / 1000000000000)) := by
  have h := reflection_log_15417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15418_neg : (540509517 / 1000000000) ≤ -Real.log (1456128519 / 2500000000) ∧
    -Real.log (1456128519 / 2500000000) ≤ (270254759 / 500000000) := by
  have h := checkLog_sound (w := (1043871481 / 3956128519)) (n := 12)
    (lo := (540509517 / 1000000000)) (hi := (270254759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1456128519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1456128519) = 1/(1456128519 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15418 : Bounds (-270254759 / 500000000) (-540509517 / 1000000000) (Real.log (1456128519 / 2500000000)) := by
  have h := reflection_log_15418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15419_neg : (76871221 / 50000000) ≤ -Real.log (10000000000 / 46525917133) ∧
    -Real.log (10000000000 / 46525917133) ≤ (1537424423 / 1000000000) := by
  have h := checkLog_sound (w := (6525917133 / 86525917133)) (n := 12)
    (lo := (7556503 / 50000000)) (hi := (151130061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46525917133 / 40000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(46525917133 / 40000000000) = 1/(10000000000 / 46525917133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15419 : Bounds (76871221 / 50000000) (1537424423 / 1000000000) (Real.log (46525917133 / 10000000000)) := by
  have h := reflection_log_15419_neg
  have he : Real.log (46525917133 / 10000000000) = -Real.log (10000000000 / 46525917133) := by
    rw [show ((46525917133 / 10000000000) : ℝ) = ((10000000000 / 46525917133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15420_neg : (1540645207 / 1000000000) ≤ -Real.log (250000000000 / 1166900219053) ∧
    -Real.log (250000000000 / 1166900219053) ≤ (154064521 / 100000000) := by
  have h := checkLog_sound (w := (166900219053 / 2166900219053)) (n := 12)
    (lo := (154350847 / 1000000000)) (hi := (602933 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166900219053 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1166900219053 / 1000000000000) = 1/(250000000000 / 1166900219053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15420 : Bounds (1540645207 / 1000000000) (154064521 / 100000000) (Real.log (1166900219053 / 250000000000)) := by
  have h := reflection_log_15420_neg
  have he : Real.log (1166900219053 / 250000000000) = -Real.log (250000000000 / 1166900219053) := by
    rw [show ((1166900219053 / 250000000000) : ℝ) = ((250000000000 / 1166900219053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15421_neg : (2825743083 / 500000000) ≤ -Real.log (250000000000 / 71178571428571) ∧
    -Real.log (250000000000 / 71178571428571) ≤ (226059447 / 40000000) := by
  have h := checkLog_sound (w := (7178571428571 / 135178571428571)) (n := 12)
    (lo := (53154363 / 500000000)) (hi := (106308727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71178571428571 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(71178571428571 / 64000000000000) = 1/(250000000000 / 71178571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15421 : Bounds (2825743083 / 500000000) (226059447 / 40000000) (Real.log (71178571428571 / 250000000000)) := by
  have h := reflection_log_15421_neg
  have he : Real.log (71178571428571 / 250000000000) = -Real.log (250000000000 / 71178571428571) := by
    rw [show ((71178571428571 / 250000000000) : ℝ) = ((250000000000 / 71178571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15422_neg : (5680574049 / 1000000000) ≤ -Real.log (125000000000 / 36639705882353) ∧
    -Real.log (125000000000 / 36639705882353) ≤ (2840287029 / 500000000) := by
  have h := checkLog_sound (w := (4639705882353 / 68639705882353)) (n := 12)
    (lo := (135396609 / 1000000000)) (hi := (13539661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36639705882353 / 32000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(36639705882353 / 32000000000000) = 1/(125000000000 / 36639705882353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15422 : Bounds (5680574049 / 1000000000) (2840287029 / 500000000) (Real.log (36639705882353 / 125000000000)) := by
  have h := reflection_log_15422_neg
  have he : Real.log (36639705882353 / 125000000000) = -Real.log (125000000000 / 36639705882353) := by
    rw [show ((36639705882353 / 125000000000) : ℝ) = ((125000000000 / 36639705882353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15423_neg : (689841723 / 1000000000) ≤ -Real.log (5000 / 9967) ∧
    -Real.log (5000 / 9967) ≤ (172460431 / 250000000) := by
  have h := checkLog_sound (w := (4967 / 14967)) (n := 12)
    (lo := (689841723 / 1000000000)) (hi := (172460431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9967 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9967 / 5000) = 1/(5000 / 9967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15423 : Bounds (689841723 / 1000000000) (172460431 / 250000000) (Real.log (9967 / 5000)) := by
  have h := reflection_log_15423_neg
  have he : Real.log (9967 / 5000) = -Real.log (5000 / 9967) := by
    rw [show ((9967 / 5000) : ℝ) = ((5000 / 9967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


