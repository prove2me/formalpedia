-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0193__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0193__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:15:58.513342+00:00
-- url     : https://prove2.me/theorems/69e012cb-2521-4c2e-b05a-fdab98567df1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0193 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0194, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0193 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0194, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0195)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0193 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0194, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0195)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0193 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0194, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0195) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0193 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0194, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0195).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0193 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12352_neg : (293539191 / 1000000000) ≤ -Real.log (37281 / 50000) ∧
    -Real.log (37281 / 50000) ≤ (36692399 / 125000000) := by
  have h := checkLog_sound (w := (12719 / 87281)) (n := 12)
    (lo := (293539191 / 1000000000)) (hi := (36692399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37281) = 1/(37281 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12352 : Bounds (-36692399 / 125000000) (-293539191 / 1000000000) (Real.log (37281 / 50000)) := by
  have h := reflection_log_12352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12353_neg : (13379553 / 200000000) ≤ -Real.log (2338227039 / 2500000000) ∧
    -Real.log (2338227039 / 2500000000) ≤ (33448883 / 500000000) := by
  have h := checkLog_sound (w := (161772961 / 4838227039)) (n := 12)
    (lo := (13379553 / 200000000)) (hi := (33448883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2338227039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2338227039) = 1/(2338227039 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12353 : Bounds (-33448883 / 500000000) (-13379553 / 200000000) (Real.log (2338227039 / 2500000000)) := by
  have h := reflection_log_12353_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12354_neg : (6633607 / 100000000) ≤ -Real.log (37432652439 / 40000000000) ∧
    -Real.log (37432652439 / 40000000000) ≤ (66336071 / 1000000000) := by
  have h := checkLog_sound (w := (2567347561 / 77432652439)) (n := 12)
    (lo := (6633607 / 100000000)) (hi := (66336071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37432652439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37432652439) = 1/(37432652439 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12354 : Bounds (-66336071 / 1000000000) (-6633607 / 100000000) (Real.log (37432652439 / 40000000000)) := by
  have h := reflection_log_12354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12355_neg : (20718721 / 40000000) ≤ -Real.log (500000000000 / 839306640951) ∧
    -Real.log (500000000000 / 839306640951) ≤ (258984013 / 500000000) := by
  have h := checkLog_sound (w := (339306640951 / 1339306640951)) (n := 12)
    (lo := (20718721 / 40000000)) (hi := (258984013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839306640951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839306640951 / 500000000000) = 1/(500000000000 / 839306640951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12355 : Bounds (20718721 / 40000000) (258984013 / 500000000) (Real.log (839306640951 / 500000000000)) := by
  have h := reflection_log_12355_neg
  have he : Real.log (839306640951 / 500000000000) = -Real.log (500000000000 / 839306640951) := by
    rw [show ((839306640951 / 500000000000) : ℝ) = ((500000000000 / 839306640951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12356_neg : (260090309 / 500000000) ≤ -Real.log (500000000000 / 841165741263) ∧
    -Real.log (500000000000 / 841165741263) ≤ (520180619 / 1000000000) := by
  have h := checkLog_sound (w := (341165741263 / 1341165741263)) (n := 12)
    (lo := (260090309 / 500000000)) (hi := (520180619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841165741263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841165741263 / 500000000000) = 1/(500000000000 / 841165741263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12356 : Bounds (260090309 / 500000000) (520180619 / 1000000000) (Real.log (841165741263 / 500000000000)) := by
  have h := reflection_log_12356_neg
  have he : Real.log (841165741263 / 500000000000) = -Real.log (500000000000 / 841165741263) := by
    rw [show ((841165741263 / 500000000000) : ℝ) = ((500000000000 / 841165741263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12357_neg : (21180063 / 20000000) ≤ -Real.log (100000000000 / 288349514563) ∧
    -Real.log (100000000000 / 288349514563) ≤ (66187697 / 62500000) := by
  have h := checkLog_sound (w := (88349514563 / 488349514563)) (n := 12)
    (lo := (36585597 / 100000000)) (hi := (365855971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288349514563 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(288349514563 / 200000000000) = 1/(100000000000 / 288349514563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12357 : Bounds (21180063 / 20000000) (66187697 / 62500000) (Real.log (288349514563 / 100000000000)) := by
  have h := reflection_log_12357_neg
  have he : Real.log (288349514563 / 100000000000) = -Real.log (100000000000 / 288349514563) := by
    rw [show ((288349514563 / 100000000000) : ℝ) = ((100000000000 / 288349514563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12358_neg : (1061619959 / 1000000000) ≤ -Real.log (500000000000 / 1445525291829) ∧
    -Real.log (500000000000 / 1445525291829) ≤ (1061619961 / 1000000000) := by
  have h := checkLog_sound (w := (445525291829 / 2445525291829)) (n := 12)
    (lo := (368472779 / 1000000000)) (hi := (18423639 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1445525291829 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1445525291829 / 1000000000000) = 1/(500000000000 / 1445525291829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12358 : Bounds (1061619959 / 1000000000) (1061619961 / 1000000000) (Real.log (1445525291829 / 500000000000)) := by
  have h := reflection_log_12358_neg
  have he : Real.log (1445525291829 / 500000000000) = -Real.log (500000000000 / 1445525291829) := by
    rw [show ((1445525291829 / 500000000000) : ℝ) = ((500000000000 / 1445525291829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12359_neg : (396760667 / 1000000000) ≤ -Real.log (1000 / 1487) ∧
    -Real.log (1000 / 1487) ≤ (99190167 / 250000000) := by
  have h := checkLog_sound (w := (487 / 2487)) (n := 12)
    (lo := (396760667 / 1000000000)) (hi := (99190167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1487 / 1000) = 1/(1000 / 1487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12359 : Bounds (396760667 / 1000000000) (99190167 / 250000000) (Real.log (1487 / 1000)) := by
  have h := reflection_log_12359_neg
  have he : Real.log (1487 / 1000) = -Real.log (1000 / 1487) := by
    rw [show ((1487 / 1000) : ℝ) = ((1000 / 1487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12360_neg : (667479433 / 1000000000) ≤ -Real.log (513 / 1000) ∧
    -Real.log (513 / 1000) ≤ (333739717 / 500000000) := by
  have h := checkLog_sound (w := (487 / 1513)) (n := 12)
    (lo := (667479433 / 1000000000)) (hi := (333739717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 513) = 1/(513 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12360 : Bounds (-333739717 / 500000000) (-667479433 / 1000000000) (Real.log (513 / 1000)) := by
  have h := reflection_log_12360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12361_neg : (486881 / 1000000000) ≤ -Real.log (1000000 / 1000487) ∧
    -Real.log (1000000 / 1000487) ≤ (243441 / 500000000) := by
  have h := checkLog_sound (w := (487 / 2000487)) (n := 12)
    (lo := (486881 / 1000000000)) (hi := (243441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000487 / 1000000) = 1/(1000000 / 1000487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12361 : Bounds (486881 / 1000000000) (243441 / 500000000) (Real.log (1000487 / 1000000)) := by
  have h := reflection_log_12361_neg
  have he : Real.log (1000487 / 1000000) = -Real.log (1000000 / 1000487) := by
    rw [show ((1000487 / 1000000) : ℝ) = ((1000000 / 1000487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12362_neg : (243559 / 500000000) ≤ -Real.log (999513 / 1000000) ∧
    -Real.log (999513 / 1000000) ≤ (487119 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 1999513)) (n := 12)
    (lo := (243559 / 500000000)) (hi := (487119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999513) = 1/(999513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12362 : Bounds (-487119 / 1000000000) (-243559 / 500000000) (Real.log (999513 / 1000000)) := by
  have h := reflection_log_12362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12363_neg : (226272251 / 1000000000) ≤ -Real.log (1000000 / 1253917) ∧
    -Real.log (1000000 / 1253917) ≤ (56568063 / 250000000) := by
  have h := checkLog_sound (w := (253917 / 2253917)) (n := 12)
    (lo := (226272251 / 1000000000)) (hi := (56568063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253917 / 1000000) = 1/(1000000 / 1253917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12363 : Bounds (226272251 / 1000000000) (56568063 / 250000000) (Real.log (1253917 / 1000000)) := by
  have h := reflection_log_12363_neg
  have he : Real.log (1253917 / 1000000) = -Real.log (1000000 / 1253917) := by
    rw [show ((1253917 / 1000000) : ℝ) = ((1000000 / 1253917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12364_neg : (36614803 / 125000000) ≤ -Real.log (746083 / 1000000) ∧
    -Real.log (746083 / 1000000) ≤ (11716737 / 40000000) := by
  have h := checkLog_sound (w := (253917 / 1746083)) (n := 12)
    (lo := (36614803 / 125000000)) (hi := (11716737 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746083) = 1/(746083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12364 : Bounds (-11716737 / 40000000) (-36614803 / 125000000) (Real.log (746083 / 1000000)) := by
  have h := reflection_log_12364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12365_neg : (227098121 / 1000000000) ≤ -Real.log (1000000 / 1254953) ∧
    -Real.log (1000000 / 1254953) ≤ (113549061 / 500000000) := by
  have h := checkLog_sound (w := (254953 / 2254953)) (n := 12)
    (lo := (227098121 / 1000000000)) (hi := (113549061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254953 / 1000000) = 1/(1000000 / 1254953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12365 : Bounds (227098121 / 1000000000) (113549061 / 500000000) (Real.log (1254953 / 1000000)) := by
  have h := reflection_log_12365_neg
  have he : Real.log (1254953 / 1000000) = -Real.log (1000000 / 1254953) := by
    rw [show ((1254953 / 1000000) : ℝ) = ((1000000 / 1254953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12366_neg : (11772319 / 40000000) ≤ -Real.log (745047 / 1000000) ∧
    -Real.log (745047 / 1000000) ≤ (36788497 / 125000000) := by
  have h := checkLog_sound (w := (254953 / 1745047)) (n := 12)
    (lo := (11772319 / 40000000)) (hi := (36788497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745047) = 1/(745047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12366 : Bounds (-36788497 / 125000000) (-11772319 / 40000000) (Real.log (745047 / 1000000)) := by
  have h := reflection_log_12366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12367_neg : (67209853 / 1000000000) ≤ -Real.log (934998967791 / 1000000000000) ∧
    -Real.log (934998967791 / 1000000000000) ≤ (33604927 / 500000000) := by
  have h := checkLog_sound (w := (65001032209 / 1934998967791)) (n := 12)
    (lo := (67209853 / 1000000000)) (hi := (33604927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 934998967791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 934998967791) = 1/(934998967791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12367 : Bounds (-33604927 / 500000000) (-67209853 / 1000000000) (Real.log (934998967791 / 1000000000000)) := by
  have h := reflection_log_12367_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12368_neg : (66646173 / 1000000000) ≤ -Real.log (935526157111 / 1000000000000) ∧
    -Real.log (935526157111 / 1000000000000) ≤ (33323087 / 500000000) := by
  have h := checkLog_sound (w := (64473842889 / 1935526157111)) (n := 12)
    (lo := (66646173 / 1000000000)) (hi := (33323087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 935526157111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 935526157111) = 1/(935526157111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12368 : Bounds (-33323087 / 500000000) (-66646173 / 1000000000) (Real.log (935526157111 / 1000000000000)) := by
  have h := reflection_log_12368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12369_neg : (129797669 / 250000000) ≤ -Real.log (100000000000 / 168066689631) ∧
    -Real.log (100000000000 / 168066689631) ≤ (519190677 / 1000000000) := by
  have h := checkLog_sound (w := (68066689631 / 268066689631)) (n := 12)
    (lo := (129797669 / 250000000)) (hi := (519190677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168066689631 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168066689631 / 100000000000) = 1/(100000000000 / 168066689631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12369 : Bounds (129797669 / 250000000) (519190677 / 1000000000) (Real.log (168066689631 / 100000000000)) := by
  have h := reflection_log_12369_neg
  have he : Real.log (168066689631 / 100000000000) = -Real.log (100000000000 / 168066689631) := by
    rw [show ((168066689631 / 100000000000) : ℝ) = ((100000000000 / 168066689631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12370_neg : (521406097 / 1000000000) ≤ -Real.log (500000000000 / 842197203667) ∧
    -Real.log (500000000000 / 842197203667) ≤ (260703049 / 500000000) := by
  have h := checkLog_sound (w := (342197203667 / 1342197203667)) (n := 12)
    (lo := (521406097 / 1000000000)) (hi := (260703049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((842197203667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(842197203667 / 500000000000) = 1/(500000000000 / 842197203667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12370 : Bounds (521406097 / 1000000000) (260703049 / 500000000) (Real.log (842197203667 / 500000000000)) := by
  have h := reflection_log_12370_neg
  have he : Real.log (842197203667 / 500000000000) = -Real.log (500000000000 / 842197203667) := by
    rw [show ((842197203667 / 500000000000) : ℝ) = ((500000000000 / 842197203667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12371_neg : (1061619959 / 1000000000) ≤ -Real.log (125000000000 / 361381322957) ∧
    -Real.log (125000000000 / 361381322957) ≤ (1061619961 / 1000000000) := by
  have h := checkLog_sound (w := (111381322957 / 611381322957)) (n := 12)
    (lo := (368472779 / 1000000000)) (hi := (18423639 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361381322957 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(361381322957 / 250000000000) = 1/(125000000000 / 361381322957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12371 : Bounds (1061619959 / 1000000000) (1061619961 / 1000000000) (Real.log (361381322957 / 125000000000)) := by
  have h := reflection_log_12371_neg
  have he : Real.log (361381322957 / 125000000000) = -Real.log (125000000000 / 361381322957) := by
    rw [show ((361381322957 / 125000000000) : ℝ) = ((125000000000 / 361381322957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12372_neg : (10642401 / 10000000) ≤ -Real.log (62500000000 / 181164717349) ∧
    -Real.log (62500000000 / 181164717349) ≤ (532120051 / 500000000) := by
  have h := checkLog_sound (w := (56164717349 / 306164717349)) (n := 12)
    (lo := (9277323 / 25000000)) (hi := (371092921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181164717349 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(181164717349 / 125000000000) = 1/(62500000000 / 181164717349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12372 : Bounds (10642401 / 10000000) (532120051 / 500000000) (Real.log (181164717349 / 62500000000)) := by
  have h := reflection_log_12372_neg
  have he : Real.log (181164717349 / 62500000000) = -Real.log (62500000000 / 181164717349) := by
    rw [show ((181164717349 / 62500000000) : ℝ) = ((62500000000 / 181164717349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12373_neg : (49679117 / 125000000) ≤ -Real.log (125 / 186) ∧
    -Real.log (125 / 186) ≤ (397432937 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 311)) (n := 12)
    (lo := (49679117 / 125000000)) (hi := (397432937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186 / 125) = 1/(125 / 186) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12373 : Bounds (49679117 / 125000000) (397432937 / 1000000000) (Real.log (186 / 125)) := by
  have h := reflection_log_12373_neg
  have he : Real.log (186 / 125) = -Real.log (125 / 186) := by
    rw [show ((186 / 125) : ℝ) = ((125 / 186) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12374_neg : (669430653 / 1000000000) ≤ -Real.log (64 / 125) ∧
    -Real.log (64 / 125) ≤ (334715327 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 64) = 1/(64 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12374 : Bounds (-334715327 / 500000000) (-669430653 / 1000000000) (Real.log (64 / 125)) := by
  have h := reflection_log_12374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12375_neg : (12197 / 25000000) ≤ -Real.log (125000 / 125061) ∧
    -Real.log (125000 / 125061) ≤ (487881 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 250061)) (n := 12)
    (lo := (12197 / 25000000)) (hi := (487881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125061 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125061 / 125000) = 1/(125000 / 125061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12375 : Bounds (12197 / 25000000) (487881 / 1000000000) (Real.log (125061 / 125000)) := by
  have h := reflection_log_12375_neg
  have he : Real.log (125061 / 125000) = -Real.log (125000 / 125061) := by
    rw [show ((125061 / 125000) : ℝ) = ((125000 / 125061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12376_neg : (488119 / 1000000000) ≤ -Real.log (124939 / 125000) ∧
    -Real.log (124939 / 125000) ≤ (12203 / 25000000) := by
  have h := checkLog_sound (w := (61 / 249939)) (n := 12)
    (lo := (488119 / 1000000000)) (hi := (12203 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124939) = 1/(124939 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12376 : Bounds (-12203 / 25000000) (-488119 / 1000000000) (Real.log (124939 / 125000)) := by
  have h := reflection_log_12376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12377_neg : (113364159 / 500000000) ≤ -Real.log (1000000 / 1254489) ∧
    -Real.log (1000000 / 1254489) ≤ (226728319 / 1000000000) := by
  have h := checkLog_sound (w := (254489 / 2254489)) (n := 12)
    (lo := (113364159 / 500000000)) (hi := (226728319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254489 / 1000000) = 1/(1000000 / 1254489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12377 : Bounds (113364159 / 500000000) (226728319 / 1000000000) (Real.log (1254489 / 1000000)) := by
  have h := reflection_log_12377_neg
  have he : Real.log (1254489 / 1000000) = -Real.log (1000000 / 1254489) := by
    rw [show ((1254489 / 1000000) : ℝ) = ((1000000 / 1254489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12378_neg : (293685389 / 1000000000) ≤ -Real.log (745511 / 1000000) ∧
    -Real.log (745511 / 1000000) ≤ (29368539 / 100000000) := by
  have h := checkLog_sound (w := (254489 / 1745511)) (n := 12)
    (lo := (293685389 / 1000000000)) (hi := (29368539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745511) = 1/(745511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12378 : Bounds (-29368539 / 100000000) (-293685389 / 1000000000) (Real.log (745511 / 1000000)) := by
  have h := reflection_log_12378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12379_neg : (14222163 / 62500000) ≤ -Real.log (500000 / 627763) ∧
    -Real.log (500000 / 627763) ≤ (227554609 / 1000000000) := by
  have h := checkLog_sound (w := (127763 / 1127763)) (n := 12)
    (lo := (14222163 / 62500000)) (hi := (227554609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627763 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627763 / 500000) = 1/(500000 / 627763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12379 : Bounds (14222163 / 62500000) (227554609 / 1000000000) (Real.log (627763 / 500000)) := by
  have h := reflection_log_12379_neg
  have he : Real.log (627763 / 500000) = -Real.log (500000 / 627763) := by
    rw [show ((627763 / 500000) : ℝ) = ((500000 / 627763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12380_neg : (5901547 / 20000000) ≤ -Real.log (372237 / 500000) ∧
    -Real.log (372237 / 500000) ≤ (295077351 / 1000000000) := by
  have h := checkLog_sound (w := (127763 / 872237)) (n := 12)
    (lo := (5901547 / 20000000)) (hi := (295077351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 372237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 372237) = 1/(372237 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12380 : Bounds (-295077351 / 1000000000) (-5901547 / 20000000) (Real.log (372237 / 500000)) := by
  have h := reflection_log_12380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12381_neg : (67522741 / 1000000000) ≤ -Real.log (233676615831 / 250000000000) ∧
    -Real.log (233676615831 / 250000000000) ≤ (33761371 / 500000000) := by
  have h := checkLog_sound (w := (16323384169 / 483676615831)) (n := 12)
    (lo := (67522741 / 1000000000)) (hi := (33761371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233676615831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233676615831) = 1/(233676615831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12381 : Bounds (-33761371 / 500000000) (-67522741 / 1000000000) (Real.log (233676615831 / 250000000000)) := by
  have h := reflection_log_12381_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12382_neg : (66957071 / 1000000000) ≤ -Real.log (935235348879 / 1000000000000) ∧
    -Real.log (935235348879 / 1000000000000) ≤ (4184817 / 62500000) := by
  have h := checkLog_sound (w := (64764651121 / 1935235348879)) (n := 12)
    (lo := (66957071 / 1000000000)) (hi := (4184817 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 935235348879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 935235348879) = 1/(935235348879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12382 : Bounds (-4184817 / 62500000) (-66957071 / 1000000000) (Real.log (935235348879 / 1000000000000)) := by
  have h := reflection_log_12382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12383_neg : (130103427 / 250000000) ≤ -Real.log (125000000000 / 210340457753) ∧
    -Real.log (125000000000 / 210340457753) ≤ (520413709 / 1000000000) := by
  have h := checkLog_sound (w := (85340457753 / 335340457753)) (n := 12)
    (lo := (130103427 / 250000000)) (hi := (520413709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210340457753 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210340457753 / 125000000000) = 1/(125000000000 / 210340457753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12383 : Bounds (130103427 / 250000000) (520413709 / 1000000000) (Real.log (210340457753 / 125000000000)) := by
  have h := reflection_log_12383_neg
  have he : Real.log (210340457753 / 125000000000) = -Real.log (125000000000 / 210340457753) := by
    rw [show ((210340457753 / 125000000000) : ℝ) = ((125000000000 / 210340457753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12384_neg : (261315979 / 500000000) ≤ -Real.log (125000000000 / 210807563461) ∧
    -Real.log (125000000000 / 210807563461) ≤ (522631959 / 1000000000) := by
  have h := checkLog_sound (w := (85807563461 / 335807563461)) (n := 12)
    (lo := (261315979 / 500000000)) (hi := (522631959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210807563461 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210807563461 / 125000000000) = 1/(125000000000 / 210807563461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12384 : Bounds (261315979 / 500000000) (522631959 / 1000000000) (Real.log (210807563461 / 125000000000)) := by
  have h := reflection_log_12384_neg
  have he : Real.log (210807563461 / 125000000000) = -Real.log (125000000000 / 210807563461) := by
    rw [show ((210807563461 / 125000000000) : ℝ) = ((125000000000 / 210807563461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12385_neg : (10642401 / 10000000) ≤ -Real.log (500000000000 / 1449317738791) ∧
    -Real.log (500000000000 / 1449317738791) ≤ (532120051 / 500000000) := by
  have h := checkLog_sound (w := (449317738791 / 2449317738791)) (n := 12)
    (lo := (9277323 / 25000000)) (hi := (371092921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1449317738791 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1449317738791 / 1000000000000) = 1/(500000000000 / 1449317738791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12385 : Bounds (10642401 / 10000000) (532120051 / 500000000) (Real.log (1449317738791 / 500000000000)) := by
  have h := reflection_log_12385_neg
  have he : Real.log (1449317738791 / 500000000000) = -Real.log (500000000000 / 1449317738791) := by
    rw [show ((1449317738791 / 500000000000) : ℝ) = ((500000000000 / 1449317738791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12386_neg : (1066863589 / 1000000000) ≤ -Real.log (32 / 93) ∧
    -Real.log (32 / 93) ≤ (1066863591 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 157)) (n := 12)
    (lo := (373716409 / 1000000000)) (hi := (37371641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 64) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(93 / 64) = 1/(32 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12386 : Bounds (1066863589 / 1000000000) (1066863591 / 1000000000) (Real.log (93 / 32)) := by
  have h := reflection_log_12386_neg
  have he : Real.log (93 / 32) = -Real.log (32 / 93) := by
    rw [show ((93 / 32) : ℝ) = ((32 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12387_neg : (398104753 / 1000000000) ≤ -Real.log (1000 / 1489) ∧
    -Real.log (1000 / 1489) ≤ (199052377 / 500000000) := by
  have h := checkLog_sound (w := (489 / 2489)) (n := 12)
    (lo := (398104753 / 1000000000)) (hi := (199052377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489 / 1000) = 1/(1000 / 1489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12387 : Bounds (398104753 / 1000000000) (199052377 / 500000000) (Real.log (1489 / 1000)) := by
  have h := reflection_log_12387_neg
  have he : Real.log (1489 / 1000) = -Real.log (1000 / 1489) := by
    rw [show ((1489 / 1000) : ℝ) = ((1000 / 1489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12388_neg : (83923211 / 125000000) ≤ -Real.log (511 / 1000) ∧
    -Real.log (511 / 1000) ≤ (671385689 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 1511)) (n := 12)
    (lo := (83923211 / 125000000)) (hi := (671385689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 511) = 1/(511 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12388 : Bounds (-671385689 / 1000000000) (-83923211 / 125000000) (Real.log (511 / 1000)) := by
  have h := reflection_log_12388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12389_neg : (6111 / 12500000) ≤ -Real.log (1000000 / 1000489) ∧
    -Real.log (1000000 / 1000489) ≤ (488881 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 2000489)) (n := 12)
    (lo := (6111 / 12500000)) (hi := (488881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000489 / 1000000) = 1/(1000000 / 1000489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12389 : Bounds (6111 / 12500000) (488881 / 1000000000) (Real.log (1000489 / 1000000)) := by
  have h := reflection_log_12389_neg
  have he : Real.log (1000489 / 1000000) = -Real.log (1000000 / 1000489) := by
    rw [show ((1000489 / 1000000) : ℝ) = ((1000000 / 1000489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12390_neg : (489119 / 1000000000) ≤ -Real.log (999511 / 1000000) ∧
    -Real.log (999511 / 1000000) ≤ (3057 / 6250000) := by
  have h := checkLog_sound (w := (489 / 1999511)) (n := 12)
    (lo := (489119 / 1000000000)) (hi := (3057 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999511) = 1/(999511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12390 : Bounds (-3057 / 6250000) (-489119 / 1000000000) (Real.log (999511 / 1000000)) := by
  have h := reflection_log_12390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12391_neg : (227184973 / 1000000000) ≤ -Real.log (500000 / 627531) ∧
    -Real.log (500000 / 627531) ≤ (113592487 / 500000000) := by
  have h := checkLog_sound (w := (127531 / 1127531)) (n := 12)
    (lo := (227184973 / 1000000000)) (hi := (113592487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627531 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627531 / 500000) = 1/(500000 / 627531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12391 : Bounds (227184973 / 1000000000) (113592487 / 500000000) (Real.log (627531 / 500000)) := by
  have h := reflection_log_12391_neg
  have he : Real.log (627531 / 500000) = -Real.log (500000 / 627531) := by
    rw [show ((627531 / 500000) : ℝ) = ((500000 / 627531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12392_neg : (58890857 / 200000000) ≤ -Real.log (372469 / 500000) ∧
    -Real.log (372469 / 500000) ≤ (147227143 / 500000000) := by
  have h := checkLog_sound (w := (127531 / 872469)) (n := 12)
    (lo := (58890857 / 200000000)) (hi := (147227143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 372469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 372469) = 1/(372469 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12392 : Bounds (-147227143 / 500000000) (-58890857 / 200000000) (Real.log (372469 / 500000)) := by
  have h := reflection_log_12392_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12393_neg : (114005841 / 500000000) ≤ -Real.log (10000 / 12561) ∧
    -Real.log (10000 / 12561) ≤ (228011683 / 1000000000) := by
  have h := checkLog_sound (w := (2561 / 22561)) (n := 12)
    (lo := (114005841 / 500000000)) (hi := (228011683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12561 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12561 / 10000) = 1/(10000 / 12561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12393 : Bounds (114005841 / 500000000) (228011683 / 1000000000) (Real.log (12561 / 10000)) := by
  have h := reflection_log_12393_neg
  have he : Real.log (12561 / 10000) = -Real.log (10000 / 12561) := by
    rw [show ((12561 / 10000) : ℝ) = ((10000 / 12561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12394_neg : (295848661 / 1000000000) ≤ -Real.log (7439 / 10000) ∧
    -Real.log (7439 / 10000) ≤ (147924331 / 500000000) := by
  have h := checkLog_sound (w := (2561 / 17439)) (n := 12)
    (lo := (295848661 / 1000000000)) (hi := (147924331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7439) = 1/(7439 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12394 : Bounds (-147924331 / 500000000) (-295848661 / 1000000000) (Real.log (7439 / 10000)) := by
  have h := reflection_log_12394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12395_neg : (67836979 / 1000000000) ≤ -Real.log (93441279 / 100000000) ∧
    -Real.log (93441279 / 100000000) ≤ (3391849 / 50000000) := by
  have h := checkLog_sound (w := (6558721 / 193441279)) (n := 12)
    (lo := (67836979 / 1000000000)) (hi := (3391849 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 93441279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 93441279) = 1/(93441279 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12395 : Bounds (-3391849 / 50000000) (-67836979 / 1000000000) (Real.log (93441279 / 100000000)) := by
  have h := reflection_log_12395_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12396_neg : (67269311 / 1000000000) ≤ -Real.log (233735844039 / 250000000000) ∧
    -Real.log (233735844039 / 250000000000) ≤ (1051083 / 15625000) := by
  have h := checkLog_sound (w := (16264155961 / 483735844039)) (n := 12)
    (lo := (67269311 / 1000000000)) (hi := (1051083 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233735844039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233735844039) = 1/(233735844039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12396 : Bounds (-1051083 / 15625000) (-67269311 / 1000000000) (Real.log (233735844039 / 250000000000)) := by
  have h := reflection_log_12396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12397_neg : (521639259 / 1000000000) ≤ -Real.log (500000000000 / 842393595171) ∧
    -Real.log (500000000000 / 842393595171) ≤ (26081963 / 50000000) := by
  have h := checkLog_sound (w := (342393595171 / 1342393595171)) (n := 12)
    (lo := (521639259 / 1000000000)) (hi := (26081963 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((842393595171 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(842393595171 / 500000000000) = 1/(500000000000 / 842393595171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12397 : Bounds (521639259 / 1000000000) (26081963 / 50000000) (Real.log (842393595171 / 500000000000)) := by
  have h := reflection_log_12397_neg
  have he : Real.log (842393595171 / 500000000000) = -Real.log (500000000000 / 842393595171) := by
    rw [show ((842393595171 / 500000000000) : ℝ) = ((500000000000 / 842393595171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12398_neg : (65482543 / 125000000) ≤ -Real.log (250000000000 / 422133351257) ∧
    -Real.log (250000000000 / 422133351257) ≤ (104772069 / 200000000) := by
  have h := checkLog_sound (w := (172133351257 / 672133351257)) (n := 12)
    (lo := (65482543 / 125000000)) (hi := (104772069 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422133351257 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422133351257 / 250000000000) = 1/(250000000000 / 422133351257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12398 : Bounds (65482543 / 125000000) (104772069 / 200000000) (Real.log (422133351257 / 250000000000)) := by
  have h := reflection_log_12398_neg
  have he : Real.log (422133351257 / 250000000000) = -Real.log (250000000000 / 422133351257) := by
    rw [show ((422133351257 / 250000000000) : ℝ) = ((250000000000 / 422133351257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12399_neg : (1069490441 / 1000000000) ≤ -Real.log (500000000000 / 1456947162427) ∧
    -Real.log (500000000000 / 1456947162427) ≤ (1069490443 / 1000000000) := by
  have h := checkLog_sound (w := (456947162427 / 2456947162427)) (n := 12)
    (lo := (376343261 / 1000000000)) (hi := (188171631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1456947162427 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1456947162427 / 1000000000000) = 1/(500000000000 / 1456947162427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12399 : Bounds (1069490441 / 1000000000) (1069490443 / 1000000000) (Real.log (1456947162427 / 500000000000)) := by
  have h := reflection_log_12399_neg
  have he : Real.log (1456947162427 / 500000000000) = -Real.log (500000000000 / 1456947162427) := by
    rw [show ((1456947162427 / 500000000000) : ℝ) = ((500000000000 / 1456947162427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12400_neg : (398776119 / 1000000000) ≤ -Real.log (100 / 149) ∧
    -Real.log (100 / 149) ≤ (9969403 / 25000000) := by
  have h := checkLog_sound (w := (49 / 249)) (n := 12)
    (lo := (398776119 / 1000000000)) (hi := (9969403 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149 / 100) = 1/(100 / 149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12400 : Bounds (398776119 / 1000000000) (9969403 / 25000000) (Real.log (149 / 100)) := by
  have h := reflection_log_12400_neg
  have he : Real.log (149 / 100) = -Real.log (100 / 149) := by
    rw [show ((149 / 100) : ℝ) = ((100 / 149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12401_neg : (673344553 / 1000000000) ≤ -Real.log (51 / 100) ∧
    -Real.log (51 / 100) ≤ (336672277 / 500000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 51) = 1/(51 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12401 : Bounds (-336672277 / 500000000) (-673344553 / 1000000000) (Real.log (51 / 100)) := by
  have h := reflection_log_12401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12402_neg : (489879 / 1000000000) ≤ -Real.log (100000 / 100049) ∧
    -Real.log (100000 / 100049) ≤ (12247 / 25000000) := by
  have h := checkLog_sound (w := (49 / 200049)) (n := 12)
    (lo := (489879 / 1000000000)) (hi := (12247 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100049 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100049 / 100000) = 1/(100000 / 100049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12402 : Bounds (489879 / 1000000000) (12247 / 25000000) (Real.log (100049 / 100000)) := by
  have h := reflection_log_12402_neg
  have he : Real.log (100049 / 100000) = -Real.log (100000 / 100049) := by
    rw [show ((100049 / 100000) : ℝ) = ((100000 / 100049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12403_neg : (12253 / 25000000) ≤ -Real.log (99951 / 100000) ∧
    -Real.log (99951 / 100000) ≤ (490121 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 199951)) (n := 12)
    (lo := (12253 / 25000000)) (hi := (490121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99951) = 1/(99951 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12403 : Bounds (-490121 / 1000000000) (-12253 / 25000000) (Real.log (99951 / 100000)) := by
  have h := reflection_log_12403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12404_neg : (11382071 / 50000000) ≤ -Real.log (200000 / 251127) ∧
    -Real.log (200000 / 251127) ≤ (227641421 / 1000000000) := by
  have h := checkLog_sound (w := (51127 / 451127)) (n := 12)
    (lo := (11382071 / 50000000)) (hi := (227641421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251127 / 200000) = 1/(200000 / 251127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12404 : Bounds (11382071 / 50000000) (227641421 / 1000000000) (Real.log (251127 / 200000)) := by
  have h := reflection_log_12404_neg
  have he : Real.log (251127 / 200000) = -Real.log (200000 / 251127) := by
    rw [show ((251127 / 200000) : ℝ) = ((200000 / 251127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12405_neg : (295223773 / 1000000000) ≤ -Real.log (148873 / 200000) ∧
    -Real.log (148873 / 200000) ≤ (147611887 / 500000000) := by
  have h := checkLog_sound (w := (51127 / 348873)) (n := 12)
    (lo := (295223773 / 1000000000)) (hi := (147611887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148873) = 1/(148873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12405 : Bounds (-147611887 / 500000000) (-295223773 / 1000000000) (Real.log (148873 / 200000)) := by
  have h := reflection_log_12405_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12406_neg : (57117137 / 250000000) ≤ -Real.log (500000 / 628337) ∧
    -Real.log (500000 / 628337) ≤ (228468549 / 1000000000) := by
  have h := checkLog_sound (w := (128337 / 1128337)) (n := 12)
    (lo := (57117137 / 250000000)) (hi := (228468549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628337 / 500000) = 1/(500000 / 628337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12406 : Bounds (57117137 / 250000000) (228468549 / 1000000000) (Real.log (628337 / 500000)) := by
  have h := reflection_log_12406_neg
  have he : Real.log (628337 / 500000) = -Real.log (500000 / 628337) := by
    rw [show ((628337 / 500000) : ℝ) = ((500000 / 628337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12407_neg : (37077571 / 125000000) ≤ -Real.log (371663 / 500000) ∧
    -Real.log (371663 / 500000) ≤ (296620569 / 1000000000) := by
  have h := checkLog_sound (w := (128337 / 871663)) (n := 12)
    (lo := (37077571 / 125000000)) (hi := (296620569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371663) = 1/(371663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12407 : Bounds (-296620569 / 1000000000) (-37077571 / 125000000) (Real.log (371663 / 500000)) := by
  have h := reflection_log_12407_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12408_neg : (3407601 / 50000000) ≤ -Real.log (233529614431 / 250000000000) ∧
    -Real.log (233529614431 / 250000000000) ≤ (68152021 / 1000000000) := by
  have h := checkLog_sound (w := (16470385569 / 483529614431)) (n := 12)
    (lo := (3407601 / 50000000)) (hi := (68152021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233529614431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233529614431) = 1/(233529614431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12408 : Bounds (-68152021 / 1000000000) (-3407601 / 50000000) (Real.log (233529614431 / 250000000000)) := by
  have h := reflection_log_12408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12409_neg : (4223897 / 62500000) ≤ -Real.log (37386029871 / 40000000000) ∧
    -Real.log (37386029871 / 40000000000) ≤ (67582353 / 1000000000) := by
  have h := checkLog_sound (w := (2613970129 / 77386029871)) (n := 12)
    (lo := (4223897 / 62500000)) (hi := (67582353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37386029871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37386029871) = 1/(37386029871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12409 : Bounds (-67582353 / 1000000000) (-4223897 / 62500000) (Real.log (37386029871 / 40000000000)) := by
  have h := reflection_log_12409_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12410_neg : (522865193 / 1000000000) ≤ -Real.log (500000000000 / 843426947801) ∧
    -Real.log (500000000000 / 843426947801) ≤ (261432597 / 500000000) := by
  have h := checkLog_sound (w := (343426947801 / 1343426947801)) (n := 12)
    (lo := (522865193 / 1000000000)) (hi := (261432597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843426947801 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843426947801 / 500000000000) = 1/(500000000000 / 843426947801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12410 : Bounds (522865193 / 1000000000) (261432597 / 500000000) (Real.log (843426947801 / 500000000000)) := by
  have h := reflection_log_12410_neg
  have he : Real.log (843426947801 / 500000000000) = -Real.log (500000000000 / 843426947801) := by
    rw [show ((843426947801 / 500000000000) : ℝ) = ((500000000000 / 843426947801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12411_neg : (525089117 / 1000000000) ≤ -Real.log (250000000000 / 422652375943) ∧
    -Real.log (250000000000 / 422652375943) ≤ (262544559 / 500000000) := by
  have h := checkLog_sound (w := (172652375943 / 672652375943)) (n := 12)
    (lo := (525089117 / 1000000000)) (hi := (262544559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422652375943 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422652375943 / 250000000000) = 1/(250000000000 / 422652375943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12411 : Bounds (525089117 / 1000000000) (262544559 / 500000000) (Real.log (422652375943 / 250000000000)) := by
  have h := reflection_log_12411_neg
  have he : Real.log (422652375943 / 250000000000) = -Real.log (250000000000 / 422652375943) := by
    rw [show ((422652375943 / 250000000000) : ℝ) = ((250000000000 / 422652375943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12412_neg : (1069490441 / 1000000000) ≤ -Real.log (250000000000 / 728473581213) ∧
    -Real.log (250000000000 / 728473581213) ≤ (1069490443 / 1000000000) := by
  have h := checkLog_sound (w := (228473581213 / 1228473581213)) (n := 12)
    (lo := (376343261 / 1000000000)) (hi := (188171631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728473581213 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(728473581213 / 500000000000) = 1/(250000000000 / 728473581213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12412 : Bounds (1069490441 / 1000000000) (1069490443 / 1000000000) (Real.log (728473581213 / 250000000000)) := by
  have h := reflection_log_12412_neg
  have he : Real.log (728473581213 / 250000000000) = -Real.log (250000000000 / 728473581213) := by
    rw [show ((728473581213 / 250000000000) : ℝ) = ((250000000000 / 728473581213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12413_neg : (33503771 / 31250000) ≤ -Real.log (250000000000 / 730392156863) ∧
    -Real.log (250000000000 / 730392156863) ≤ (536060337 / 500000000) := by
  have h := checkLog_sound (w := (230392156863 / 1230392156863)) (n := 12)
    (lo := (94743373 / 250000000)) (hi := (378973493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730392156863 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(730392156863 / 500000000000) = 1/(250000000000 / 730392156863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12413 : Bounds (33503771 / 31250000) (536060337 / 500000000) (Real.log (730392156863 / 250000000000)) := by
  have h := reflection_log_12413_neg
  have he : Real.log (730392156863 / 250000000000) = -Real.log (250000000000 / 730392156863) := by
    rw [show ((730392156863 / 250000000000) : ℝ) = ((250000000000 / 730392156863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12414_neg : (79889407 / 200000000) ≤ -Real.log (1000 / 1491) ∧
    -Real.log (1000 / 1491) ≤ (99861759 / 250000000) := by
  have h := checkLog_sound (w := (491 / 2491)) (n := 12)
    (lo := (79889407 / 200000000)) (hi := (99861759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1491 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1491 / 1000) = 1/(1000 / 1491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12414 : Bounds (79889407 / 200000000) (99861759 / 250000000) (Real.log (1491 / 1000)) := by
  have h := reflection_log_12414_neg
  have he : Real.log (1491 / 1000) = -Real.log (1000 / 1491) := by
    rw [show ((1491 / 1000) : ℝ) = ((1000 / 1491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12415_neg : (337653631 / 500000000) ≤ -Real.log (509 / 1000) ∧
    -Real.log (509 / 1000) ≤ (675307263 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 1509)) (n := 12)
    (lo := (337653631 / 500000000)) (hi := (675307263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 509) = 1/(509 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12415 : Bounds (-675307263 / 1000000000) (-337653631 / 500000000) (Real.log (509 / 1000)) := by
  have h := reflection_log_12415_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0194 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12416_neg : (490879 / 1000000000) ≤ -Real.log (1000000 / 1000491) ∧
    -Real.log (1000000 / 1000491) ≤ (767 / 1562500) := by
  have h := checkLog_sound (w := (491 / 2000491)) (n := 12)
    (lo := (490879 / 1000000000)) (hi := (767 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000491 / 1000000) = 1/(1000000 / 1000491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12416 : Bounds (490879 / 1000000000) (767 / 1562500) (Real.log (1000491 / 1000000)) := by
  have h := reflection_log_12416_neg
  have he : Real.log (1000491 / 1000000) = -Real.log (1000000 / 1000491) := by
    rw [show ((1000491 / 1000000) : ℝ) = ((1000000 / 1000491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12417_neg : (6139 / 12500000) ≤ -Real.log (999509 / 1000000) ∧
    -Real.log (999509 / 1000000) ≤ (491121 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 1999509)) (n := 12)
    (lo := (6139 / 12500000)) (hi := (491121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999509) = 1/(999509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12417 : Bounds (-491121 / 1000000000) (-6139 / 12500000) (Real.log (999509 / 1000000)) := by
  have h := reflection_log_12417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12418_neg : (228097659 / 1000000000) ≤ -Real.log (62500 / 78513) ∧
    -Real.log (62500 / 78513) ≤ (11404883 / 50000000) := by
  have h := checkLog_sound (w := (16013 / 141013)) (n := 12)
    (lo := (228097659 / 1000000000)) (hi := (11404883 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78513 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78513 / 62500) = 1/(62500 / 78513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12418 : Bounds (228097659 / 1000000000) (11404883 / 50000000) (Real.log (78513 / 62500)) := by
  have h := reflection_log_12418_neg
  have he : Real.log (78513 / 62500) = -Real.log (62500 / 78513) := by
    rw [show ((78513 / 62500) : ℝ) = ((62500 / 78513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12419_neg : (295993853 / 1000000000) ≤ -Real.log (46487 / 62500) ∧
    -Real.log (46487 / 62500) ≤ (147996927 / 500000000) := by
  have h := checkLog_sound (w := (16013 / 108987)) (n := 12)
    (lo := (295993853 / 1000000000)) (hi := (147996927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46487) = 1/(46487 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12419 : Bounds (-147996927 / 500000000) (-295993853 / 1000000000) (Real.log (46487 / 62500)) := by
  have h := reflection_log_12419_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12420_neg : (114463 / 500000) ≤ -Real.log (1000000 / 1257249) ∧
    -Real.log (1000000 / 1257249) ≤ (228926001 / 1000000000) := by
  have h := checkLog_sound (w := (257249 / 2257249)) (n := 12)
    (lo := (114463 / 500000)) (hi := (228926001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257249 / 1000000) = 1/(1000000 / 1257249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12420 : Bounds (114463 / 500000) (228926001 / 1000000000) (Real.log (1257249 / 1000000)) := by
  have h := reflection_log_12420_neg
  have he : Real.log (1257249 / 1000000) = -Real.log (1000000 / 1257249) := by
    rw [show ((1257249 / 1000000) : ℝ) = ((1000000 / 1257249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12421_neg : (148697209 / 500000000) ≤ -Real.log (742751 / 1000000) ∧
    -Real.log (742751 / 1000000) ≤ (297394419 / 1000000000) := by
  have h := checkLog_sound (w := (257249 / 1742751)) (n := 12)
    (lo := (148697209 / 500000000)) (hi := (297394419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742751) = 1/(742751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12421 : Bounds (-297394419 / 1000000000) (-148697209 / 500000000) (Real.log (742751 / 1000000)) := by
  have h := reflection_log_12421_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12422_neg : (68468417 / 1000000000) ≤ -Real.log (933822951999 / 1000000000000) ∧
    -Real.log (933822951999 / 1000000000000) ≤ (34234209 / 500000000) := by
  have h := checkLog_sound (w := (66177048001 / 1933822951999)) (n := 12)
    (lo := (68468417 / 1000000000)) (hi := (34234209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 933822951999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 933822951999) = 1/(933822951999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12422 : Bounds (-34234209 / 500000000) (-68468417 / 1000000000) (Real.log (933822951999 / 1000000000000)) := by
  have h := reflection_log_12422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12423_neg : (67896193 / 1000000000) ≤ -Real.log (3649833831 / 3906250000) ∧
    -Real.log (3649833831 / 3906250000) ≤ (33948097 / 500000000) := by
  have h := checkLog_sound (w := (256416169 / 7556083831)) (n := 12)
    (lo := (67896193 / 1000000000)) (hi := (33948097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3649833831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3649833831) = 1/(3649833831 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12423 : Bounds (-33948097 / 500000000) (-67896193 / 1000000000) (Real.log (3649833831 / 3906250000)) := by
  have h := reflection_log_12423_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12424_neg : (65511439 / 125000000) ≤ -Real.log (125000000000 / 211115473143) ∧
    -Real.log (125000000000 / 211115473143) ≤ (524091513 / 1000000000) := by
  have h := checkLog_sound (w := (86115473143 / 336115473143)) (n := 12)
    (lo := (65511439 / 125000000)) (hi := (524091513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211115473143 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211115473143 / 125000000000) = 1/(125000000000 / 211115473143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12424 : Bounds (65511439 / 125000000) (524091513 / 1000000000) (Real.log (211115473143 / 125000000000)) := by
  have h := reflection_log_12424_neg
  have he : Real.log (211115473143 / 125000000000) = -Real.log (125000000000 / 211115473143) := by
    rw [show ((211115473143 / 125000000000) : ℝ) = ((125000000000 / 211115473143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12425_neg : (263160209 / 500000000) ≤ -Real.log (125000000000 / 211586554579) ∧
    -Real.log (125000000000 / 211586554579) ≤ (526320419 / 1000000000) := by
  have h := checkLog_sound (w := (86586554579 / 336586554579)) (n := 12)
    (lo := (263160209 / 500000000)) (hi := (526320419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211586554579 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211586554579 / 125000000000) = 1/(125000000000 / 211586554579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12425 : Bounds (263160209 / 500000000) (526320419 / 1000000000) (Real.log (211586554579 / 125000000000)) := by
  have h := reflection_log_12425_neg
  have he : Real.log (211586554579 / 125000000000) = -Real.log (125000000000 / 211586554579) := by
    rw [show ((211586554579 / 125000000000) : ℝ) = ((125000000000 / 211586554579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12426_neg : (33503771 / 31250000) ≤ -Real.log (20000000000 / 58431372549) ∧
    -Real.log (20000000000 / 58431372549) ≤ (536060337 / 500000000) := by
  have h := checkLog_sound (w := (18431372549 / 98431372549)) (n := 12)
    (lo := (94743373 / 250000000)) (hi := (378973493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58431372549 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(58431372549 / 40000000000) = 1/(20000000000 / 58431372549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12426 : Bounds (33503771 / 31250000) (536060337 / 500000000) (Real.log (58431372549 / 20000000000)) := by
  have h := reflection_log_12426_neg
  have he : Real.log (58431372549 / 20000000000) = -Real.log (20000000000 / 58431372549) := by
    rw [show ((58431372549 / 20000000000) : ℝ) = ((20000000000 / 58431372549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12427_neg : (1074754297 / 1000000000) ≤ -Real.log (3125000000 / 9153978389) ∧
    -Real.log (3125000000 / 9153978389) ≤ (1074754299 / 1000000000) := by
  have h := checkLog_sound (w := (2903978389 / 15403978389)) (n := 12)
    (lo := (381607117 / 1000000000)) (hi := (190803559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9153978389 / 6250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9153978389 / 6250000000) = 1/(3125000000 / 9153978389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12427 : Bounds (1074754297 / 1000000000) (1074754299 / 1000000000) (Real.log (9153978389 / 3125000000)) := by
  have h := reflection_log_12427_neg
  have he : Real.log (9153978389 / 3125000000) = -Real.log (3125000000 / 9153978389) := by
    rw [show ((9153978389 / 3125000000) : ℝ) = ((3125000000 / 9153978389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12428_neg : (400117501 / 1000000000) ≤ -Real.log (250 / 373) ∧
    -Real.log (250 / 373) ≤ (200058751 / 500000000) := by
  have h := checkLog_sound (w := (123 / 623)) (n := 12)
    (lo := (400117501 / 1000000000)) (hi := (200058751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373 / 250) = 1/(250 / 373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12428 : Bounds (400117501 / 1000000000) (200058751 / 500000000) (Real.log (373 / 250)) := by
  have h := reflection_log_12428_neg
  have he : Real.log (373 / 250) = -Real.log (250 / 373) := by
    rw [show ((373 / 250) : ℝ) = ((250 / 373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12429_neg : (677273831 / 1000000000) ≤ -Real.log (127 / 250) ∧
    -Real.log (127 / 250) ≤ (84659229 / 125000000) := by
  have h := checkLog_sound (w := (123 / 377)) (n := 12)
    (lo := (677273831 / 1000000000)) (hi := (84659229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 127) = 1/(127 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12429 : Bounds (-84659229 / 125000000) (-677273831 / 1000000000) (Real.log (127 / 250)) := by
  have h := reflection_log_12429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12430_neg : (491879 / 1000000000) ≤ -Real.log (250000 / 250123) ∧
    -Real.log (250000 / 250123) ≤ (12297 / 25000000) := by
  have h := checkLog_sound (w := (123 / 500123)) (n := 12)
    (lo := (491879 / 1000000000)) (hi := (12297 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250123 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250123 / 250000) = 1/(250000 / 250123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12430 : Bounds (491879 / 1000000000) (12297 / 25000000) (Real.log (250123 / 250000)) := by
  have h := reflection_log_12430_neg
  have he : Real.log (250123 / 250000) = -Real.log (250000 / 250123) := by
    rw [show ((250123 / 250000) : ℝ) = ((250000 / 250123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12431_neg : (492121 / 1000000000) ≤ -Real.log (249877 / 250000) ∧
    -Real.log (249877 / 250000) ≤ (246061 / 500000000) := by
  have h := checkLog_sound (w := (123 / 499877)) (n := 12)
    (lo := (492121 / 1000000000)) (hi := (246061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249877) = 1/(249877 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12431 : Bounds (-246061 / 500000000) (-492121 / 1000000000) (Real.log (249877 / 250000)) := by
  have h := reflection_log_12431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12432_neg : (45710897 / 200000000) ≤ -Real.log (500000 / 628391) ∧
    -Real.log (500000 / 628391) ≤ (114277243 / 500000000) := by
  have h := checkLog_sound (w := (128391 / 1128391)) (n := 12)
    (lo := (45710897 / 200000000)) (hi := (114277243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628391 / 500000) = 1/(500000 / 628391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12432 : Bounds (45710897 / 200000000) (114277243 / 500000000) (Real.log (628391 / 500000)) := by
  have h := reflection_log_12432_neg
  have he : Real.log (628391 / 500000) = -Real.log (500000 / 628391) := by
    rw [show ((628391 / 500000) : ℝ) = ((500000 / 628391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12433_neg : (18547867 / 62500000) ≤ -Real.log (371609 / 500000) ∧
    -Real.log (371609 / 500000) ≤ (296765873 / 1000000000) := by
  have h := checkLog_sound (w := (128391 / 871609)) (n := 12)
    (lo := (18547867 / 62500000)) (hi := (296765873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371609) = 1/(371609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12433 : Bounds (-296765873 / 1000000000) (-18547867 / 62500000) (Real.log (371609 / 500000)) := by
  have h := reflection_log_12433_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12434_neg : (229383243 / 1000000000) ≤ -Real.log (31250 / 39307) ∧
    -Real.log (31250 / 39307) ≤ (57345811 / 250000000) := by
  have h := checkLog_sound (w := (8057 / 70557)) (n := 12)
    (lo := (229383243 / 1000000000)) (hi := (57345811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39307 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39307 / 31250) = 1/(31250 / 39307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12434 : Bounds (229383243 / 1000000000) (57345811 / 250000000) (Real.log (39307 / 31250)) := by
  have h := reflection_log_12434_neg
  have he : Real.log (39307 / 31250) = -Real.log (31250 / 39307) := by
    rw [show ((39307 / 31250) : ℝ) = ((31250 / 39307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12435_neg : (298168867 / 1000000000) ≤ -Real.log (23193 / 31250) ∧
    -Real.log (23193 / 31250) ≤ (74542217 / 250000000) := by
  have h := checkLog_sound (w := (8057 / 54443)) (n := 12)
    (lo := (298168867 / 1000000000)) (hi := (74542217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23193) = 1/(23193 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12435 : Bounds (-74542217 / 250000000) (-298168867 / 1000000000) (Real.log (23193 / 31250)) := by
  have h := reflection_log_12435_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12436_neg : (68785623 / 1000000000) ≤ -Real.log (911647251 / 976562500) ∧
    -Real.log (911647251 / 976562500) ≤ (8598203 / 125000000) := by
  have h := checkLog_sound (w := (64915249 / 1888209751)) (n := 12)
    (lo := (68785623 / 1000000000)) (hi := (8598203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 911647251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 911647251) = 1/(911647251 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12436 : Bounds (-8598203 / 125000000) (-68785623 / 1000000000) (Real.log (911647251 / 976562500)) := by
  have h := reflection_log_12436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12437_neg : (34105693 / 500000000) ≤ -Real.log (233515751119 / 250000000000) ∧
    -Real.log (233515751119 / 250000000000) ≤ (68211387 / 1000000000) := by
  have h := checkLog_sound (w := (16484248881 / 483515751119)) (n := 12)
    (lo := (34105693 / 500000000)) (hi := (68211387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233515751119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233515751119) = 1/(233515751119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12437 : Bounds (-68211387 / 1000000000) (-34105693 / 500000000) (Real.log (233515751119 / 250000000000)) := by
  have h := reflection_log_12437_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12438_neg : (525320357 / 1000000000) ≤ -Real.log (100000000000 / 169100048707) ∧
    -Real.log (100000000000 / 169100048707) ≤ (262660179 / 500000000) := by
  have h := checkLog_sound (w := (69100048707 / 269100048707)) (n := 12)
    (lo := (525320357 / 1000000000)) (hi := (262660179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169100048707 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169100048707 / 100000000000) = 1/(100000000000 / 169100048707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12438 : Bounds (525320357 / 1000000000) (262660179 / 500000000) (Real.log (169100048707 / 100000000000)) := by
  have h := reflection_log_12438_neg
  have he : Real.log (169100048707 / 100000000000) = -Real.log (100000000000 / 169100048707) := by
    rw [show ((169100048707 / 100000000000) : ℝ) = ((100000000000 / 169100048707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12439_neg : (527552111 / 1000000000) ≤ -Real.log (7812500000 / 13240457789) ∧
    -Real.log (7812500000 / 13240457789) ≤ (32972007 / 62500000) := by
  have h := checkLog_sound (w := (5427957789 / 21052957789)) (n := 12)
    (lo := (527552111 / 1000000000)) (hi := (32972007 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13240457789 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13240457789 / 7812500000) = 1/(7812500000 / 13240457789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12439 : Bounds (527552111 / 1000000000) (32972007 / 62500000) (Real.log (13240457789 / 7812500000)) := by
  have h := reflection_log_12439_neg
  have he : Real.log (13240457789 / 7812500000) = -Real.log (7812500000 / 13240457789) := by
    rw [show ((13240457789 / 7812500000) : ℝ) = ((7812500000 / 13240457789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12440_neg : (1074754297 / 1000000000) ≤ -Real.log (500000000000 / 1464636542239) ∧
    -Real.log (500000000000 / 1464636542239) ≤ (1074754299 / 1000000000) := by
  have h := checkLog_sound (w := (464636542239 / 2464636542239)) (n := 12)
    (lo := (381607117 / 1000000000)) (hi := (190803559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1464636542239 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1464636542239 / 1000000000000) = 1/(500000000000 / 1464636542239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12440 : Bounds (1074754297 / 1000000000) (1074754299 / 1000000000) (Real.log (1464636542239 / 500000000000)) := by
  have h := reflection_log_12440_neg
  have he : Real.log (1464636542239 / 500000000000) = -Real.log (500000000000 / 1464636542239) := by
    rw [show ((1464636542239 / 500000000000) : ℝ) = ((500000000000 / 1464636542239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12441_neg : (269347833 / 250000000) ≤ -Real.log (31250000000 / 91781496063) ∧
    -Real.log (31250000000 / 91781496063) ≤ (538695667 / 500000000) := by
  have h := checkLog_sound (w := (29281496063 / 154281496063)) (n := 12)
    (lo := (48030519 / 125000000)) (hi := (384244153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91781496063 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(91781496063 / 62500000000) = 1/(31250000000 / 91781496063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12441 : Bounds (269347833 / 250000000) (538695667 / 500000000) (Real.log (91781496063 / 31250000000)) := by
  have h := reflection_log_12441_neg
  have he : Real.log (91781496063 / 31250000000) = -Real.log (31250000000 / 91781496063) := by
    rw [show ((91781496063 / 31250000000) : ℝ) = ((31250000000 / 91781496063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12442_neg : (200393759 / 500000000) ≤ -Real.log (1000 / 1493) ∧
    -Real.log (1000 / 1493) ≤ (400787519 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 2493)) (n := 12)
    (lo := (200393759 / 500000000)) (hi := (400787519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493 / 1000) = 1/(1000 / 1493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12442 : Bounds (200393759 / 500000000) (400787519 / 1000000000) (Real.log (1493 / 1000)) := by
  have h := reflection_log_12442_neg
  have he : Real.log (1493 / 1000) = -Real.log (1000 / 1493) := by
    rw [show ((1493 / 1000) : ℝ) = ((1000 / 1493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12443_neg : (27169771 / 40000000) ≤ -Real.log (507 / 1000) ∧
    -Real.log (507 / 1000) ≤ (169811069 / 250000000) := by
  have h := checkLog_sound (w := (493 / 1507)) (n := 12)
    (lo := (27169771 / 40000000)) (hi := (169811069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 507) = 1/(507 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12443 : Bounds (-169811069 / 250000000) (-27169771 / 40000000) (Real.log (507 / 1000)) := by
  have h := reflection_log_12443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12444_neg : (246439 / 500000000) ≤ -Real.log (1000000 / 1000493) ∧
    -Real.log (1000000 / 1000493) ≤ (492879 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 2000493)) (n := 12)
    (lo := (246439 / 500000000)) (hi := (492879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000493 / 1000000) = 1/(1000000 / 1000493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12444 : Bounds (246439 / 500000000) (492879 / 1000000000) (Real.log (1000493 / 1000000)) := by
  have h := reflection_log_12444_neg
  have he : Real.log (1000493 / 1000000) = -Real.log (1000000 / 1000493) := by
    rw [show ((1000493 / 1000000) : ℝ) = ((1000000 / 1000493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12445_neg : (493121 / 1000000000) ≤ -Real.log (999507 / 1000000) ∧
    -Real.log (999507 / 1000000) ≤ (246561 / 500000000) := by
  have h := checkLog_sound (w := (493 / 1999507)) (n := 12)
    (lo := (493121 / 1000000000)) (hi := (246561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999507) = 1/(999507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12445 : Bounds (-246561 / 500000000) (-493121 / 1000000000) (Real.log (999507 / 1000000)) := by
  have h := reflection_log_12445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12446_neg : (229011103 / 1000000000) ≤ -Real.log (250000 / 314339) ∧
    -Real.log (250000 / 314339) ≤ (7156597 / 31250000) := by
  have h := checkLog_sound (w := (64339 / 564339)) (n := 12)
    (lo := (229011103 / 1000000000)) (hi := (7156597 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314339 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314339 / 250000) = 1/(250000 / 314339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12446 : Bounds (229011103 / 1000000000) (7156597 / 31250000) (Real.log (314339 / 250000)) := by
  have h := reflection_log_12446_neg
  have he : Real.log (314339 / 250000) = -Real.log (250000 / 314339) := by
    rw [show ((314339 / 250000) : ℝ) = ((250000 / 314339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12447_neg : (297538487 / 1000000000) ≤ -Real.log (185661 / 250000) ∧
    -Real.log (185661 / 250000) ≤ (37192311 / 125000000) := by
  have h := checkLog_sound (w := (64339 / 435661)) (n := 12)
    (lo := (297538487 / 1000000000)) (hi := (37192311 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185661) = 1/(185661 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12447 : Bounds (-37192311 / 125000000) (-297538487 / 1000000000) (Real.log (185661 / 250000)) := by
  have h := reflection_log_12447_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12448_neg : (114920139 / 500000000) ≤ -Real.log (1000000 / 1258399) ∧
    -Real.log (1000000 / 1258399) ≤ (229840279 / 1000000000) := by
  have h := checkLog_sound (w := (258399 / 2258399)) (n := 12)
    (lo := (114920139 / 500000000)) (hi := (229840279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1258399 / 1000000) = 1/(1000000 / 1258399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12448 : Bounds (114920139 / 500000000) (229840279 / 1000000000) (Real.log (1258399 / 1000000)) := by
  have h := reflection_log_12448_neg
  have he : Real.log (1258399 / 1000000) = -Real.log (1000000 / 1258399) := by
    rw [show ((1258399 / 1000000) : ℝ) = ((1000000 / 1258399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12449_neg : (74735979 / 250000000) ≤ -Real.log (741601 / 1000000) ∧
    -Real.log (741601 / 1000000) ≤ (298943917 / 1000000000) := by
  have h := checkLog_sound (w := (258399 / 1741601)) (n := 12)
    (lo := (74735979 / 250000000)) (hi := (298943917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 741601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 741601) = 1/(741601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12449 : Bounds (-298943917 / 1000000000) (-74735979 / 250000000) (Real.log (741601 / 1000000)) := by
  have h := reflection_log_12449_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12450_neg : (34551819 / 500000000) ≤ -Real.log (933229956799 / 1000000000000) ∧
    -Real.log (933229956799 / 1000000000000) ≤ (69103639 / 1000000000) := by
  have h := checkLog_sound (w := (66770043201 / 1933229956799)) (n := 12)
    (lo := (34551819 / 500000000)) (hi := (69103639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 933229956799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 933229956799) = 1/(933229956799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12450 : Bounds (-69103639 / 1000000000) (-34551819 / 500000000) (Real.log (933229956799 / 1000000000000)) := by
  have h := reflection_log_12450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12451_neg : (8565923 / 125000000) ≤ -Real.log (58360493079 / 62500000000) ∧
    -Real.log (58360493079 / 62500000000) ≤ (13705477 / 200000000) := by
  have h := checkLog_sound (w := (4139506921 / 120860493079)) (n := 12)
    (lo := (8565923 / 125000000)) (hi := (13705477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58360493079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58360493079) = 1/(58360493079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12451 : Bounds (-13705477 / 200000000) (-8565923 / 125000000) (Real.log (58360493079 / 62500000000)) := by
  have h := reflection_log_12451_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12452_neg : (526549591 / 1000000000) ≤ -Real.log (500000000000 / 846540199611) ∧
    -Real.log (500000000000 / 846540199611) ≤ (65818699 / 125000000) := by
  have h := checkLog_sound (w := (346540199611 / 1346540199611)) (n := 12)
    (lo := (526549591 / 1000000000)) (hi := (65818699 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846540199611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(846540199611 / 500000000000) = 1/(500000000000 / 846540199611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12452 : Bounds (526549591 / 1000000000) (65818699 / 125000000) (Real.log (846540199611 / 500000000000)) := by
  have h := reflection_log_12452_neg
  have he : Real.log (846540199611 / 500000000000) = -Real.log (500000000000 / 846540199611) := by
    rw [show ((846540199611 / 500000000000) : ℝ) = ((500000000000 / 846540199611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12453_neg : (264392097 / 500000000) ≤ -Real.log (500000000000 / 848433996179) ∧
    -Real.log (500000000000 / 848433996179) ≤ (105756839 / 200000000) := by
  have h := checkLog_sound (w := (348433996179 / 1348433996179)) (n := 12)
    (lo := (264392097 / 500000000)) (hi := (105756839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848433996179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848433996179 / 500000000000) = 1/(500000000000 / 848433996179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12453 : Bounds (264392097 / 500000000) (105756839 / 200000000) (Real.log (848433996179 / 500000000000)) := by
  have h := reflection_log_12453_neg
  have he : Real.log (848433996179 / 500000000000) = -Real.log (500000000000 / 848433996179) := by
    rw [show ((848433996179 / 500000000000) : ℝ) = ((500000000000 / 848433996179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12454_neg : (269347833 / 250000000) ≤ -Real.log (500000000000 / 1468503937007) ∧
    -Real.log (500000000000 / 1468503937007) ≤ (538695667 / 500000000) := by
  have h := checkLog_sound (w := (468503937007 / 2468503937007)) (n := 12)
    (lo := (48030519 / 125000000)) (hi := (384244153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1468503937007 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1468503937007 / 1000000000000) = 1/(500000000000 / 1468503937007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12454 : Bounds (269347833 / 250000000) (538695667 / 500000000) (Real.log (1468503937007 / 500000000000)) := by
  have h := reflection_log_12454_neg
  have he : Real.log (1468503937007 / 500000000000) = -Real.log (500000000000 / 1468503937007) := by
    rw [show ((1468503937007 / 500000000000) : ℝ) = ((500000000000 / 1468503937007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12455_neg : (1080031793 / 1000000000) ≤ -Real.log (125000000000 / 368096646943) ∧
    -Real.log (125000000000 / 368096646943) ≤ (216006359 / 200000000) := by
  have h := checkLog_sound (w := (118096646943 / 618096646943)) (n := 12)
    (lo := (386884613 / 1000000000)) (hi := (193442307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368096646943 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(368096646943 / 250000000000) = 1/(125000000000 / 368096646943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12455 : Bounds (1080031793 / 1000000000) (216006359 / 200000000) (Real.log (368096646943 / 125000000000)) := by
  have h := reflection_log_12455_neg
  have he : Real.log (368096646943 / 125000000000) = -Real.log (125000000000 / 368096646943) := by
    rw [show ((368096646943 / 125000000000) : ℝ) = ((125000000000 / 368096646943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12456_neg : (200728543 / 500000000) ≤ -Real.log (500 / 747) ∧
    -Real.log (500 / 747) ≤ (401457087 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1247)) (n := 12)
    (lo := (200728543 / 500000000)) (hi := (401457087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747 / 500) = 1/(500 / 747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12456 : Bounds (200728543 / 500000000) (401457087 / 1000000000) (Real.log (747 / 500)) := by
  have h := reflection_log_12456_neg
  have he : Real.log (747 / 500) = -Real.log (500 / 747) := by
    rw [show ((747 / 500) : ℝ) = ((500 / 747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12457_neg : (681218609 / 1000000000) ≤ -Real.log (253 / 500) ∧
    -Real.log (253 / 500) ≤ (68121861 / 100000000) := by
  have h := checkLog_sound (w := (247 / 753)) (n := 12)
    (lo := (681218609 / 1000000000)) (hi := (68121861 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 253) = 1/(253 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12457 : Bounds (-68121861 / 100000000) (-681218609 / 1000000000) (Real.log (253 / 500)) := by
  have h := reflection_log_12457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12458_neg : (246939 / 500000000) ≤ -Real.log (500000 / 500247) ∧
    -Real.log (500000 / 500247) ≤ (493879 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1000247)) (n := 12)
    (lo := (246939 / 500000000)) (hi := (493879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500247 / 500000) = 1/(500000 / 500247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12458 : Bounds (246939 / 500000000) (493879 / 1000000000) (Real.log (500247 / 500000)) := by
  have h := reflection_log_12458_neg
  have he : Real.log (500247 / 500000) = -Real.log (500000 / 500247) := by
    rw [show ((500247 / 500000) : ℝ) = ((500000 / 500247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12459_neg : (247061 / 500000000) ≤ -Real.log (499753 / 500000) ∧
    -Real.log (499753 / 500000) ≤ (494123 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 999753)) (n := 12)
    (lo := (247061 / 500000000)) (hi := (494123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499753) = 1/(499753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12459 : Bounds (-494123 / 1000000000) (-247061 / 500000000) (Real.log (499753 / 500000)) := by
  have h := reflection_log_12459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12460_neg : (28683439 / 125000000) ≤ -Real.log (100000 / 125793) ∧
    -Real.log (100000 / 125793) ≤ (229467513 / 1000000000) := by
  have h := checkLog_sound (w := (25793 / 225793)) (n := 12)
    (lo := (28683439 / 125000000)) (hi := (229467513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125793 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125793 / 100000) = 1/(100000 / 125793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12460 : Bounds (28683439 / 125000000) (229467513 / 1000000000) (Real.log (125793 / 100000)) := by
  have h := reflection_log_12460_neg
  have he : Real.log (125793 / 100000) = -Real.log (100000 / 125793) := by
    rw [show ((125793 / 100000) : ℝ) = ((100000 / 125793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12461_neg : (2983117 / 10000000) ≤ -Real.log (74207 / 100000) ∧
    -Real.log (74207 / 100000) ≤ (298311701 / 1000000000) := by
  have h := checkLog_sound (w := (25793 / 174207)) (n := 12)
    (lo := (2983117 / 10000000)) (hi := (298311701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74207) = 1/(74207 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12461 : Bounds (-298311701 / 1000000000) (-2983117 / 10000000) (Real.log (74207 / 100000)) := by
  have h := reflection_log_12461_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12462_neg : (230297103 / 1000000000) ≤ -Real.log (500000 / 629487) ∧
    -Real.log (500000 / 629487) ≤ (14393569 / 62500000) := by
  have h := checkLog_sound (w := (129487 / 1129487)) (n := 12)
    (lo := (230297103 / 1000000000)) (hi := (14393569 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629487 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629487 / 500000) = 1/(500000 / 629487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12462 : Bounds (230297103 / 1000000000) (14393569 / 62500000) (Real.log (629487 / 500000)) := by
  have h := reflection_log_12462_neg
  have he : Real.log (629487 / 500000) = -Real.log (500000 / 629487) := by
    rw [show ((629487 / 500000) : ℝ) = ((500000 / 629487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12463_neg : (149859783 / 500000000) ≤ -Real.log (370513 / 500000) ∧
    -Real.log (370513 / 500000) ≤ (299719567 / 1000000000) := by
  have h := checkLog_sound (w := (129487 / 870513)) (n := 12)
    (lo := (149859783 / 500000000)) (hi := (299719567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370513) = 1/(370513 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12463 : Bounds (-299719567 / 1000000000) (-149859783 / 500000000) (Real.log (370513 / 500000)) := by
  have h := reflection_log_12463_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12464_neg : (69422463 / 1000000000) ≤ -Real.log (233233116831 / 250000000000) ∧
    -Real.log (233233116831 / 250000000000) ≤ (542363 / 7812500) := by
  have h := checkLog_sound (w := (16766883169 / 483233116831)) (n := 12)
    (lo := (69422463 / 1000000000)) (hi := (542363 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233233116831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233233116831) = 1/(233233116831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12464 : Bounds (-542363 / 7812500) (-69422463 / 1000000000) (Real.log (233233116831 / 250000000000)) := by
  have h := reflection_log_12464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12465_neg : (68844187 / 1000000000) ≤ -Real.log (9334721151 / 10000000000) ∧
    -Real.log (9334721151 / 10000000000) ≤ (17211047 / 250000000) := by
  have h := checkLog_sound (w := (665278849 / 19334721151)) (n := 12)
    (lo := (68844187 / 1000000000)) (hi := (17211047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9334721151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9334721151) = 1/(9334721151 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12465 : Bounds (-17211047 / 250000000) (-68844187 / 1000000000) (Real.log (9334721151 / 10000000000)) := by
  have h := reflection_log_12465_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12466_neg : (527779213 / 1000000000) ≤ -Real.log (500000000000 / 847581764523) ∧
    -Real.log (500000000000 / 847581764523) ≤ (263889607 / 500000000) := by
  have h := checkLog_sound (w := (347581764523 / 1347581764523)) (n := 12)
    (lo := (527779213 / 1000000000)) (hi := (263889607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847581764523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847581764523 / 500000000000) = 1/(500000000000 / 847581764523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12466 : Bounds (527779213 / 1000000000) (263889607 / 500000000) (Real.log (847581764523 / 500000000000)) := by
  have h := reflection_log_12466_neg
  have he : Real.log (847581764523 / 500000000000) = -Real.log (500000000000 / 847581764523) := by
    rw [show ((847581764523 / 500000000000) : ℝ) = ((500000000000 / 847581764523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12467_neg : (53001667 / 100000000) ≤ -Real.log (500000000000 / 849480315131) ∧
    -Real.log (500000000000 / 849480315131) ≤ (530016671 / 1000000000) := by
  have h := checkLog_sound (w := (349480315131 / 1349480315131)) (n := 12)
    (lo := (53001667 / 100000000)) (hi := (530016671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849480315131 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849480315131 / 500000000000) = 1/(500000000000 / 849480315131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12467 : Bounds (53001667 / 100000000) (530016671 / 1000000000) (Real.log (849480315131 / 500000000000)) := by
  have h := reflection_log_12467_neg
  have he : Real.log (849480315131 / 500000000000) = -Real.log (500000000000 / 849480315131) := by
    rw [show ((849480315131 / 500000000000) : ℝ) = ((500000000000 / 849480315131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12468_neg : (1080031793 / 1000000000) ≤ -Real.log (500000000000 / 1472386587771) ∧
    -Real.log (500000000000 / 1472386587771) ≤ (216006359 / 200000000) := by
  have h := checkLog_sound (w := (472386587771 / 2472386587771)) (n := 12)
    (lo := (386884613 / 1000000000)) (hi := (193442307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1472386587771 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1472386587771 / 1000000000000) = 1/(500000000000 / 1472386587771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12468 : Bounds (1080031793 / 1000000000) (216006359 / 200000000) (Real.log (1472386587771 / 500000000000)) := by
  have h := reflection_log_12468_neg
  have he : Real.log (1472386587771 / 500000000000) = -Real.log (500000000000 / 1472386587771) := by
    rw [show ((1472386587771 / 500000000000) : ℝ) = ((500000000000 / 1472386587771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12469_neg : (216535139 / 200000000) ≤ -Real.log (500000000000 / 1476284584981) ∧
    -Real.log (500000000000 / 1476284584981) ≤ (1082675697 / 1000000000) := by
  have h := checkLog_sound (w := (476284584981 / 2476284584981)) (n := 12)
    (lo := (77905703 / 200000000)) (hi := (97382129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1476284584981 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1476284584981 / 1000000000000) = 1/(500000000000 / 1476284584981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12469 : Bounds (216535139 / 200000000) (1082675697 / 1000000000) (Real.log (1476284584981 / 500000000000)) := by
  have h := reflection_log_12469_neg
  have he : Real.log (1476284584981 / 500000000000) = -Real.log (500000000000 / 1476284584981) := by
    rw [show ((1476284584981 / 500000000000) : ℝ) = ((500000000000 / 1476284584981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12470_neg : (201063103 / 500000000) ≤ -Real.log (200 / 299) ∧
    -Real.log (200 / 299) ≤ (402126207 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 499)) (n := 12)
    (lo := (201063103 / 500000000)) (hi := (402126207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299 / 200) = 1/(200 / 299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12470 : Bounds (201063103 / 500000000) (402126207 / 1000000000) (Real.log (299 / 200)) := by
  have h := reflection_log_12470_neg
  have he : Real.log (299 / 200) = -Real.log (200 / 299) := by
    rw [show ((299 / 200) : ℝ) = ((200 / 299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12471_neg : (683196849 / 1000000000) ≤ -Real.log (101 / 200) ∧
    -Real.log (101 / 200) ≤ (13663937 / 20000000) := by
  have h := checkLog_sound (w := (99 / 301)) (n := 12)
    (lo := (683196849 / 1000000000)) (hi := (13663937 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 101) = 1/(101 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12471 : Bounds (-13663937 / 20000000) (-683196849 / 1000000000) (Real.log (101 / 200)) := by
  have h := reflection_log_12471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12472_neg : (494877 / 1000000000) ≤ -Real.log (200000 / 200099) ∧
    -Real.log (200000 / 200099) ≤ (247439 / 500000000) := by
  have h := checkLog_sound (w := (99 / 400099)) (n := 12)
    (lo := (494877 / 1000000000)) (hi := (247439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200099 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200099 / 200000) = 1/(200000 / 200099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12472 : Bounds (494877 / 1000000000) (247439 / 500000000) (Real.log (200099 / 200000)) := by
  have h := reflection_log_12472_neg
  have he : Real.log (200099 / 200000) = -Real.log (200000 / 200099) := by
    rw [show ((200099 / 200000) : ℝ) = ((200000 / 200099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12473_neg : (247561 / 500000000) ≤ -Real.log (199901 / 200000) ∧
    -Real.log (199901 / 200000) ≤ (495123 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 399901)) (n := 12)
    (lo := (247561 / 500000000)) (hi := (495123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199901) = 1/(199901 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12473 : Bounds (-495123 / 1000000000) (-247561 / 500000000) (Real.log (199901 / 200000)) := by
  have h := reflection_log_12473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12474_neg : (57481127 / 250000000) ≤ -Real.log (200000 / 251701) ∧
    -Real.log (200000 / 251701) ≤ (229924509 / 1000000000) := by
  have h := checkLog_sound (w := (51701 / 451701)) (n := 12)
    (lo := (57481127 / 250000000)) (hi := (229924509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251701 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251701 / 200000) = 1/(200000 / 251701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12474 : Bounds (57481127 / 250000000) (229924509 / 1000000000) (Real.log (251701 / 200000)) := by
  have h := reflection_log_12474_neg
  have he : Real.log (251701 / 200000) = -Real.log (200000 / 251701) := by
    rw [show ((251701 / 200000) : ℝ) = ((200000 / 251701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12475_neg : (14954343 / 50000000) ≤ -Real.log (148299 / 200000) ∧
    -Real.log (148299 / 200000) ≤ (299086861 / 1000000000) := by
  have h := checkLog_sound (w := (51701 / 348299)) (n := 12)
    (lo := (14954343 / 50000000)) (hi := (299086861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148299) = 1/(148299 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12475 : Bounds (-299086861 / 1000000000) (-14954343 / 50000000) (Real.log (148299 / 200000)) := by
  have h := reflection_log_12475_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12476_neg : (115377257 / 500000000) ≤ -Real.log (20000 / 25191) ∧
    -Real.log (20000 / 25191) ≤ (46150903 / 200000000) := by
  have h := checkLog_sound (w := (5191 / 45191)) (n := 12)
    (lo := (115377257 / 500000000)) (hi := (46150903 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25191 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25191 / 20000) = 1/(20000 / 25191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12476 : Bounds (115377257 / 500000000) (46150903 / 200000000) (Real.log (25191 / 20000)) := by
  have h := reflection_log_12476_neg
  have he : Real.log (25191 / 20000) = -Real.log (20000 / 25191) := by
    rw [show ((25191 / 20000) : ℝ) = ((20000 / 25191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12477_neg : (300497169 / 1000000000) ≤ -Real.log (14809 / 20000) ∧
    -Real.log (14809 / 20000) ≤ (30049717 / 100000000) := by
  have h := checkLog_sound (w := (5191 / 34809)) (n := 12)
    (lo := (300497169 / 1000000000)) (hi := (30049717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 14809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 14809) = 1/(14809 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12477 : Bounds (-30049717 / 100000000) (-300497169 / 1000000000) (Real.log (14809 / 20000)) := by
  have h := reflection_log_12477_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12478_neg : (13948531 / 200000000) ≤ -Real.log (373053519 / 400000000) ∧
    -Real.log (373053519 / 400000000) ≤ (1089729 / 15625000) := by
  have h := checkLog_sound (w := (26946481 / 773053519)) (n := 12)
    (lo := (13948531 / 200000000)) (hi := (1089729 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 373053519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 373053519) = 1/(373053519 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12478 : Bounds (-1089729 / 15625000) (-13948531 / 200000000) (Real.log (373053519 / 400000000)) := by
  have h := reflection_log_12478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12479_neg : (69162351 / 1000000000) ≤ -Real.log (37327006599 / 40000000000) ∧
    -Real.log (37327006599 / 40000000000) ≤ (4322647 / 62500000) := by
  have h := checkLog_sound (w := (2672993401 / 77327006599)) (n := 12)
    (lo := (69162351 / 1000000000)) (hi := (4322647 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37327006599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37327006599) = 1/(37327006599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12479 : Bounds (-4322647 / 62500000) (-69162351 / 1000000000) (Real.log (37327006599 / 40000000000)) := by
  have h := reflection_log_12479_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0195 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12480_neg : (529011369 / 1000000000) ≤ -Real.log (625000000 / 1060783451) ∧
    -Real.log (625000000 / 1060783451) ≤ (52901137 / 100000000) := by
  have h := checkLog_sound (w := (435783451 / 1685783451)) (n := 12)
    (lo := (529011369 / 1000000000)) (hi := (52901137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060783451 / 625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1060783451 / 625000000) = 1/(625000000 / 1060783451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12480 : Bounds (529011369 / 1000000000) (52901137 / 100000000) (Real.log (1060783451 / 625000000)) := by
  have h := reflection_log_12480_neg
  have he : Real.log (1060783451 / 625000000) = -Real.log (625000000 / 1060783451) := by
    rw [show ((1060783451 / 625000000) : ℝ) = ((625000000 / 1060783451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12481_neg : (531251683 / 1000000000) ≤ -Real.log (250000000000 / 425265041529) ∧
    -Real.log (250000000000 / 425265041529) ≤ (132812921 / 250000000) := by
  have h := checkLog_sound (w := (175265041529 / 675265041529)) (n := 12)
    (lo := (531251683 / 1000000000)) (hi := (132812921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425265041529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425265041529 / 250000000000) = 1/(250000000000 / 425265041529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12481 : Bounds (531251683 / 1000000000) (132812921 / 250000000) (Real.log (425265041529 / 250000000000)) := by
  have h := reflection_log_12481_neg
  have he : Real.log (425265041529 / 250000000000) = -Real.log (250000000000 / 425265041529) := by
    rw [show ((425265041529 / 250000000000) : ℝ) = ((250000000000 / 425265041529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12482_neg : (216535139 / 200000000) ≤ -Real.log (25000000000 / 73814229249) ∧
    -Real.log (25000000000 / 73814229249) ≤ (1082675697 / 1000000000) := by
  have h := checkLog_sound (w := (23814229249 / 123814229249)) (n := 12)
    (lo := (77905703 / 200000000)) (hi := (97382129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73814229249 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(73814229249 / 50000000000) = 1/(25000000000 / 73814229249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12482 : Bounds (216535139 / 200000000) (1082675697 / 1000000000) (Real.log (73814229249 / 25000000000)) := by
  have h := reflection_log_12482_neg
  have he : Real.log (73814229249 / 25000000000) = -Real.log (25000000000 / 73814229249) := by
    rw [show ((73814229249 / 25000000000) : ℝ) = ((25000000000 / 73814229249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12483_neg : (217064611 / 200000000) ≤ -Real.log (250000000000 / 740099009901) ∧
    -Real.log (250000000000 / 740099009901) ≤ (1085323057 / 1000000000) := by
  have h := checkLog_sound (w := (240099009901 / 1240099009901)) (n := 12)
    (lo := (3137407 / 8000000)) (hi := (98043969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740099009901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(740099009901 / 500000000000) = 1/(250000000000 / 740099009901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12483 : Bounds (217064611 / 200000000) (1085323057 / 1000000000) (Real.log (740099009901 / 250000000000)) := by
  have h := reflection_log_12483_neg
  have he : Real.log (740099009901 / 250000000000) = -Real.log (250000000000 / 740099009901) := by
    rw [show ((740099009901 / 250000000000) : ℝ) = ((250000000000 / 740099009901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12484_neg : (402794879 / 1000000000) ≤ -Real.log (125 / 187) ∧
    -Real.log (125 / 187) ≤ (629367 / 1562500) := by
  have h := checkLog_sound (w := (31 / 156)) (n := 12)
    (lo := (402794879 / 1000000000)) (hi := (629367 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187 / 125) = 1/(125 / 187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12484 : Bounds (402794879 / 1000000000) (629367 / 1562500) (Real.log (187 / 125)) := by
  have h := reflection_log_12484_neg
  have he : Real.log (187 / 125) = -Real.log (125 / 187) := by
    rw [show ((187 / 125) : ℝ) = ((125 / 187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12485_neg : (68517901 / 100000000) ≤ -Real.log (63 / 125) ∧
    -Real.log (63 / 125) ≤ (685179011 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 94)) (n := 12)
    (lo := (68517901 / 100000000)) (hi := (685179011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 63) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 63) = 1/(63 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12485 : Bounds (-685179011 / 1000000000) (-68517901 / 100000000) (Real.log (63 / 125)) := by
  have h := reflection_log_12485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12486_neg : (495877 / 1000000000) ≤ -Real.log (62500 / 62531) ∧
    -Real.log (62500 / 62531) ≤ (247939 / 500000000) := by
  have h := checkLog_sound (w := (31 / 125031)) (n := 12)
    (lo := (495877 / 1000000000)) (hi := (247939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62531 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62531 / 62500) = 1/(62500 / 62531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12486 : Bounds (495877 / 1000000000) (247939 / 500000000) (Real.log (62531 / 62500)) := by
  have h := reflection_log_12486_neg
  have he : Real.log (62531 / 62500) = -Real.log (62500 / 62531) := by
    rw [show ((62531 / 62500) : ℝ) = ((62500 / 62531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12487_neg : (496123 / 1000000000) ≤ -Real.log (62469 / 62500) ∧
    -Real.log (62469 / 62500) ≤ (124031 / 250000000) := by
  have h := checkLog_sound (w := (31 / 124969)) (n := 12)
    (lo := (496123 / 1000000000)) (hi := (124031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62469) = 1/(62469 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12487 : Bounds (-124031 / 250000000) (-496123 / 1000000000) (Real.log (62469 / 62500)) := by
  have h := reflection_log_12487_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12488_neg : (46076259 / 200000000) ≤ -Real.log (25000 / 31477) ∧
    -Real.log (25000 / 31477) ≤ (14398831 / 62500000) := by
  have h := checkLog_sound (w := (6477 / 56477)) (n := 12)
    (lo := (46076259 / 200000000)) (hi := (14398831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31477 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31477 / 25000) = 1/(25000 / 31477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12488 : Bounds (46076259 / 200000000) (14398831 / 62500000) (Real.log (31477 / 25000)) := by
  have h := reflection_log_12488_neg
  have he : Real.log (31477 / 25000) = -Real.log (25000 / 31477) := by
    rw [show ((31477 / 25000) : ℝ) = ((25000 / 31477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12489_neg : (299862621 / 1000000000) ≤ -Real.log (18523 / 25000) ∧
    -Real.log (18523 / 25000) ≤ (149931311 / 500000000) := by
  have h := checkLog_sound (w := (6477 / 43523)) (n := 12)
    (lo := (299862621 / 1000000000)) (hi := (149931311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18523) = 1/(18523 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12489 : Bounds (-149931311 / 500000000) (-299862621 / 1000000000) (Real.log (18523 / 25000)) := by
  have h := reflection_log_12489_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12490_neg : (46242343 / 200000000) ≤ -Real.log (500000 / 630063) ∧
    -Real.log (500000 / 630063) ≤ (57802929 / 250000000) := by
  have h := checkLog_sound (w := (130063 / 1130063)) (n := 12)
    (lo := (46242343 / 200000000)) (hi := (57802929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630063 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630063 / 500000) = 1/(500000 / 630063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12490 : Bounds (46242343 / 200000000) (57802929 / 250000000) (Real.log (630063 / 500000)) := by
  have h := reflection_log_12490_neg
  have he : Real.log (630063 / 500000) = -Real.log (500000 / 630063) := by
    rw [show ((630063 / 500000) : ℝ) = ((500000 / 630063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12491_neg : (301275377 / 1000000000) ≤ -Real.log (369937 / 500000) ∧
    -Real.log (369937 / 500000) ≤ (150637689 / 500000000) := by
  have h := checkLog_sound (w := (130063 / 869937)) (n := 12)
    (lo := (301275377 / 1000000000)) (hi := (150637689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369937) = 1/(369937 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12491 : Bounds (-150637689 / 500000000) (-301275377 / 1000000000) (Real.log (369937 / 500000)) := by
  have h := reflection_log_12491_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12492_neg : (70063661 / 1000000000) ≤ -Real.log (233083616031 / 250000000000) ∧
    -Real.log (233083616031 / 250000000000) ≤ (35031831 / 500000000) := by
  have h := checkLog_sound (w := (16916383969 / 483083616031)) (n := 12)
    (lo := (70063661 / 1000000000)) (hi := (35031831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233083616031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233083616031) = 1/(233083616031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12492 : Bounds (-35031831 / 500000000) (-70063661 / 1000000000) (Real.log (233083616031 / 250000000000)) := by
  have h := reflection_log_12492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12493_neg : (34740663 / 500000000) ≤ -Real.log (583048471 / 625000000) ∧
    -Real.log (583048471 / 625000000) ≤ (69481327 / 1000000000) := by
  have h := checkLog_sound (w := (41951529 / 1208048471)) (n := 12)
    (lo := (34740663 / 500000000)) (hi := (69481327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 583048471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 583048471) = 1/(583048471 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12493 : Bounds (-69481327 / 1000000000) (-34740663 / 500000000) (Real.log (583048471 / 625000000)) := by
  have h := reflection_log_12493_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12494_neg : (530243917 / 1000000000) ≤ -Real.log (250000000000 / 424836689521) ∧
    -Real.log (250000000000 / 424836689521) ≤ (265121959 / 500000000) := by
  have h := checkLog_sound (w := (174836689521 / 674836689521)) (n := 12)
    (lo := (530243917 / 1000000000)) (hi := (265121959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424836689521 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424836689521 / 250000000000) = 1/(250000000000 / 424836689521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12494 : Bounds (530243917 / 1000000000) (265121959 / 500000000) (Real.log (424836689521 / 250000000000)) := by
  have h := reflection_log_12494_neg
  have he : Real.log (424836689521 / 250000000000) = -Real.log (250000000000 / 424836689521) := by
    rw [show ((424836689521 / 250000000000) : ℝ) = ((250000000000 / 424836689521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12495_neg : (532487093 / 1000000000) ≤ -Real.log (500000000000 / 851581485497) ∧
    -Real.log (500000000000 / 851581485497) ≤ (266243547 / 500000000) := by
  have h := checkLog_sound (w := (351581485497 / 1351581485497)) (n := 12)
    (lo := (532487093 / 1000000000)) (hi := (266243547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851581485497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851581485497 / 500000000000) = 1/(500000000000 / 851581485497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12495 : Bounds (532487093 / 1000000000) (266243547 / 500000000) (Real.log (851581485497 / 500000000000)) := by
  have h := reflection_log_12495_neg
  have he : Real.log (851581485497 / 500000000000) = -Real.log (500000000000 / 851581485497) := by
    rw [show ((851581485497 / 500000000000) : ℝ) = ((500000000000 / 851581485497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12496_neg : (217064611 / 200000000) ≤ -Real.log (500000000000 / 1480198019801) ∧
    -Real.log (500000000000 / 1480198019801) ≤ (1085323057 / 1000000000) := by
  have h := checkLog_sound (w := (480198019801 / 2480198019801)) (n := 12)
    (lo := (3137407 / 8000000)) (hi := (98043969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1480198019801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1480198019801 / 1000000000000) = 1/(500000000000 / 1480198019801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12496 : Bounds (217064611 / 200000000) (1085323057 / 1000000000) (Real.log (1480198019801 / 500000000000)) := by
  have h := reflection_log_12496_neg
  have he : Real.log (1480198019801 / 500000000000) = -Real.log (500000000000 / 1480198019801) := by
    rw [show ((1480198019801 / 500000000000) : ℝ) = ((500000000000 / 1480198019801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12497_neg : (1087973889 / 1000000000) ≤ -Real.log (500000000000 / 1484126984127) ∧
    -Real.log (500000000000 / 1484126984127) ≤ (1087973891 / 1000000000) := by
  have h := checkLog_sound (w := (484126984127 / 2484126984127)) (n := 12)
    (lo := (394826709 / 1000000000)) (hi := (39482671 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1484126984127 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1484126984127 / 1000000000000) = 1/(500000000000 / 1484126984127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12497 : Bounds (1087973889 / 1000000000) (1087973891 / 1000000000) (Real.log (1484126984127 / 500000000000)) := by
  have h := reflection_log_12497_neg
  have he : Real.log (1484126984127 / 500000000000) = -Real.log (500000000000 / 1484126984127) := by
    rw [show ((1484126984127 / 500000000000) : ℝ) = ((500000000000 / 1484126984127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12498_neg : (80692621 / 200000000) ≤ -Real.log (1000 / 1497) ∧
    -Real.log (1000 / 1497) ≤ (201731553 / 500000000) := by
  have h := checkLog_sound (w := (497 / 2497)) (n := 12)
    (lo := (80692621 / 200000000)) (hi := (201731553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1497 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1497 / 1000) = 1/(1000 / 1497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12498 : Bounds (80692621 / 200000000) (201731553 / 500000000) (Real.log (1497 / 1000)) := by
  have h := reflection_log_12498_neg
  have he : Real.log (1497 / 1000) = -Real.log (1000 / 1497) := by
    rw [show ((1497 / 1000) : ℝ) = ((1000 / 1497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12499_neg : (171791277 / 250000000) ≤ -Real.log (503 / 1000) ∧
    -Real.log (503 / 1000) ≤ (687165109 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 1503)) (n := 12)
    (lo := (171791277 / 250000000)) (hi := (687165109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 503) = 1/(503 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12499 : Bounds (-687165109 / 1000000000) (-171791277 / 250000000) (Real.log (503 / 1000)) := by
  have h := reflection_log_12499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12500_neg : (124219 / 250000000) ≤ -Real.log (1000000 / 1000497) ∧
    -Real.log (1000000 / 1000497) ≤ (496877 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 2000497)) (n := 12)
    (lo := (124219 / 250000000)) (hi := (496877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000497 / 1000000) = 1/(1000000 / 1000497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12500 : Bounds (124219 / 250000000) (496877 / 1000000000) (Real.log (1000497 / 1000000)) := by
  have h := reflection_log_12500_neg
  have he : Real.log (1000497 / 1000000) = -Real.log (1000000 / 1000497) := by
    rw [show ((1000497 / 1000000) : ℝ) = ((1000000 / 1000497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12501_neg : (497123 / 1000000000) ≤ -Real.log (999503 / 1000000) ∧
    -Real.log (999503 / 1000000) ≤ (124281 / 250000000) := by
  have h := checkLog_sound (w := (497 / 1999503)) (n := 12)
    (lo := (497123 / 1000000000)) (hi := (124281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999503) = 1/(999503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12501 : Bounds (-124281 / 250000000) (-497123 / 1000000000) (Real.log (999503 / 1000000)) := by
  have h := reflection_log_12501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12502_neg : (230837873 / 1000000000) ≤ -Real.log (200000 / 251931) ∧
    -Real.log (200000 / 251931) ≤ (115418937 / 500000000) := by
  have h := checkLog_sound (w := (51931 / 451931)) (n := 12)
    (lo := (230837873 / 1000000000)) (hi := (115418937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251931 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251931 / 200000) = 1/(200000 / 251931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12502 : Bounds (230837873 / 1000000000) (115418937 / 500000000) (Real.log (251931 / 200000)) := by
  have h := reflection_log_12502_neg
  have he : Real.log (251931 / 200000) = -Real.log (200000 / 251931) := by
    rw [show ((251931 / 200000) : ℝ) = ((200000 / 251931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12503_neg : (60127797 / 200000000) ≤ -Real.log (148069 / 200000) ∧
    -Real.log (148069 / 200000) ≤ (150319493 / 500000000) := by
  have h := checkLog_sound (w := (51931 / 348069)) (n := 12)
    (lo := (60127797 / 200000000)) (hi := (150319493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148069) = 1/(148069 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12503 : Bounds (-150319493 / 500000000) (-60127797 / 200000000) (Real.log (148069 / 200000)) := by
  have h := reflection_log_12503_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12504_neg : (231669501 / 1000000000) ≤ -Real.log (1000000 / 1260703) ∧
    -Real.log (1000000 / 1260703) ≤ (115834751 / 500000000) := by
  have h := checkLog_sound (w := (260703 / 2260703)) (n := 12)
    (lo := (231669501 / 1000000000)) (hi := (115834751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260703 / 1000000) = 1/(1000000 / 1260703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12504 : Bounds (231669501 / 1000000000) (115834751 / 500000000) (Real.log (1260703 / 1000000)) := by
  have h := reflection_log_12504_neg
  have he : Real.log (1260703 / 1000000) = -Real.log (1000000 / 1260703) := by
    rw [show ((1260703 / 1000000) : ℝ) = ((1000000 / 1260703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12505_neg : (37756943 / 125000000) ≤ -Real.log (739297 / 1000000) ∧
    -Real.log (739297 / 1000000) ≤ (60411109 / 200000000) := by
  have h := checkLog_sound (w := (260703 / 1739297)) (n := 12)
    (lo := (37756943 / 125000000)) (hi := (60411109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739297) = 1/(739297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12505 : Bounds (-60411109 / 200000000) (-37756943 / 125000000) (Real.log (739297 / 1000000)) := by
  have h := reflection_log_12505_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12506_neg : (35193021 / 500000000) ≤ -Real.log (932033945791 / 1000000000000) ∧
    -Real.log (932033945791 / 1000000000000) ≤ (70386043 / 1000000000) := by
  have h := checkLog_sound (w := (67966054209 / 1932033945791)) (n := 12)
    (lo := (35193021 / 500000000)) (hi := (70386043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 932033945791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 932033945791) = 1/(932033945791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12506 : Bounds (-70386043 / 1000000000) (-35193021 / 500000000) (Real.log (932033945791 / 1000000000000)) := by
  have h := reflection_log_12506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12507_neg : (69801111 / 1000000000) ≤ -Real.log (37303171239 / 40000000000) ∧
    -Real.log (37303171239 / 40000000000) ≤ (8725139 / 125000000) := by
  have h := checkLog_sound (w := (2696828761 / 77303171239)) (n := 12)
    (lo := (69801111 / 1000000000)) (hi := (8725139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37303171239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37303171239) = 1/(37303171239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12507 : Bounds (-8725139 / 125000000) (-69801111 / 1000000000) (Real.log (37303171239 / 40000000000)) := by
  have h := reflection_log_12507_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12508_neg : (531476859 / 1000000000) ≤ -Real.log (500000000000 / 850721623027) ∧
    -Real.log (500000000000 / 850721623027) ≤ (26573843 / 50000000) := by
  have h := checkLog_sound (w := (350721623027 / 1350721623027)) (n := 12)
    (lo := (531476859 / 1000000000)) (hi := (26573843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850721623027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850721623027 / 500000000000) = 1/(500000000000 / 850721623027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12508 : Bounds (531476859 / 1000000000) (26573843 / 50000000) (Real.log (850721623027 / 500000000000)) := by
  have h := reflection_log_12508_neg
  have he : Real.log (850721623027 / 500000000000) = -Real.log (500000000000 / 850721623027) := by
    rw [show ((850721623027 / 500000000000) : ℝ) = ((500000000000 / 850721623027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12509_neg : (266862523 / 500000000) ≤ -Real.log (50000000000 / 85263635589) ∧
    -Real.log (50000000000 / 85263635589) ≤ (533725047 / 1000000000) := by
  have h := checkLog_sound (w := (35263635589 / 135263635589)) (n := 12)
    (lo := (266862523 / 500000000)) (hi := (533725047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85263635589 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85263635589 / 50000000000) = 1/(50000000000 / 85263635589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12509 : Bounds (266862523 / 500000000) (533725047 / 1000000000) (Real.log (85263635589 / 50000000000)) := by
  have h := reflection_log_12509_neg
  have he : Real.log (85263635589 / 50000000000) = -Real.log (50000000000 / 85263635589) := by
    rw [show ((85263635589 / 50000000000) : ℝ) = ((50000000000 / 85263635589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12510_neg : (1087973889 / 1000000000) ≤ -Real.log (250000000000 / 742063492063) ∧
    -Real.log (250000000000 / 742063492063) ≤ (1087973891 / 1000000000) := by
  have h := checkLog_sound (w := (242063492063 / 1242063492063)) (n := 12)
    (lo := (394826709 / 1000000000)) (hi := (39482671 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742063492063 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(742063492063 / 500000000000) = 1/(250000000000 / 742063492063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12510 : Bounds (1087973889 / 1000000000) (1087973891 / 1000000000) (Real.log (742063492063 / 250000000000)) := by
  have h := reflection_log_12510_neg
  have he : Real.log (742063492063 / 250000000000) = -Real.log (250000000000 / 742063492063) := by
    rw [show ((742063492063 / 250000000000) : ℝ) = ((250000000000 / 742063492063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12511_neg : (1090628213 / 1000000000) ≤ -Real.log (500000000000 / 1488071570577) ∧
    -Real.log (500000000000 / 1488071570577) ≤ (218125643 / 200000000) := by
  have h := checkLog_sound (w := (488071570577 / 2488071570577)) (n := 12)
    (lo := (397481033 / 1000000000)) (hi := (198740517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1488071570577 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1488071570577 / 1000000000000) = 1/(500000000000 / 1488071570577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12511 : Bounds (1090628213 / 1000000000) (218125643 / 200000000) (Real.log (1488071570577 / 500000000000)) := by
  have h := reflection_log_12511_neg
  have he : Real.log (1488071570577 / 500000000000) = -Real.log (500000000000 / 1488071570577) := by
    rw [show ((1488071570577 / 500000000000) : ℝ) = ((500000000000 / 1488071570577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12512_neg : (80826177 / 200000000) ≤ -Real.log (500 / 749) ∧
    -Real.log (500 / 749) ≤ (202065443 / 500000000) := by
  have h := checkLog_sound (w := (249 / 1249)) (n := 12)
    (lo := (80826177 / 200000000)) (hi := (202065443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749 / 500) = 1/(500 / 749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12512 : Bounds (80826177 / 200000000) (202065443 / 500000000) (Real.log (749 / 500)) := by
  have h := reflection_log_12512_neg
  have he : Real.log (749 / 500) = -Real.log (500 / 749) := by
    rw [show ((749 / 500) : ℝ) = ((500 / 749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12513_neg : (689155159 / 1000000000) ≤ -Real.log (251 / 500) ∧
    -Real.log (251 / 500) ≤ (17228879 / 25000000) := by
  have h := checkLog_sound (w := (249 / 751)) (n := 12)
    (lo := (689155159 / 1000000000)) (hi := (17228879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 251) = 1/(251 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12513 : Bounds (-17228879 / 25000000) (-689155159 / 1000000000) (Real.log (251 / 500)) := by
  have h := reflection_log_12513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12514_neg : (124469 / 250000000) ≤ -Real.log (500000 / 500249) ∧
    -Real.log (500000 / 500249) ≤ (497877 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 1000249)) (n := 12)
    (lo := (124469 / 250000000)) (hi := (497877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500249 / 500000) = 1/(500000 / 500249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12514 : Bounds (124469 / 250000000) (497877 / 1000000000) (Real.log (500249 / 500000)) := by
  have h := reflection_log_12514_neg
  have he : Real.log (500249 / 500000) = -Real.log (500000 / 500249) := by
    rw [show ((500249 / 500000) : ℝ) = ((500000 / 500249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12515_neg : (124531 / 250000000) ≤ -Real.log (499751 / 500000) ∧
    -Real.log (499751 / 500000) ≤ (797 / 1600000) := by
  have h := checkLog_sound (w := (249 / 999751)) (n := 12)
    (lo := (124531 / 250000000)) (hi := (797 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499751) = 1/(499751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12515 : Bounds (-797 / 1600000) (-124531 / 250000000) (Real.log (499751 / 500000)) := by
  have h := reflection_log_12515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12516_neg : (231295037 / 1000000000) ≤ -Real.log (1000000 / 1260231) ∧
    -Real.log (1000000 / 1260231) ≤ (115647519 / 500000000) := by
  have h := checkLog_sound (w := (260231 / 2260231)) (n := 12)
    (lo := (231295037 / 1000000000)) (hi := (115647519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260231 / 1000000) = 1/(1000000 / 1260231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12516 : Bounds (231295037 / 1000000000) (115647519 / 500000000) (Real.log (1260231 / 1000000)) := by
  have h := reflection_log_12516_neg
  have he : Real.log (1260231 / 1000000) = -Real.log (1000000 / 1260231) := by
    rw [show ((1260231 / 1000000) : ℝ) = ((1000000 / 1260231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12517_neg : (301417303 / 1000000000) ≤ -Real.log (739769 / 1000000) ∧
    -Real.log (739769 / 1000000) ≤ (37677163 / 125000000) := by
  have h := checkLog_sound (w := (260231 / 1739769)) (n := 12)
    (lo := (301417303 / 1000000000)) (hi := (37677163 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739769) = 1/(739769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12517 : Bounds (-37677163 / 125000000) (-301417303 / 1000000000) (Real.log (739769 / 1000000)) := by
  have h := reflection_log_12517_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12518_neg : (116063539 / 500000000) ≤ -Real.log (6250 / 7883) ∧
    -Real.log (6250 / 7883) ≤ (232127079 / 1000000000) := by
  have h := checkLog_sound (w := (1633 / 14133)) (n := 12)
    (lo := (116063539 / 500000000)) (hi := (232127079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7883 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7883 / 6250) = 1/(6250 / 7883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12518 : Bounds (116063539 / 500000000) (232127079 / 1000000000) (Real.log (7883 / 6250)) := by
  have h := reflection_log_12518_neg
  have he : Real.log (7883 / 6250) = -Real.log (6250 / 7883) := by
    rw [show ((7883 / 6250) : ℝ) = ((6250 / 7883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12519_neg : (1892727 / 6250000) ≤ -Real.log (4617 / 6250) ∧
    -Real.log (4617 / 6250) ≤ (302836321 / 1000000000) := by
  have h := checkLog_sound (w := (1633 / 10867)) (n := 12)
    (lo := (1892727 / 6250000)) (hi := (302836321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4617) = 1/(4617 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12519 : Bounds (-302836321 / 1000000000) (-1892727 / 6250000) (Real.log (4617 / 6250)) := by
  have h := reflection_log_12519_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12520_neg : (70709241 / 1000000000) ≤ -Real.log (36395811 / 39062500) ∧
    -Real.log (36395811 / 39062500) ≤ (35354621 / 500000000) := by
  have h := checkLog_sound (w := (2666689 / 75458311)) (n := 12)
    (lo := (70709241 / 1000000000)) (hi := (35354621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 36395811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 36395811) = 1/(36395811 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12520 : Bounds (-35354621 / 500000000) (-70709241 / 1000000000) (Real.log (36395811 / 39062500)) := by
  have h := reflection_log_12520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12521_neg : (35061133 / 500000000) ≤ -Real.log (932279826639 / 1000000000000) ∧
    -Real.log (932279826639 / 1000000000000) ≤ (70122267 / 1000000000) := by
  have h := checkLog_sound (w := (67720173361 / 1932279826639)) (n := 12)
    (lo := (35061133 / 500000000)) (hi := (70122267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 932279826639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 932279826639) = 1/(932279826639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12521 : Bounds (-70122267 / 1000000000) (-35061133 / 500000000) (Real.log (932279826639 / 1000000000000)) := by
  have h := reflection_log_12521_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12522_neg : (532712341 / 1000000000) ≤ -Real.log (250000000000 / 425886661917) ∧
    -Real.log (250000000000 / 425886661917) ≤ (266356171 / 500000000) := by
  have h := checkLog_sound (w := (175886661917 / 675886661917)) (n := 12)
    (lo := (532712341 / 1000000000)) (hi := (266356171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425886661917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425886661917 / 250000000000) = 1/(250000000000 / 425886661917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12522 : Bounds (532712341 / 1000000000) (266356171 / 500000000) (Real.log (425886661917 / 250000000000)) := by
  have h := reflection_log_12522_neg
  have he : Real.log (425886661917 / 250000000000) = -Real.log (250000000000 / 425886661917) := by
    rw [show ((425886661917 / 250000000000) : ℝ) = ((250000000000 / 425886661917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12523_neg : (267481699 / 500000000) ≤ -Real.log (500000000000 / 853692874161) ∧
    -Real.log (500000000000 / 853692874161) ≤ (534963399 / 1000000000) := by
  have h := checkLog_sound (w := (353692874161 / 1353692874161)) (n := 12)
    (lo := (267481699 / 500000000)) (hi := (534963399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853692874161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853692874161 / 500000000000) = 1/(500000000000 / 853692874161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12523 : Bounds (267481699 / 500000000) (534963399 / 1000000000) (Real.log (853692874161 / 500000000000)) := by
  have h := reflection_log_12523_neg
  have he : Real.log (853692874161 / 500000000000) = -Real.log (500000000000 / 853692874161) := by
    rw [show ((853692874161 / 500000000000) : ℝ) = ((500000000000 / 853692874161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12524_neg : (1090628213 / 1000000000) ≤ -Real.log (31250000000 / 93004473161) ∧
    -Real.log (31250000000 / 93004473161) ≤ (218125643 / 200000000) := by
  have h := checkLog_sound (w := (30504473161 / 155504473161)) (n := 12)
    (lo := (397481033 / 1000000000)) (hi := (198740517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93004473161 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(93004473161 / 62500000000) = 1/(31250000000 / 93004473161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12524 : Bounds (1090628213 / 1000000000) (218125643 / 200000000) (Real.log (93004473161 / 31250000000)) := by
  have h := reflection_log_12524_neg
  have he : Real.log (93004473161 / 31250000000) = -Real.log (31250000000 / 93004473161) := by
    rw [show ((93004473161 / 31250000000) : ℝ) = ((31250000000 / 93004473161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12525_neg : (1093286043 / 1000000000) ≤ -Real.log (50000000000 / 149203187251) ∧
    -Real.log (50000000000 / 149203187251) ≤ (218657209 / 200000000) := by
  have h := checkLog_sound (w := (49203187251 / 249203187251)) (n := 12)
    (lo := (400138863 / 1000000000)) (hi := (25008679 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149203187251 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(149203187251 / 100000000000) = 1/(50000000000 / 149203187251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12525 : Bounds (1093286043 / 1000000000) (218657209 / 200000000) (Real.log (149203187251 / 50000000000)) := by
  have h := reflection_log_12525_neg
  have he : Real.log (149203187251 / 50000000000) = -Real.log (50000000000 / 149203187251) := by
    rw [show ((149203187251 / 50000000000) : ℝ) = ((50000000000 / 149203187251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12526_neg : (404798219 / 1000000000) ≤ -Real.log (1000 / 1499) ∧
    -Real.log (1000 / 1499) ≤ (20239911 / 50000000) := by
  have h := checkLog_sound (w := (499 / 2499)) (n := 12)
    (lo := (404798219 / 1000000000)) (hi := (20239911 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499 / 1000) = 1/(1000 / 1499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12526 : Bounds (404798219 / 1000000000) (20239911 / 50000000) (Real.log (1499 / 1000)) := by
  have h := reflection_log_12526_neg
  have he : Real.log (1499 / 1000) = -Real.log (1000 / 1499) := by
    rw [show ((1499 / 1000) : ℝ) = ((1000 / 1499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12527_neg : (691149177 / 1000000000) ≤ -Real.log (501 / 1000) ∧
    -Real.log (501 / 1000) ≤ (345574589 / 500000000) := by
  have h := checkLog_sound (w := (499 / 1501)) (n := 12)
    (lo := (691149177 / 1000000000)) (hi := (345574589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 501) = 1/(501 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12527 : Bounds (-345574589 / 500000000) (-691149177 / 1000000000) (Real.log (501 / 1000)) := by
  have h := reflection_log_12527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12528_neg : (3991 / 8000000) ≤ -Real.log (1000000 / 1000499) ∧
    -Real.log (1000000 / 1000499) ≤ (124719 / 250000000) := by
  have h := checkLog_sound (w := (499 / 2000499)) (n := 12)
    (lo := (3991 / 8000000)) (hi := (124719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000499 / 1000000) = 1/(1000000 / 1000499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12528 : Bounds (3991 / 8000000) (124719 / 250000000) (Real.log (1000499 / 1000000)) := by
  have h := reflection_log_12528_neg
  have he : Real.log (1000499 / 1000000) = -Real.log (1000000 / 1000499) := by
    rw [show ((1000499 / 1000000) : ℝ) = ((1000000 / 1000499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12529_neg : (124781 / 250000000) ≤ -Real.log (999501 / 1000000) ∧
    -Real.log (999501 / 1000000) ≤ (3993 / 8000000) := by
  have h := checkLog_sound (w := (499 / 1999501)) (n := 12)
    (lo := (124781 / 250000000)) (hi := (3993 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999501) = 1/(999501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12529 : Bounds (-3993 / 8000000) (-124781 / 250000000) (Real.log (999501 / 1000000)) := by
  have h := reflection_log_12529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12530_neg : (28968999 / 125000000) ≤ -Real.log (1000000 / 1260807) ∧
    -Real.log (1000000 / 1260807) ≤ (231751993 / 1000000000) := by
  have h := checkLog_sound (w := (260807 / 2260807)) (n := 12)
    (lo := (28968999 / 125000000)) (hi := (231751993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260807 / 1000000) = 1/(1000000 / 1260807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12530 : Bounds (28968999 / 125000000) (231751993 / 1000000000) (Real.log (1260807 / 1000000)) := by
  have h := reflection_log_12530_neg
  have he : Real.log (1260807 / 1000000) = -Real.log (1000000 / 1260807) := by
    rw [show ((1260807 / 1000000) : ℝ) = ((1000000 / 1260807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12531_neg : (75549057 / 250000000) ≤ -Real.log (739193 / 1000000) ∧
    -Real.log (739193 / 1000000) ≤ (302196229 / 1000000000) := by
  have h := checkLog_sound (w := (260807 / 1739193)) (n := 12)
    (lo := (75549057 / 250000000)) (hi := (302196229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739193) = 1/(739193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12531 : Bounds (-302196229 / 1000000000) (-75549057 / 250000000) (Real.log (739193 / 1000000)) := by
  have h := reflection_log_12531_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12532_neg : (46516889 / 200000000) ≤ -Real.log (1000000 / 1261857) ∧
    -Real.log (1000000 / 1261857) ≤ (116292223 / 500000000) := by
  have h := checkLog_sound (w := (261857 / 2261857)) (n := 12)
    (lo := (46516889 / 200000000)) (hi := (116292223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261857 / 1000000) = 1/(1000000 / 1261857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12532 : Bounds (46516889 / 200000000) (116292223 / 500000000) (Real.log (1261857 / 1000000)) := by
  have h := reflection_log_12532_neg
  have he : Real.log (1261857 / 1000000) = -Real.log (1000000 / 1261857) := by
    rw [show ((1261857 / 1000000) : ℝ) = ((1000000 / 1261857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12533_neg : (151808853 / 500000000) ≤ -Real.log (738143 / 1000000) ∧
    -Real.log (738143 / 1000000) ≤ (303617707 / 1000000000) := by
  have h := checkLog_sound (w := (261857 / 1738143)) (n := 12)
    (lo := (151808853 / 500000000)) (hi := (303617707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738143) = 1/(738143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12533 : Bounds (-303617707 / 1000000000) (-151808853 / 500000000) (Real.log (738143 / 1000000)) := by
  have h := reflection_log_12533_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12534_neg : (3551663 / 50000000) ≤ -Real.log (931430911551 / 1000000000000) ∧
    -Real.log (931430911551 / 1000000000000) ≤ (71033261 / 1000000000) := by
  have h := checkLog_sound (w := (68569088449 / 1931430911551)) (n := 12)
    (lo := (3551663 / 50000000)) (hi := (71033261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 931430911551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 931430911551) = 1/(931430911551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12534 : Bounds (-71033261 / 1000000000) (-3551663 / 50000000) (Real.log (931430911551 / 1000000000000)) := by
  have h := reflection_log_12534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12535_neg : (17611059 / 250000000) ≤ -Real.log (931979708751 / 1000000000000) ∧
    -Real.log (931979708751 / 1000000000000) ≤ (70444237 / 1000000000) := by
  have h := checkLog_sound (w := (68020291249 / 1931979708751)) (n := 12)
    (lo := (17611059 / 250000000)) (hi := (70444237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 931979708751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 931979708751) = 1/(931979708751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12535 : Bounds (-70444237 / 1000000000) (-17611059 / 250000000) (Real.log (931979708751 / 1000000000000)) := by
  have h := reflection_log_12535_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12536_neg : (26697411 / 50000000) ≤ -Real.log (62500000000 / 106603332959) ∧
    -Real.log (62500000000 / 106603332959) ≤ (533948221 / 1000000000) := by
  have h := checkLog_sound (w := (44103332959 / 169103332959)) (n := 12)
    (lo := (26697411 / 50000000)) (hi := (533948221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106603332959 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106603332959 / 62500000000) = 1/(62500000000 / 106603332959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12536 : Bounds (26697411 / 50000000) (533948221 / 1000000000) (Real.log (106603332959 / 62500000000)) := by
  have h := reflection_log_12536_neg
  have he : Real.log (106603332959 / 62500000000) = -Real.log (62500000000 / 106603332959) := by
    rw [show ((106603332959 / 62500000000) : ℝ) = ((62500000000 / 106603332959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12537_neg : (536202151 / 1000000000) ≤ -Real.log (20000000000 / 34190041767) ∧
    -Real.log (20000000000 / 34190041767) ≤ (67025269 / 125000000) := by
  have h := checkLog_sound (w := (14190041767 / 54190041767)) (n := 12)
    (lo := (536202151 / 1000000000)) (hi := (67025269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34190041767 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34190041767 / 20000000000) = 1/(20000000000 / 34190041767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12537 : Bounds (536202151 / 1000000000) (67025269 / 125000000) (Real.log (34190041767 / 20000000000)) := by
  have h := reflection_log_12537_neg
  have he : Real.log (34190041767 / 20000000000) = -Real.log (20000000000 / 34190041767) := by
    rw [show ((34190041767 / 20000000000) : ℝ) = ((20000000000 / 34190041767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12538_neg : (1093286043 / 1000000000) ≤ -Real.log (500000000000 / 1492031872509) ∧
    -Real.log (500000000000 / 1492031872509) ≤ (218657209 / 200000000) := by
  have h := checkLog_sound (w := (492031872509 / 2492031872509)) (n := 12)
    (lo := (400138863 / 1000000000)) (hi := (25008679 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1492031872509 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1492031872509 / 1000000000000) = 1/(500000000000 / 1492031872509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12538 : Bounds (1093286043 / 1000000000) (218657209 / 200000000) (Real.log (1492031872509 / 500000000000)) := by
  have h := reflection_log_12538_neg
  have he : Real.log (1492031872509 / 500000000000) = -Real.log (500000000000 / 1492031872509) := by
    rw [show ((1492031872509 / 500000000000) : ℝ) = ((500000000000 / 1492031872509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12539_neg : (273986849 / 250000000) ≤ -Real.log (15625000000 / 46750249501) ∧
    -Real.log (15625000000 / 46750249501) ≤ (547973699 / 500000000) := by
  have h := checkLog_sound (w := (15500249501 / 78000249501)) (n := 12)
    (lo := (50350027 / 125000000)) (hi := (402800217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46750249501 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(46750249501 / 31250000000) = 1/(15625000000 / 46750249501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12539 : Bounds (273986849 / 250000000) (547973699 / 500000000) (Real.log (46750249501 / 15625000000)) := by
  have h := reflection_log_12539_neg
  have he : Real.log (46750249501 / 15625000000) = -Real.log (15625000000 / 46750249501) := by
    rw [show ((46750249501 / 15625000000) : ℝ) = ((15625000000 / 46750249501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12540_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12540 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) (Real.log (1 / 2)) := by
  have h := reflection_log_12540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12541_neg : (3999 / 8000000) ≤ -Real.log (2000 / 2001) ∧
    -Real.log (2000 / 2001) ≤ (124969 / 250000000) := by
  have h := checkLog_sound (w := (1 / 4001)) (n := 12)
    (lo := (3999 / 8000000)) (hi := (124969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2001 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2001 / 2000) = 1/(2000 / 2001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12541 : Bounds (3999 / 8000000) (124969 / 250000000) (Real.log (2001 / 2000)) := by
  have h := reflection_log_12541_neg
  have he : Real.log (2001 / 2000) = -Real.log (2000 / 2001) := by
    rw [show ((2001 / 2000) : ℝ) = ((2000 / 2001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12542_neg : (4001 / 8000000) ≤ -Real.log (1999 / 2000) ∧
    -Real.log (1999 / 2000) ≤ (250063 / 500000000) := by
  have h := checkLog_sound (w := (1 / 3999)) (n := 12)
    (lo := (4001 / 8000000)) (hi := (250063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1999) = 1/(1999 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12542 : Bounds (-250063 / 500000000) (-4001 / 8000000) (Real.log (1999 / 2000)) := by
  have h := reflection_log_12542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12543_neg : (116104369 / 500000000) ≤ -Real.log (1000000 / 1261383) ∧
    -Real.log (1000000 / 1261383) ≤ (232208739 / 1000000000) := by
  have h := checkLog_sound (w := (261383 / 2261383)) (n := 12)
    (lo := (116104369 / 500000000)) (hi := (232208739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261383 / 1000000) = 1/(1000000 / 1261383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12543 : Bounds (116104369 / 500000000) (232208739 / 1000000000) (Real.log (1261383 / 1000000)) := by
  have h := reflection_log_12543_neg
  have he : Real.log (1261383 / 1000000) = -Real.log (1000000 / 1261383) := by
    rw [show ((1261383 / 1000000) : ℝ) = ((1000000 / 1261383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


