-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0208__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0208__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T01:31:51.741477+00:00
-- url     : https://prove2.me/theorems/24e26c75-0968-4be6-ac78-4b060813d531
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0208 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0209, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0208 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0209, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0210)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0208 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0209, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0210)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0208 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0209, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0210) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0208 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0209, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0210).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0208 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13312_neg : (61653937 / 200000000) ≤ -Real.log (250000 / 340267) ∧
    -Real.log (250000 / 340267) ≤ (154134843 / 500000000) := by
  have h := checkLog_sound (w := (90267 / 590267)) (n := 12)
    (lo := (61653937 / 200000000)) (hi := (154134843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340267 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340267 / 250000) = 1/(250000 / 340267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13312 : Bounds (61653937 / 200000000) (154134843 / 500000000) (Real.log (340267 / 250000)) := by
  have h := reflection_log_13312_neg
  have he : Real.log (340267 / 250000) = -Real.log (250000 / 340267) := by
    rw [show ((340267 / 250000) : ℝ) = ((250000 / 340267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13313_neg : (223978623 / 500000000) ≤ -Real.log (159733 / 250000) ∧
    -Real.log (159733 / 250000) ≤ (447957247 / 1000000000) := by
  have h := checkLog_sound (w := (90267 / 409733)) (n := 12)
    (lo := (223978623 / 500000000)) (hi := (447957247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159733) = 1/(159733 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13313 : Bounds (-447957247 / 1000000000) (-223978623 / 500000000) (Real.log (159733 / 250000)) := by
  have h := reflection_log_13313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13314_neg : (155074397 / 500000000) ≤ -Real.log (250000 / 340907) ∧
    -Real.log (250000 / 340907) ≤ (62029759 / 200000000) := by
  have h := checkLog_sound (w := (90907 / 590907)) (n := 12)
    (lo := (155074397 / 500000000)) (hi := (62029759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340907 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340907 / 250000) = 1/(250000 / 340907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13314 : Bounds (155074397 / 500000000) (62029759 / 200000000) (Real.log (340907 / 250000)) := by
  have h := reflection_log_13314_neg
  have he : Real.log (340907 / 250000) = -Real.log (250000 / 340907) := by
    rw [show ((340907 / 250000) : ℝ) = ((250000 / 340907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13315_neg : (22598599 / 50000000) ≤ -Real.log (159093 / 250000) ∧
    -Real.log (159093 / 250000) ≤ (451971981 / 1000000000) := by
  have h := checkLog_sound (w := (90907 / 409093)) (n := 12)
    (lo := (22598599 / 50000000)) (hi := (451971981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159093) = 1/(159093 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13315 : Bounds (-451971981 / 1000000000) (-22598599 / 50000000) (Real.log (159093 / 250000)) := by
  have h := reflection_log_13315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13316_neg : (70911593 / 500000000) ≤ -Real.log (54235917351 / 62500000000) ∧
    -Real.log (54235917351 / 62500000000) ≤ (141823187 / 1000000000) := by
  have h := checkLog_sound (w := (8264082649 / 116735917351)) (n := 12)
    (lo := (70911593 / 500000000)) (hi := (141823187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 54235917351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 54235917351) = 1/(54235917351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13316 : Bounds (-141823187 / 1000000000) (-70911593 / 500000000) (Real.log (54235917351 / 62500000000)) := by
  have h := reflection_log_13316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13317_neg : (3492189 / 25000000) ≤ -Real.log (54351868711 / 62500000000) ∧
    -Real.log (54351868711 / 62500000000) ≤ (139687561 / 1000000000) := by
  have h := checkLog_sound (w := (8148131289 / 116851868711)) (n := 12)
    (lo := (3492189 / 25000000)) (hi := (139687561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 54351868711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 54351868711) = 1/(54351868711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13317 : Bounds (-139687561 / 1000000000) (-3492189 / 25000000) (Real.log (54351868711 / 62500000000)) := by
  have h := reflection_log_13317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13318_neg : (756226931 / 1000000000) ≤ -Real.log (500000000000 / 1065111780283) ∧
    -Real.log (500000000000 / 1065111780283) ≤ (756226933 / 1000000000) := by
  have h := checkLog_sound (w := (65111780283 / 2065111780283)) (n := 12)
    (lo := (63079751 / 1000000000)) (hi := (7884969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1065111780283 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1065111780283 / 1000000000000) = 1/(500000000000 / 1065111780283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13318 : Bounds (756226931 / 1000000000) (756226933 / 1000000000) (Real.log (1065111780283 / 500000000000)) := by
  have h := reflection_log_13318_neg
  have he : Real.log (1065111780283 / 500000000000) = -Real.log (500000000000 / 1065111780283) := by
    rw [show ((1065111780283 / 500000000000) : ℝ) = ((500000000000 / 1065111780283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13319_neg : (30484831 / 40000000) ≤ -Real.log (500000000000 / 1071407918639) ∧
    -Real.log (500000000000 / 1071407918639) ≤ (762120777 / 1000000000) := by
  have h := checkLog_sound (w := (71407918639 / 2071407918639)) (n := 12)
    (lo := (13794719 / 200000000)) (hi := (17243399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1071407918639 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1071407918639 / 1000000000000) = 1/(500000000000 / 1071407918639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13319 : Bounds (30484831 / 40000000) (762120777 / 1000000000) (Real.log (1071407918639 / 500000000000)) := by
  have h := reflection_log_13319_neg
  have he : Real.log (1071407918639 / 500000000000) = -Real.log (500000000000 / 1071407918639) := by
    rw [show ((1071407918639 / 500000000000) : ℝ) = ((500000000000 / 1071407918639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13320_neg : (796365539 / 500000000) ≤ -Real.log (62500000000 / 307322485207) ∧
    -Real.log (62500000000 / 307322485207) ≤ (1592731081 / 1000000000) := by
  have h := checkLog_sound (w := (57322485207 / 557322485207)) (n := 12)
    (lo := (103218359 / 500000000)) (hi := (206436719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307322485207 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(307322485207 / 250000000000) = 1/(62500000000 / 307322485207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13320 : Bounds (796365539 / 500000000) (1592731081 / 1000000000) (Real.log (307322485207 / 62500000000)) := by
  have h := reflection_log_13320_neg
  have he : Real.log (307322485207 / 62500000000) = -Real.log (62500000000 / 307322485207) := by
    rw [show ((307322485207 / 62500000000) : ℝ) = ((62500000000 / 307322485207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13321_neg : (1603449869 / 1000000000) ≤ -Real.log (250000000000 / 1242537313433) ∧
    -Real.log (250000000000 / 1242537313433) ≤ (100215617 / 62500000) := by
  have h := checkLog_sound (w := (242537313433 / 2242537313433)) (n := 12)
    (lo := (217155509 / 1000000000)) (hi := (21715551 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242537313433 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1242537313433 / 1000000000000) = 1/(250000000000 / 1242537313433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13321 : Bounds (1603449869 / 1000000000) (100215617 / 62500000) (Real.log (1242537313433 / 250000000000)) := by
  have h := reflection_log_13321_neg
  have he : Real.log (1242537313433 / 250000000000) = -Real.log (250000000000 / 1242537313433) := by
    rw [show ((1242537313433 / 250000000000) : ℝ) = ((250000000000 / 1242537313433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13322_neg : (511625303 / 1000000000) ≤ -Real.log (250 / 417) ∧
    -Real.log (250 / 417) ≤ (63953163 / 125000000) := by
  have h := checkLog_sound (w := (167 / 667)) (n := 12)
    (lo := (511625303 / 1000000000)) (hi := (63953163 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417 / 250) = 1/(250 / 417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13322 : Bounds (511625303 / 1000000000) (63953163 / 125000000) (Real.log (417 / 250)) := by
  have h := reflection_log_13322_neg
  have he : Real.log (417 / 250) = -Real.log (250 / 417) := by
    rw [show ((417 / 250) : ℝ) = ((250 / 417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13323_neg : (1102620309 / 1000000000) ≤ -Real.log (83 / 250) ∧
    -Real.log (83 / 250) ≤ (1102620311 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 104)) (n := 12)
    (lo := (409473129 / 1000000000)) (hi := (40947313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 83) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 83) = 1/(83 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13323 : Bounds (-1102620311 / 1000000000) (-1102620309 / 1000000000) (Real.log (83 / 250)) := by
  have h := reflection_log_13323_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13324_neg : (5217 / 7812500) ≤ -Real.log (250000 / 250167) ∧
    -Real.log (250000 / 250167) ≤ (667777 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 500167)) (n := 12)
    (lo := (5217 / 7812500)) (hi := (667777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250167 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250167 / 250000) = 1/(250000 / 250167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13324 : Bounds (5217 / 7812500) (667777 / 1000000000) (Real.log (250167 / 250000)) := by
  have h := reflection_log_13324_neg
  have he : Real.log (250167 / 250000) = -Real.log (250000 / 250167) := by
    rw [show ((250167 / 250000) : ℝ) = ((250000 / 250167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13325_neg : (668223 / 1000000000) ≤ -Real.log (249833 / 250000) ∧
    -Real.log (249833 / 250000) ≤ (10441 / 15625000) := by
  have h := checkLog_sound (w := (167 / 499833)) (n := 12)
    (lo := (668223 / 1000000000)) (hi := (10441 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249833) = 1/(249833 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13325 : Bounds (-10441 / 15625000) (-668223 / 1000000000) (Real.log (249833 / 250000)) := by
  have h := reflection_log_13325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13326_neg : (19356931 / 62500000) ≤ -Real.log (1000000 / 1363031) ∧
    -Real.log (1000000 / 1363031) ≤ (309710897 / 1000000000) := by
  have h := checkLog_sound (w := (363031 / 2363031)) (n := 12)
    (lo := (19356931 / 62500000)) (hi := (309710897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363031 / 1000000) = 1/(1000000 / 1363031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13326 : Bounds (19356931 / 62500000) (309710897 / 1000000000) (Real.log (1363031 / 1000000)) := by
  have h := reflection_log_13326_neg
  have he : Real.log (1363031 / 1000000) = -Real.log (1000000 / 1363031) := by
    rw [show ((1363031 / 1000000) : ℝ) = ((1000000 / 1363031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13327_neg : (45103429 / 100000000) ≤ -Real.log (636969 / 1000000) ∧
    -Real.log (636969 / 1000000) ≤ (451034291 / 1000000000) := by
  have h := checkLog_sound (w := (363031 / 1636969)) (n := 12)
    (lo := (45103429 / 100000000)) (hi := (451034291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 636969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 636969) = 1/(636969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13327 : Bounds (-451034291 / 1000000000) (-45103429 / 100000000) (Real.log (636969 / 1000000)) := by
  have h := reflection_log_13327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13328_neg : (7789829 / 25000000) ≤ -Real.log (1000000 / 1365599) ∧
    -Real.log (1000000 / 1365599) ≤ (311593161 / 1000000000) := by
  have h := checkLog_sound (w := (365599 / 2365599)) (n := 12)
    (lo := (7789829 / 25000000)) (hi := (311593161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1365599 / 1000000) = 1/(1000000 / 1365599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13328 : Bounds (7789829 / 25000000) (311593161 / 1000000000) (Real.log (1365599 / 1000000)) := by
  have h := reflection_log_13328_neg
  have he : Real.log (1365599 / 1000000) = -Real.log (1000000 / 1365599) := by
    rw [show ((1365599 / 1000000) : ℝ) = ((1000000 / 1365599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13329_neg : (28442127 / 62500000) ≤ -Real.log (634401 / 1000000) ∧
    -Real.log (634401 / 1000000) ≤ (455074033 / 1000000000) := by
  have h := checkLog_sound (w := (365599 / 1634401)) (n := 12)
    (lo := (28442127 / 62500000)) (hi := (455074033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 634401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 634401) = 1/(634401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13329 : Bounds (-455074033 / 1000000000) (-28442127 / 62500000) (Real.log (634401 / 1000000)) := by
  have h := reflection_log_13329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13330_neg : (17935109 / 125000000) ≤ -Real.log (866337371199 / 1000000000000) ∧
    -Real.log (866337371199 / 1000000000000) ≤ (143480873 / 1000000000) := by
  have h := checkLog_sound (w := (133662628801 / 1866337371199)) (n := 12)
    (lo := (17935109 / 125000000)) (hi := (143480873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 866337371199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 866337371199) = 1/(866337371199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13330 : Bounds (-143480873 / 1000000000) (-17935109 / 125000000) (Real.log (866337371199 / 1000000000000)) := by
  have h := reflection_log_13330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13331_neg : (141323393 / 1000000000) ≤ -Real.log (868208493039 / 1000000000000) ∧
    -Real.log (868208493039 / 1000000000000) ≤ (70661697 / 500000000) := by
  have h := checkLog_sound (w := (131791506961 / 1868208493039)) (n := 12)
    (lo := (141323393 / 1000000000)) (hi := (70661697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 868208493039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 868208493039) = 1/(868208493039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13331 : Bounds (-70661697 / 500000000) (-141323393 / 1000000000) (Real.log (868208493039 / 1000000000000)) := by
  have h := reflection_log_13331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13332_neg : (380372593 / 500000000) ≤ -Real.log (500000000000 / 1069935114581) ∧
    -Real.log (500000000000 / 1069935114581) ≤ (190186297 / 250000000) := by
  have h := checkLog_sound (w := (69935114581 / 2069935114581)) (n := 12)
    (lo := (33799003 / 500000000)) (hi := (67598007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1069935114581 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1069935114581 / 1000000000000) = 1/(500000000000 / 1069935114581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13332 : Bounds (380372593 / 500000000) (190186297 / 250000000) (Real.log (1069935114581 / 500000000000)) := by
  have h := reflection_log_13332_neg
  have he : Real.log (1069935114581 / 500000000000) = -Real.log (500000000000 / 1069935114581) := by
    rw [show ((1069935114581 / 500000000000) : ℝ) = ((500000000000 / 1069935114581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13333_neg : (95833399 / 125000000) ≤ -Real.log (100000000000 / 215258015041) ∧
    -Real.log (100000000000 / 215258015041) ≤ (383333597 / 500000000) := by
  have h := checkLog_sound (w := (15258015041 / 415258015041)) (n := 12)
    (lo := (18380003 / 250000000)) (hi := (73520013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215258015041 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(215258015041 / 200000000000) = 1/(100000000000 / 215258015041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13333 : Bounds (95833399 / 125000000) (383333597 / 500000000) (Real.log (215258015041 / 100000000000)) := by
  have h := reflection_log_13333_neg
  have he : Real.log (215258015041 / 100000000000) = -Real.log (100000000000 / 215258015041) := by
    rw [show ((215258015041 / 100000000000) : ℝ) = ((100000000000 / 215258015041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13334_neg : (1603449869 / 1000000000) ≤ -Real.log (100000000000 / 497014925373) ∧
    -Real.log (100000000000 / 497014925373) ≤ (100215617 / 62500000) := by
  have h := checkLog_sound (w := (97014925373 / 897014925373)) (n := 12)
    (lo := (217155509 / 1000000000)) (hi := (21715551 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497014925373 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(497014925373 / 400000000000) = 1/(100000000000 / 497014925373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13334 : Bounds (1603449869 / 1000000000) (100215617 / 62500000) (Real.log (497014925373 / 100000000000)) := by
  have h := reflection_log_13334_neg
  have he : Real.log (497014925373 / 100000000000) = -Real.log (100000000000 / 497014925373) := by
    rw [show ((497014925373 / 100000000000) : ℝ) = ((100000000000 / 497014925373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13335_neg : (403561403 / 250000000) ≤ -Real.log (125000000000 / 628012048193) ∧
    -Real.log (125000000000 / 628012048193) ≤ (322849123 / 200000000) := by
  have h := checkLog_sound (w := (128012048193 / 1128012048193)) (n := 12)
    (lo := (56987813 / 250000000)) (hi := (227951253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628012048193 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(628012048193 / 500000000000) = 1/(125000000000 / 628012048193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13335 : Bounds (403561403 / 250000000) (322849123 / 200000000) (Real.log (628012048193 / 125000000000)) := by
  have h := reflection_log_13335_neg
  have he : Real.log (628012048193 / 125000000000) = -Real.log (125000000000 / 628012048193) := by
    rw [show ((628012048193 / 125000000000) : ℝ) = ((125000000000 / 628012048193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13336_neg : (513422249 / 1000000000) ≤ -Real.log (1000 / 1671) ∧
    -Real.log (1000 / 1671) ≤ (2053689 / 4000000) := by
  have h := checkLog_sound (w := (671 / 2671)) (n := 12)
    (lo := (513422249 / 1000000000)) (hi := (2053689 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1671 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1671 / 1000) = 1/(1000 / 1671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13336 : Bounds (513422249 / 1000000000) (2053689 / 4000000) (Real.log (1671 / 1000)) := by
  have h := reflection_log_13336_neg
  have he : Real.log (1671 / 1000) = -Real.log (1000 / 1671) := by
    rw [show ((1671 / 1000) : ℝ) = ((1000 / 1671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13337_neg : (1111697527 / 1000000000) ≤ -Real.log (329 / 1000) ∧
    -Real.log (329 / 1000) ≤ (1111697529 / 1000000000) := by
  have h := checkLog_sound (w := (171 / 829)) (n := 12)
    (lo := (418550347 / 1000000000)) (hi := (104637587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 329) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 329) = 1/(329 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13337 : Bounds (-1111697529 / 1000000000) (-1111697527 / 1000000000) (Real.log (329 / 1000)) := by
  have h := reflection_log_13337_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13338_neg : (335387 / 500000000) ≤ -Real.log (1000000 / 1000671) ∧
    -Real.log (1000000 / 1000671) ≤ (26831 / 40000000) := by
  have h := checkLog_sound (w := (671 / 2000671)) (n := 12)
    (lo := (335387 / 500000000)) (hi := (26831 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000671 / 1000000) = 1/(1000000 / 1000671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13338 : Bounds (335387 / 500000000) (26831 / 40000000) (Real.log (1000671 / 1000000)) := by
  have h := reflection_log_13338_neg
  have he : Real.log (1000671 / 1000000) = -Real.log (1000000 / 1000671) := by
    rw [show ((1000671 / 1000000) : ℝ) = ((1000000 / 1000671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13339_neg : (26849 / 40000000) ≤ -Real.log (999329 / 1000000) ∧
    -Real.log (999329 / 1000000) ≤ (335613 / 500000000) := by
  have h := checkLog_sound (w := (671 / 1999329)) (n := 12)
    (lo := (26849 / 40000000)) (hi := (335613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999329) = 1/(999329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13339 : Bounds (-335613 / 500000000) (-26849 / 40000000) (Real.log (999329 / 1000000)) := by
  have h := reflection_log_13339_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13340_neg : (311155161 / 1000000000) ≤ -Real.log (1000000 / 1365001) ∧
    -Real.log (1000000 / 1365001) ≤ (155577581 / 500000000) := by
  have h := checkLog_sound (w := (365001 / 2365001)) (n := 12)
    (lo := (311155161 / 1000000000)) (hi := (155577581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1365001 / 1000000) = 1/(1000000 / 1365001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13340 : Bounds (311155161 / 1000000000) (155577581 / 500000000) (Real.log (1365001 / 1000000)) := by
  have h := reflection_log_13340_neg
  have he : Real.log (1365001 / 1000000) = -Real.log (1000000 / 1365001) := by
    rw [show ((1365001 / 1000000) : ℝ) = ((1000000 / 1365001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13341_neg : (227065927 / 500000000) ≤ -Real.log (634999 / 1000000) ∧
    -Real.log (634999 / 1000000) ≤ (90826371 / 200000000) := by
  have h := checkLog_sound (w := (365001 / 1634999)) (n := 12)
    (lo := (227065927 / 500000000)) (hi := (90826371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 634999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 634999) = 1/(634999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13341 : Bounds (-90826371 / 200000000) (-227065927 / 500000000) (Real.log (634999 / 1000000)) := by
  have h := reflection_log_13341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13342_neg : (156519549 / 500000000) ≤ -Real.log (40000 / 54703) ∧
    -Real.log (40000 / 54703) ≤ (313039099 / 1000000000) := by
  have h := checkLog_sound (w := (14703 / 94703)) (n := 12)
    (lo := (156519549 / 500000000)) (hi := (313039099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54703 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54703 / 40000) = 1/(40000 / 54703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13342 : Bounds (156519549 / 500000000) (313039099 / 1000000000) (Real.log (54703 / 40000)) := by
  have h := reflection_log_13342_neg
  have he : Real.log (54703 / 40000) = -Real.log (40000 / 54703) := by
    rw [show ((54703 / 40000) : ℝ) = ((40000 / 54703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13343_neg : (229096821 / 500000000) ≤ -Real.log (25297 / 40000) ∧
    -Real.log (25297 / 40000) ≤ (458193643 / 1000000000) := by
  have h := checkLog_sound (w := (14703 / 65297)) (n := 12)
    (lo := (229096821 / 500000000)) (hi := (458193643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 25297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 25297) = 1/(25297 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13343 : Bounds (-458193643 / 1000000000) (-229096821 / 500000000) (Real.log (25297 / 40000)) := by
  have h := reflection_log_13343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13344_neg : (9072159 / 62500000) ≤ -Real.log (1383821791 / 1600000000) ∧
    -Real.log (1383821791 / 1600000000) ≤ (29030909 / 200000000) := by
  have h := checkLog_sound (w := (216178209 / 2983821791)) (n := 12)
    (lo := (9072159 / 62500000)) (hi := (29030909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1383821791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1383821791) = 1/(1383821791 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13344 : Bounds (-29030909 / 200000000) (-9072159 / 62500000) (Real.log (1383821791 / 1600000000)) := by
  have h := reflection_log_13344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13345_neg : (142976693 / 1000000000) ≤ -Real.log (866774269999 / 1000000000000) ∧
    -Real.log (866774269999 / 1000000000000) ≤ (71488347 / 500000000) := by
  have h := checkLog_sound (w := (133225730001 / 1866774269999)) (n := 12)
    (lo := (142976693 / 1000000000)) (hi := (71488347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 866774269999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 866774269999) = 1/(866774269999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13345 : Bounds (-71488347 / 500000000) (-142976693 / 1000000000) (Real.log (866774269999 / 1000000000000)) := by
  have h := reflection_log_13345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13346_neg : (153057403 / 200000000) ≤ -Real.log (100000000000 / 214961125923) ∧
    -Real.log (100000000000 / 214961125923) ≤ (765287017 / 1000000000) := by
  have h := checkLog_sound (w := (14961125923 / 414961125923)) (n := 12)
    (lo := (14427967 / 200000000)) (hi := (18034959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((214961125923 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(214961125923 / 200000000000) = 1/(100000000000 / 214961125923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13346 : Bounds (153057403 / 200000000) (765287017 / 1000000000) (Real.log (214961125923 / 100000000000)) := by
  have h := reflection_log_13346_neg
  have he : Real.log (214961125923 / 100000000000) = -Real.log (100000000000 / 214961125923) := by
    rw [show ((214961125923 / 100000000000) : ℝ) = ((100000000000 / 214961125923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13347_neg : (38561637 / 50000000) ≤ -Real.log (250000000000 / 540607581927) ∧
    -Real.log (250000000000 / 540607581927) ≤ (385616371 / 500000000) := by
  have h := checkLog_sound (w := (40607581927 / 1040607581927)) (n := 12)
    (lo := (1952139 / 25000000)) (hi := (78085561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540607581927 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(540607581927 / 500000000000) = 1/(250000000000 / 540607581927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13347 : Bounds (38561637 / 50000000) (385616371 / 500000000) (Real.log (540607581927 / 250000000000)) := by
  have h := reflection_log_13347_neg
  have he : Real.log (540607581927 / 250000000000) = -Real.log (250000000000 / 540607581927) := by
    rw [show ((540607581927 / 250000000000) : ℝ) = ((250000000000 / 540607581927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13348_neg : (403561403 / 250000000) ≤ -Real.log (500000000000 / 2512048192771) ∧
    -Real.log (500000000000 / 2512048192771) ≤ (322849123 / 200000000) := by
  have h := checkLog_sound (w := (512048192771 / 4512048192771)) (n := 12)
    (lo := (56987813 / 250000000)) (hi := (227951253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2512048192771 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2512048192771 / 2000000000000) = 1/(500000000000 / 2512048192771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13348 : Bounds (403561403 / 250000000) (322849123 / 200000000) (Real.log (2512048192771 / 500000000000)) := by
  have h := reflection_log_13348_neg
  have he : Real.log (2512048192771 / 500000000000) = -Real.log (500000000000 / 2512048192771) := by
    rw [show ((2512048192771 / 500000000000) : ℝ) = ((500000000000 / 2512048192771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13349_neg : (50784993 / 31250000) ≤ -Real.log (125000000000 / 634878419453) ∧
    -Real.log (125000000000 / 634878419453) ≤ (1625119779 / 1000000000) := by
  have h := checkLog_sound (w := (134878419453 / 1134878419453)) (n := 12)
    (lo := (29853177 / 125000000)) (hi := (238825417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634878419453 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(634878419453 / 500000000000) = 1/(125000000000 / 634878419453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13349 : Bounds (50784993 / 31250000) (1625119779 / 1000000000) (Real.log (634878419453 / 125000000000)) := by
  have h := reflection_log_13349_neg
  have he : Real.log (634878419453 / 125000000000) = -Real.log (125000000000 / 634878419453) := by
    rw [show ((634878419453 / 125000000000) : ℝ) = ((125000000000 / 634878419453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13350_neg : (128803993 / 250000000) ≤ -Real.log (500 / 837) ∧
    -Real.log (500 / 837) ≤ (515215973 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 1337)) (n := 12)
    (lo := (128803993 / 250000000)) (hi := (515215973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837 / 500) = 1/(500 / 837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13350 : Bounds (128803993 / 250000000) (515215973 / 1000000000) (Real.log (837 / 500)) := by
  have h := reflection_log_13350_neg
  have he : Real.log (837 / 500) = -Real.log (500 / 837) := by
    rw [show ((837 / 500) : ℝ) = ((500 / 837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13351_neg : (1120857897 / 1000000000) ≤ -Real.log (163 / 500) ∧
    -Real.log (163 / 500) ≤ (1120857899 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 413)) (n := 12)
    (lo := (427710717 / 1000000000)) (hi := (213855359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 163) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 163) = 1/(163 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13351 : Bounds (-1120857899 / 1000000000) (-1120857897 / 1000000000) (Real.log (163 / 500)) := by
  have h := reflection_log_13351_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13352_neg : (168443 / 250000000) ≤ -Real.log (500000 / 500337) ∧
    -Real.log (500000 / 500337) ≤ (673773 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 1000337)) (n := 12)
    (lo := (168443 / 250000000)) (hi := (673773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500337 / 500000) = 1/(500000 / 500337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13352 : Bounds (168443 / 250000000) (673773 / 1000000000) (Real.log (500337 / 500000)) := by
  have h := reflection_log_13352_neg
  have he : Real.log (500337 / 500000) = -Real.log (500000 / 500337) := by
    rw [show ((500337 / 500000) : ℝ) = ((500000 / 500337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13353_neg : (674227 / 1000000000) ≤ -Real.log (499663 / 500000) ∧
    -Real.log (499663 / 500000) ≤ (168557 / 250000000) := by
  have h := checkLog_sound (w := (337 / 999663)) (n := 12)
    (lo := (674227 / 1000000000)) (hi := (168557 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499663) = 1/(499663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13353 : Bounds (-168557 / 250000000) (-674227 / 1000000000) (Real.log (499663 / 500000)) := by
  have h := reflection_log_13353_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13354_neg : (312600269 / 1000000000) ≤ -Real.log (40000 / 54679) ∧
    -Real.log (40000 / 54679) ≤ (31260027 / 100000000) := by
  have h := checkLog_sound (w := (14679 / 94679)) (n := 12)
    (lo := (312600269 / 1000000000)) (hi := (31260027 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54679 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54679 / 40000) = 1/(40000 / 54679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13354 : Bounds (312600269 / 1000000000) (31260027 / 100000000) (Real.log (54679 / 40000)) := by
  have h := reflection_log_13354_neg
  have he : Real.log (54679 / 40000) = -Real.log (40000 / 54679) := by
    rw [show ((54679 / 40000) : ℝ) = ((40000 / 54679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13355_neg : (457245363 / 1000000000) ≤ -Real.log (25321 / 40000) ∧
    -Real.log (25321 / 40000) ≤ (114311341 / 250000000) := by
  have h := checkLog_sound (w := (14679 / 65321)) (n := 12)
    (lo := (457245363 / 1000000000)) (hi := (114311341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 25321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 25321) = 1/(25321 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13355 : Bounds (-114311341 / 250000000) (-457245363 / 1000000000) (Real.log (25321 / 40000)) := by
  have h := reflection_log_13355_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13356_neg : (15724403 / 50000000) ≤ -Real.log (500000 / 684779) ∧
    -Real.log (500000 / 684779) ≤ (314488061 / 1000000000) := by
  have h := checkLog_sound (w := (184779 / 1184779)) (n := 12)
    (lo := (15724403 / 50000000)) (hi := (314488061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684779 / 500000) = 1/(500000 / 684779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13356 : Bounds (15724403 / 50000000) (314488061 / 1000000000) (Real.log (684779 / 500000)) := by
  have h := reflection_log_13356_neg
  have he : Real.log (684779 / 500000) = -Real.log (500000 / 684779) := by
    rw [show ((684779 / 500000) : ℝ) = ((500000 / 684779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13357_neg : (230667059 / 500000000) ≤ -Real.log (315221 / 500000) ∧
    -Real.log (315221 / 500000) ≤ (461334119 / 1000000000) := by
  have h := checkLog_sound (w := (184779 / 815221)) (n := 12)
    (lo := (230667059 / 500000000)) (hi := (461334119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 315221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 315221) = 1/(315221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13357 : Bounds (-461334119 / 1000000000) (-230667059 / 500000000) (Real.log (315221 / 500000)) := by
  have h := reflection_log_13357_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13358_neg : (73423029 / 500000000) ≤ -Real.log (215856721159 / 250000000000) ∧
    -Real.log (215856721159 / 250000000000) ≤ (146846059 / 1000000000) := by
  have h := checkLog_sound (w := (34143278841 / 465856721159)) (n := 12)
    (lo := (73423029 / 500000000)) (hi := (146846059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 215856721159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 215856721159) = 1/(215856721159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13358 : Bounds (-146846059 / 1000000000) (-73423029 / 500000000) (Real.log (215856721159 / 250000000000)) := by
  have h := reflection_log_13358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13359_neg : (144645093 / 1000000000) ≤ -Real.log (1384526959 / 1600000000) ∧
    -Real.log (1384526959 / 1600000000) ≤ (72322547 / 500000000) := by
  have h := checkLog_sound (w := (215473041 / 2984526959)) (n := 12)
    (lo := (144645093 / 1000000000)) (hi := (72322547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1384526959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1384526959) = 1/(1384526959 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13359 : Bounds (-72322547 / 500000000) (-144645093 / 1000000000) (Real.log (1384526959 / 1600000000)) := by
  have h := reflection_log_13359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13360_neg : (769845631 / 1000000000) ≤ -Real.log (250000000000 / 539858220449) ∧
    -Real.log (250000000000 / 539858220449) ≤ (769845633 / 1000000000) := by
  have h := checkLog_sound (w := (39858220449 / 1039858220449)) (n := 12)
    (lo := (76698451 / 1000000000)) (hi := (19174613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539858220449 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(539858220449 / 500000000000) = 1/(250000000000 / 539858220449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13360 : Bounds (769845631 / 1000000000) (769845633 / 1000000000) (Real.log (539858220449 / 250000000000)) := by
  have h := reflection_log_13360_neg
  have he : Real.log (539858220449 / 250000000000) = -Real.log (250000000000 / 539858220449) := by
    rw [show ((539858220449 / 250000000000) : ℝ) = ((250000000000 / 539858220449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13361_neg : (775822177 / 1000000000) ≤ -Real.log (250000000000 / 543094368713) ∧
    -Real.log (250000000000 / 543094368713) ≤ (775822179 / 1000000000) := by
  have h := checkLog_sound (w := (43094368713 / 1043094368713)) (n := 12)
    (lo := (82674997 / 1000000000)) (hi := (41337499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543094368713 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(543094368713 / 500000000000) = 1/(250000000000 / 543094368713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13361 : Bounds (775822177 / 1000000000) (775822179 / 1000000000) (Real.log (543094368713 / 250000000000)) := by
  have h := reflection_log_13361_neg
  have he : Real.log (543094368713 / 250000000000) = -Real.log (250000000000 / 543094368713) := by
    rw [show ((543094368713 / 250000000000) : ℝ) = ((250000000000 / 543094368713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13362_neg : (50784993 / 31250000) ≤ -Real.log (500000000000 / 2539513677811) ∧
    -Real.log (500000000000 / 2539513677811) ≤ (1625119779 / 1000000000) := by
  have h := checkLog_sound (w := (539513677811 / 4539513677811)) (n := 12)
    (lo := (29853177 / 125000000)) (hi := (238825417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2539513677811 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2539513677811 / 2000000000000) = 1/(500000000000 / 2539513677811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13362 : Bounds (50784993 / 31250000) (1625119779 / 1000000000) (Real.log (2539513677811 / 500000000000)) := by
  have h := reflection_log_13362_neg
  have he : Real.log (2539513677811 / 500000000000) = -Real.log (500000000000 / 2539513677811) := by
    rw [show ((2539513677811 / 500000000000) : ℝ) = ((500000000000 / 2539513677811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13363_neg : (409018467 / 250000000) ≤ -Real.log (500000000000 / 2567484662577) ∧
    -Real.log (500000000000 / 2567484662577) ≤ (1636073871 / 1000000000) := by
  have h := checkLog_sound (w := (567484662577 / 4567484662577)) (n := 12)
    (lo := (62444877 / 250000000)) (hi := (249779509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2567484662577 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2567484662577 / 2000000000000) = 1/(500000000000 / 2567484662577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13363 : Bounds (409018467 / 250000000) (1636073871 / 1000000000) (Real.log (2567484662577 / 500000000000)) := by
  have h := reflection_log_13363_neg
  have he : Real.log (2567484662577 / 500000000000) = -Real.log (500000000000 / 2567484662577) := by
    rw [show ((2567484662577 / 500000000000) : ℝ) = ((500000000000 / 2567484662577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13364_neg : (258503241 / 500000000) ≤ -Real.log (1000 / 1677) ∧
    -Real.log (1000 / 1677) ≤ (517006483 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 2677)) (n := 12)
    (lo := (258503241 / 500000000)) (hi := (517006483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1677 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1677 / 1000) = 1/(1000 / 1677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13364 : Bounds (258503241 / 500000000) (517006483 / 1000000000) (Real.log (1677 / 1000)) := by
  have h := reflection_log_13364_neg
  have he : Real.log (1677 / 1000) = -Real.log (1000 / 1677) := by
    rw [show ((1677 / 1000) : ℝ) = ((1000 / 1677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13365_neg : (226020591 / 200000000) ≤ -Real.log (323 / 1000) ∧
    -Real.log (323 / 1000) ≤ (1130102957 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 823)) (n := 12)
    (lo := (17478231 / 40000000)) (hi := (3413717 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 323) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 323) = 1/(323 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13365 : Bounds (-1130102957 / 1000000000) (-226020591 / 200000000) (Real.log (323 / 1000)) := by
  have h := reflection_log_13365_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13366_neg : (67677 / 100000000) ≤ -Real.log (1000000 / 1000677) ∧
    -Real.log (1000000 / 1000677) ≤ (676771 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 2000677)) (n := 12)
    (lo := (67677 / 100000000)) (hi := (676771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000677 / 1000000) = 1/(1000000 / 1000677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13366 : Bounds (67677 / 100000000) (676771 / 1000000000) (Real.log (1000677 / 1000000)) := by
  have h := reflection_log_13366_neg
  have he : Real.log (1000677 / 1000000) = -Real.log (1000000 / 1000677) := by
    rw [show ((1000677 / 1000000) : ℝ) = ((1000000 / 1000677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13367_neg : (677229 / 1000000000) ≤ -Real.log (999323 / 1000000) ∧
    -Real.log (999323 / 1000000) ≤ (67723 / 100000000) := by
  have h := checkLog_sound (w := (677 / 1999323)) (n := 12)
    (lo := (677229 / 1000000000)) (hi := (67723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999323) = 1/(999323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13367 : Bounds (-67723 / 100000000) (-677229 / 1000000000) (Real.log (999323 / 1000000)) := by
  have h := reflection_log_13367_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13368_neg : (62809681 / 200000000) ≤ -Real.log (250000 / 342239) ∧
    -Real.log (250000 / 342239) ≤ (157024203 / 500000000) := by
  have h := checkLog_sound (w := (92239 / 592239)) (n := 12)
    (lo := (62809681 / 200000000)) (hi := (157024203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342239 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342239 / 250000) = 1/(250000 / 342239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13368 : Bounds (62809681 / 200000000) (157024203 / 500000000) (Real.log (342239 / 250000)) := by
  have h := reflection_log_13368_neg
  have he : Real.log (342239 / 250000) = -Real.log (250000 / 342239) := by
    rw [show ((342239 / 250000) : ℝ) = ((250000 / 342239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13369_neg : (57547461 / 125000000) ≤ -Real.log (157761 / 250000) ∧
    -Real.log (157761 / 250000) ≤ (460379689 / 1000000000) := by
  have h := checkLog_sound (w := (92239 / 407761)) (n := 12)
    (lo := (57547461 / 125000000)) (hi := (460379689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 157761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 157761) = 1/(157761 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13369 : Bounds (-460379689 / 1000000000) (-57547461 / 125000000) (Real.log (157761 / 250000)) := by
  have h := reflection_log_13369_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13370_neg : (31593857 / 100000000) ≤ -Real.log (500000 / 685773) ∧
    -Real.log (500000 / 685773) ≤ (315938571 / 1000000000) := by
  have h := checkLog_sound (w := (185773 / 1185773)) (n := 12)
    (lo := (31593857 / 100000000)) (hi := (315938571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685773 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685773 / 500000) = 1/(500000 / 685773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13370 : Bounds (31593857 / 100000000) (315938571 / 1000000000) (Real.log (685773 / 500000)) := by
  have h := reflection_log_13370_neg
  have he : Real.log (685773 / 500000) = -Real.log (500000 / 685773) := by
    rw [show ((685773 / 500000) : ℝ) = ((500000 / 685773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13371_neg : (464492443 / 1000000000) ≤ -Real.log (314227 / 500000) ∧
    -Real.log (314227 / 500000) ≤ (116123111 / 250000000) := by
  have h := checkLog_sound (w := (185773 / 814227)) (n := 12)
    (lo := (464492443 / 1000000000)) (hi := (116123111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 314227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 314227) = 1/(314227 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13371 : Bounds (-116123111 / 250000000) (-464492443 / 1000000000) (Real.log (314227 / 500000)) := by
  have h := reflection_log_13371_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13372_neg : (148553873 / 1000000000) ≤ -Real.log (215488392471 / 250000000000) ∧
    -Real.log (215488392471 / 250000000000) ≤ (74276937 / 500000000) := by
  have h := checkLog_sound (w := (34511607529 / 465488392471)) (n := 12)
    (lo := (148553873 / 1000000000)) (hi := (74276937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 215488392471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 215488392471) = 1/(215488392471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13372 : Bounds (-74276937 / 500000000) (-148553873 / 1000000000) (Real.log (215488392471 / 250000000000)) := by
  have h := reflection_log_13372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13373_neg : (73165641 / 500000000) ≤ -Real.log (53991966879 / 62500000000) ∧
    -Real.log (53991966879 / 62500000000) ≤ (146331283 / 1000000000) := by
  have h := checkLog_sound (w := (8508033121 / 116491966879)) (n := 12)
    (lo := (73165641 / 500000000)) (hi := (146331283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 53991966879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 53991966879) = 1/(53991966879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13373 : Bounds (-146331283 / 1000000000) (-73165641 / 500000000) (Real.log (53991966879 / 62500000000)) := by
  have h := reflection_log_13373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13374_neg : (774428093 / 1000000000) ≤ -Real.log (500000000000 / 1084675553527) ∧
    -Real.log (500000000000 / 1084675553527) ≤ (154885619 / 200000000) := by
  have h := checkLog_sound (w := (84675553527 / 2084675553527)) (n := 12)
    (lo := (81280913 / 1000000000)) (hi := (40640457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084675553527 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1084675553527 / 1000000000000) = 1/(500000000000 / 1084675553527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13374 : Bounds (774428093 / 1000000000) (154885619 / 200000000) (Real.log (1084675553527 / 500000000000)) := by
  have h := reflection_log_13374_neg
  have he : Real.log (1084675553527 / 500000000000) = -Real.log (500000000000 / 1084675553527) := by
    rw [show ((1084675553527 / 500000000000) : ℝ) = ((500000000000 / 1084675553527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13375_neg : (780431013 / 1000000000) ≤ -Real.log (125000000000 / 272801589297) ∧
    -Real.log (125000000000 / 272801589297) ≤ (156086203 / 200000000) := by
  have h := checkLog_sound (w := (22801589297 / 522801589297)) (n := 12)
    (lo := (87283833 / 1000000000)) (hi := (43641917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272801589297 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272801589297 / 250000000000) = 1/(125000000000 / 272801589297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13375 : Bounds (780431013 / 1000000000) (156086203 / 200000000) (Real.log (272801589297 / 125000000000)) := by
  have h := reflection_log_13375_neg
  have he : Real.log (272801589297 / 125000000000) = -Real.log (125000000000 / 272801589297) := by
    rw [show ((272801589297 / 125000000000) : ℝ) = ((125000000000 / 272801589297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0209 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13376_neg : (409018467 / 250000000) ≤ -Real.log (31250000000 / 160467791411) ∧
    -Real.log (31250000000 / 160467791411) ≤ (1636073871 / 1000000000) := by
  have h := checkLog_sound (w := (35467791411 / 285467791411)) (n := 12)
    (lo := (62444877 / 250000000)) (hi := (249779509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160467791411 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160467791411 / 125000000000) = 1/(31250000000 / 160467791411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13376 : Bounds (409018467 / 250000000) (1636073871 / 1000000000) (Real.log (160467791411 / 31250000000)) := by
  have h := reflection_log_13376_neg
  have he : Real.log (160467791411 / 31250000000) = -Real.log (31250000000 / 160467791411) := by
    rw [show ((160467791411 / 31250000000) : ℝ) = ((31250000000 / 160467791411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13377_neg : (1647109437 / 1000000000) ≤ -Real.log (500000000000 / 2595975232199) ∧
    -Real.log (500000000000 / 2595975232199) ≤ (5147217 / 3125000) := by
  have h := checkLog_sound (w := (595975232199 / 4595975232199)) (n := 12)
    (lo := (260815077 / 1000000000)) (hi := (130407539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2595975232199 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2595975232199 / 2000000000000) = 1/(500000000000 / 2595975232199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13377 : Bounds (1647109437 / 1000000000) (5147217 / 3125000) (Real.log (2595975232199 / 500000000000)) := by
  have h := reflection_log_13377_neg
  have he : Real.log (2595975232199 / 500000000000) = -Real.log (500000000000 / 2595975232199) := by
    rw [show ((2595975232199 / 500000000000) : ℝ) = ((500000000000 / 2595975232199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13378_neg : (518793793 / 1000000000) ≤ -Real.log (25 / 42) ∧
    -Real.log (25 / 42) ≤ (259396897 / 500000000) := by
  have h := checkLog_sound (w := (17 / 67)) (n := 12)
    (lo := (518793793 / 1000000000)) (hi := (259396897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42 / 25) = 1/(25 / 42) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13378 : Bounds (518793793 / 1000000000) (259396897 / 500000000) (Real.log (42 / 25)) := by
  have h := reflection_log_13378_neg
  have he : Real.log (42 / 25) = -Real.log (25 / 42) := by
    rw [show ((42 / 25) : ℝ) = ((25 / 42) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13379_neg : (569717141 / 500000000) ≤ -Real.log (8 / 25) ∧
    -Real.log (8 / 25) ≤ (284858571 / 250000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 16) = 1/(8 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13379 : Bounds (-284858571 / 250000000) (-569717141 / 500000000) (Real.log (8 / 25)) := by
  have h := reflection_log_13379_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13380_neg : (84971 / 125000000) ≤ -Real.log (25000 / 25017) ∧
    -Real.log (25000 / 25017) ≤ (679769 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 50017)) (n := 12)
    (lo := (84971 / 125000000)) (hi := (679769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25017 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25017 / 25000) = 1/(25000 / 25017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13380 : Bounds (84971 / 125000000) (679769 / 1000000000) (Real.log (25017 / 25000)) := by
  have h := reflection_log_13380_neg
  have he : Real.log (25017 / 25000) = -Real.log (25000 / 25017) := by
    rw [show ((25017 / 25000) : ℝ) = ((25000 / 25017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13381_neg : (680231 / 1000000000) ≤ -Real.log (24983 / 25000) ∧
    -Real.log (24983 / 25000) ≤ (85029 / 125000000) := by
  have h := checkLog_sound (w := (17 / 49983)) (n := 12)
    (lo := (680231 / 1000000000)) (hi := (85029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 24983) = 1/(24983 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13381 : Bounds (-85029 / 125000000) (-680231 / 1000000000) (Real.log (24983 / 25000)) := by
  have h := reflection_log_13381_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13382_neg : (39437353 / 125000000) ≤ -Real.log (1000000 / 1370943) ∧
    -Real.log (1000000 / 1370943) ≤ (12619953 / 40000000) := by
  have h := checkLog_sound (w := (370943 / 2370943)) (n := 12)
    (lo := (39437353 / 125000000)) (hi := (12619953 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1370943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1370943 / 1000000) = 1/(1000000 / 1370943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13382 : Bounds (39437353 / 125000000) (12619953 / 40000000) (Real.log (1370943 / 1000000)) := by
  have h := reflection_log_13382_neg
  have he : Real.log (1370943 / 1000000) = -Real.log (1000000 / 1370943) := by
    rw [show ((1370943 / 1000000) : ℝ) = ((1000000 / 1370943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13383_neg : (231766703 / 500000000) ≤ -Real.log (629057 / 1000000) ∧
    -Real.log (629057 / 1000000) ≤ (463533407 / 1000000000) := by
  have h := checkLog_sound (w := (370943 / 1629057)) (n := 12)
    (lo := (231766703 / 500000000)) (hi := (463533407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 629057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 629057) = 1/(629057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13383 : Bounds (-463533407 / 1000000000) (-231766703 / 500000000) (Real.log (629057 / 1000000)) := by
  have h := reflection_log_13383_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13384_neg : (79347837 / 250000000) ≤ -Real.log (50000 / 68677) ∧
    -Real.log (50000 / 68677) ≤ (317391349 / 1000000000) := by
  have h := checkLog_sound (w := (18677 / 118677)) (n := 12)
    (lo := (79347837 / 250000000)) (hi := (317391349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68677 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68677 / 50000) = 1/(50000 / 68677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13384 : Bounds (79347837 / 250000000) (317391349 / 1000000000) (Real.log (68677 / 50000)) := by
  have h := reflection_log_13384_neg
  have he : Real.log (68677 / 50000) = -Real.log (50000 / 68677) := by
    rw [show ((68677 / 50000) : ℝ) = ((50000 / 68677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13385_neg : (467670353 / 1000000000) ≤ -Real.log (31323 / 50000) ∧
    -Real.log (31323 / 50000) ≤ (233835177 / 500000000) := by
  have h := checkLog_sound (w := (18677 / 81323)) (n := 12)
    (lo := (467670353 / 1000000000)) (hi := (233835177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 31323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 31323) = 1/(31323 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13385 : Bounds (-233835177 / 500000000) (-467670353 / 1000000000) (Real.log (31323 / 50000)) := by
  have h := reflection_log_13385_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13386_neg : (37569751 / 250000000) ≤ -Real.log (2151169671 / 2500000000) ∧
    -Real.log (2151169671 / 2500000000) ≤ (30055801 / 200000000) := by
  have h := checkLog_sound (w := (348830329 / 4651169671)) (n := 12)
    (lo := (37569751 / 250000000)) (hi := (30055801 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2151169671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2151169671) = 1/(2151169671 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13386 : Bounds (-30055801 / 200000000) (-37569751 / 250000000) (Real.log (2151169671 / 2500000000)) := by
  have h := reflection_log_13386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13387_neg : (74017291 / 500000000) ≤ -Real.log (862401290751 / 1000000000000) ∧
    -Real.log (862401290751 / 1000000000000) ≤ (148034583 / 1000000000) := by
  have h := checkLog_sound (w := (137598709249 / 1862401290751)) (n := 12)
    (lo := (74017291 / 500000000)) (hi := (148034583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 862401290751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 862401290751) = 1/(862401290751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13387 : Bounds (-148034583 / 1000000000) (-74017291 / 500000000) (Real.log (862401290751 / 1000000000000)) := by
  have h := reflection_log_13387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13388_neg : (77903223 / 100000000) ≤ -Real.log (31250000000 / 68105066393) ∧
    -Real.log (31250000000 / 68105066393) ≤ (97379029 / 125000000) := by
  have h := checkLog_sound (w := (5605066393 / 130605066393)) (n := 12)
    (lo := (1717701 / 20000000)) (hi := (85885051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68105066393 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68105066393 / 62500000000) = 1/(31250000000 / 68105066393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13388 : Bounds (77903223 / 100000000) (97379029 / 125000000) (Real.log (68105066393 / 31250000000)) := by
  have h := reflection_log_13388_neg
  have he : Real.log (68105066393 / 31250000000) = -Real.log (31250000000 / 68105066393) := by
    rw [show ((68105066393 / 31250000000) : ℝ) = ((31250000000 / 68105066393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13389_neg : (785061701 / 1000000000) ≤ -Real.log (250000000000 / 548135555343) ∧
    -Real.log (250000000000 / 548135555343) ≤ (785061703 / 1000000000) := by
  have h := checkLog_sound (w := (48135555343 / 1048135555343)) (n := 12)
    (lo := (91914521 / 1000000000)) (hi := (45957261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548135555343 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(548135555343 / 500000000000) = 1/(250000000000 / 548135555343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13389 : Bounds (785061701 / 1000000000) (785061703 / 1000000000) (Real.log (548135555343 / 250000000000)) := by
  have h := reflection_log_13389_neg
  have he : Real.log (548135555343 / 250000000000) = -Real.log (250000000000 / 548135555343) := by
    rw [show ((548135555343 / 250000000000) : ℝ) = ((250000000000 / 548135555343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13390_neg : (1647109437 / 1000000000) ≤ -Real.log (250000000000 / 1297987616099) ∧
    -Real.log (250000000000 / 1297987616099) ≤ (5147217 / 3125000) := by
  have h := checkLog_sound (w := (297987616099 / 2297987616099)) (n := 12)
    (lo := (260815077 / 1000000000)) (hi := (130407539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297987616099 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1297987616099 / 1000000000000) = 1/(250000000000 / 1297987616099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13390 : Bounds (1647109437 / 1000000000) (5147217 / 3125000) (Real.log (1297987616099 / 250000000000)) := by
  have h := reflection_log_13390_neg
  have he : Real.log (1297987616099 / 250000000000) = -Real.log (250000000000 / 1297987616099) := by
    rw [show ((1297987616099 / 250000000000) : ℝ) = ((250000000000 / 1297987616099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13391_neg : (66329123 / 40000000) ≤ -Real.log (4 / 21) ∧
    -Real.log (4 / 21) ≤ (829114039 / 500000000) := by
  have h := checkLog_sound (w := (5 / 37)) (n := 12)
    (lo := (54386743 / 200000000)) (hi := (67983429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 16) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(21 / 16) = 1/(4 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13391 : Bounds (66329123 / 40000000) (829114039 / 500000000) (Real.log (21 / 4)) := by
  have h := reflection_log_13391_neg
  have he : Real.log (21 / 4) = -Real.log (4 / 21) := by
    rw [show ((21 / 4) : ℝ) = ((4 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13392_neg : (104115583 / 200000000) ≤ -Real.log (1000 / 1683) ∧
    -Real.log (1000 / 1683) ≤ (130144479 / 250000000) := by
  have h := checkLog_sound (w := (683 / 2683)) (n := 12)
    (lo := (104115583 / 200000000)) (hi := (130144479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1683 / 1000) = 1/(1000 / 1683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13392 : Bounds (104115583 / 200000000) (130144479 / 250000000) (Real.log (1683 / 1000)) := by
  have h := reflection_log_13392_neg
  have he : Real.log (1683 / 1000) = -Real.log (1000 / 1683) := by
    rw [show ((1683 / 1000) : ℝ) = ((1000 / 1683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13393_neg : (4487709 / 3906250) ≤ -Real.log (317 / 1000) ∧
    -Real.log (317 / 1000) ≤ (574426753 / 500000000) := by
  have h := checkLog_sound (w := (183 / 817)) (n := 12)
    (lo := (113926581 / 250000000)) (hi := (18228253 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 317) = 1/(317 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13393 : Bounds (-574426753 / 500000000) (-4487709 / 3906250) (Real.log (317 / 1000)) := by
  have h := reflection_log_13393_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13394_neg : (341383 / 500000000) ≤ -Real.log (1000000 / 1000683) ∧
    -Real.log (1000000 / 1000683) ≤ (682767 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 2000683)) (n := 12)
    (lo := (341383 / 500000000)) (hi := (682767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000683 / 1000000) = 1/(1000000 / 1000683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13394 : Bounds (341383 / 500000000) (682767 / 1000000000) (Real.log (1000683 / 1000000)) := by
  have h := reflection_log_13394_neg
  have he : Real.log (1000683 / 1000000) = -Real.log (1000000 / 1000683) := by
    rw [show ((1000683 / 1000000) : ℝ) = ((1000000 / 1000683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13395_neg : (683233 / 1000000000) ≤ -Real.log (999317 / 1000000) ∧
    -Real.log (999317 / 1000000) ≤ (341617 / 500000000) := by
  have h := checkLog_sound (w := (683 / 1999317)) (n := 12)
    (lo := (683233 / 1000000000)) (hi := (341617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999317) = 1/(999317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13395 : Bounds (-341617 / 500000000) (-683233 / 1000000000) (Real.log (999317 / 1000000)) := by
  have h := reflection_log_13395_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13396_neg : (1238089 / 3906250) ≤ -Real.log (200000 / 274587) ∧
    -Real.log (200000 / 274587) ≤ (63390157 / 200000000) := by
  have h := checkLog_sound (w := (74587 / 474587)) (n := 12)
    (lo := (1238089 / 3906250)) (hi := (63390157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274587 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274587 / 200000) = 1/(200000 / 274587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13396 : Bounds (1238089 / 3906250) (63390157 / 200000000) (Real.log (274587 / 200000)) := by
  have h := reflection_log_13396_neg
  have he : Real.log (274587 / 200000) = -Real.log (200000 / 274587) := by
    rw [show ((274587 / 200000) : ℝ) = ((200000 / 274587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13397_neg : (18668203 / 40000000) ≤ -Real.log (125413 / 200000) ∧
    -Real.log (125413 / 200000) ≤ (116676269 / 250000000) := by
  have h := checkLog_sound (w := (74587 / 325413)) (n := 12)
    (lo := (18668203 / 40000000)) (hi := (116676269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 125413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 125413) = 1/(125413 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13397 : Bounds (-116676269 / 250000000) (-18668203 / 40000000) (Real.log (125413 / 200000)) := by
  have h := reflection_log_13397_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13398_neg : (318846381 / 1000000000) ≤ -Real.log (50000 / 68777) ∧
    -Real.log (50000 / 68777) ≤ (159423191 / 500000000) := by
  have h := checkLog_sound (w := (18777 / 118777)) (n := 12)
    (lo := (318846381 / 1000000000)) (hi := (159423191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68777 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68777 / 50000) = 1/(50000 / 68777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13398 : Bounds (318846381 / 1000000000) (159423191 / 500000000) (Real.log (68777 / 50000)) := by
  have h := reflection_log_13398_neg
  have he : Real.log (68777 / 50000) = -Real.log (50000 / 68777) := by
    rw [show ((68777 / 50000) : ℝ) = ((50000 / 68777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13399_neg : (235434001 / 500000000) ≤ -Real.log (31223 / 50000) ∧
    -Real.log (31223 / 50000) ≤ (470868003 / 1000000000) := by
  have h := checkLog_sound (w := (18777 / 81223)) (n := 12)
    (lo := (235434001 / 500000000)) (hi := (470868003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 31223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 31223) = 1/(31223 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13399 : Bounds (-470868003 / 1000000000) (-235434001 / 500000000) (Real.log (31223 / 50000)) := by
  have h := reflection_log_13399_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13400_neg : (152021621 / 1000000000) ≤ -Real.log (2147424271 / 2500000000) ∧
    -Real.log (2147424271 / 2500000000) ≤ (76010811 / 500000000) := by
  have h := checkLog_sound (w := (352575729 / 4647424271)) (n := 12)
    (lo := (152021621 / 1000000000)) (hi := (76010811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2147424271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2147424271) = 1/(2147424271 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13400 : Bounds (-76010811 / 500000000) (-152021621 / 1000000000) (Real.log (2147424271 / 2500000000)) := by
  have h := reflection_log_13400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13401_neg : (149754291 / 1000000000) ≤ -Real.log (34436779431 / 40000000000) ∧
    -Real.log (34436779431 / 40000000000) ≤ (37438573 / 250000000) := by
  have h := checkLog_sound (w := (5563220569 / 74436779431)) (n := 12)
    (lo := (149754291 / 1000000000)) (hi := (37438573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 34436779431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 34436779431) = 1/(34436779431 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13401 : Bounds (-37438573 / 250000000) (-149754291 / 1000000000) (Real.log (34436779431 / 40000000000)) := by
  have h := reflection_log_13401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13402_neg : (391827929 / 500000000) ≤ -Real.log (500000000000 / 1094731008747) ∧
    -Real.log (500000000000 / 1094731008747) ≤ (39182793 / 50000000) := by
  have h := checkLog_sound (w := (94731008747 / 2094731008747)) (n := 12)
    (lo := (45254339 / 500000000)) (hi := (90508679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094731008747 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1094731008747 / 1000000000000) = 1/(500000000000 / 1094731008747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13402 : Bounds (391827929 / 500000000) (39182793 / 50000000) (Real.log (1094731008747 / 500000000000)) := by
  have h := reflection_log_13402_neg
  have he : Real.log (1094731008747 / 500000000000) = -Real.log (500000000000 / 1094731008747) := by
    rw [show ((1094731008747 / 500000000000) : ℝ) = ((500000000000 / 1094731008747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13403_neg : (789714383 / 1000000000) ≤ -Real.log (500000000000 / 1101383595427) ∧
    -Real.log (500000000000 / 1101383595427) ≤ (157942877 / 200000000) := by
  have h := checkLog_sound (w := (101383595427 / 2101383595427)) (n := 12)
    (lo := (96567203 / 1000000000)) (hi := (24141801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101383595427 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1101383595427 / 1000000000000) = 1/(500000000000 / 1101383595427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13403 : Bounds (789714383 / 1000000000) (157942877 / 200000000) (Real.log (1101383595427 / 500000000000)) := by
  have h := reflection_log_13403_neg
  have he : Real.log (1101383595427 / 500000000000) = -Real.log (500000000000 / 1101383595427) := by
    rw [show ((1101383595427 / 500000000000) : ℝ) = ((500000000000 / 1101383595427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13404_neg : (1669431419 / 1000000000) ≤ -Real.log (500000000000 / 2654574132493) ∧
    -Real.log (500000000000 / 2654574132493) ≤ (834715711 / 500000000) := by
  have h := checkLog_sound (w := (654574132493 / 4654574132493)) (n := 12)
    (lo := (283137059 / 1000000000)) (hi := (14156853 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2654574132493 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2654574132493 / 2000000000000) = 1/(500000000000 / 2654574132493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13404 : Bounds (1669431419 / 1000000000) (834715711 / 500000000) (Real.log (2654574132493 / 500000000000)) := by
  have h := reflection_log_13404_neg
  have he : Real.log (2654574132493 / 500000000000) = -Real.log (500000000000 / 2654574132493) := by
    rw [show ((2654574132493 / 500000000000) : ℝ) = ((500000000000 / 2654574132493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13405_neg : (522358859 / 1000000000) ≤ -Real.log (500 / 843) ∧
    -Real.log (500 / 843) ≤ (26117943 / 50000000) := by
  have h := checkLog_sound (w := (343 / 1343)) (n := 12)
    (lo := (522358859 / 1000000000)) (hi := (26117943 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843 / 500) = 1/(500 / 843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13405 : Bounds (522358859 / 1000000000) (26117943 / 50000000) (Real.log (843 / 500)) := by
  have h := reflection_log_13405_neg
  have he : Real.log (843 / 500) = -Real.log (500 / 843) := by
    rw [show ((843 / 500) : ℝ) = ((500 / 843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13406_neg : (289590573 / 250000000) ≤ -Real.log (157 / 500) ∧
    -Real.log (157 / 500) ≤ (579181147 / 500000000) := by
  have h := checkLog_sound (w := (93 / 407)) (n := 12)
    (lo := (58151889 / 125000000)) (hi := (465215113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 157) = 1/(157 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13406 : Bounds (-579181147 / 500000000) (-289590573 / 250000000) (Real.log (157 / 500)) := by
  have h := reflection_log_13406_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13407_neg : (171441 / 250000000) ≤ -Real.log (500000 / 500343) ∧
    -Real.log (500000 / 500343) ≤ (137153 / 200000000) := by
  have h := checkLog_sound (w := (343 / 1000343)) (n := 12)
    (lo := (171441 / 250000000)) (hi := (137153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500343 / 500000) = 1/(500000 / 500343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13407 : Bounds (171441 / 250000000) (137153 / 200000000) (Real.log (500343 / 500000)) := by
  have h := reflection_log_13407_neg
  have he : Real.log (500343 / 500000) = -Real.log (500000 / 500343) := by
    rw [show ((500343 / 500000) : ℝ) = ((500000 / 500343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13408_neg : (137247 / 200000000) ≤ -Real.log (499657 / 500000) ∧
    -Real.log (499657 / 500000) ≤ (171559 / 250000000) := by
  have h := checkLog_sound (w := (343 / 999657)) (n := 12)
    (lo := (137247 / 200000000)) (hi := (171559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499657) = 1/(499657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13408 : Bounds (-171559 / 250000000) (-137247 / 200000000) (Real.log (499657 / 500000)) := by
  have h := reflection_log_13408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13409_neg : (159202501 / 500000000) ≤ -Real.log (1000000 / 1374933) ∧
    -Real.log (1000000 / 1374933) ≤ (318405003 / 1000000000) := by
  have h := checkLog_sound (w := (374933 / 2374933)) (n := 12)
    (lo := (159202501 / 500000000)) (hi := (318405003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1374933 / 1000000) = 1/(1000000 / 1374933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13409 : Bounds (159202501 / 500000000) (318405003 / 1000000000) (Real.log (1374933 / 1000000)) := by
  have h := reflection_log_13409_neg
  have he : Real.log (1374933 / 1000000) = -Real.log (1000000 / 1374933) := by
    rw [show ((1374933 / 1000000) : ℝ) = ((1000000 / 1374933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13410_neg : (234948217 / 500000000) ≤ -Real.log (625067 / 1000000) ∧
    -Real.log (625067 / 1000000) ≤ (93979287 / 200000000) := by
  have h := checkLog_sound (w := (374933 / 1625067)) (n := 12)
    (lo := (234948217 / 500000000)) (hi := (93979287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 625067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 625067) = 1/(625067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13410 : Bounds (-93979287 / 200000000) (-234948217 / 500000000) (Real.log (625067 / 1000000)) := by
  have h := reflection_log_13410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13411_neg : (64060731 / 200000000) ≤ -Real.log (500000 / 688773) ∧
    -Real.log (500000 / 688773) ≤ (40037957 / 125000000) := by
  have h := checkLog_sound (w := (188773 / 1188773)) (n := 12)
    (lo := (64060731 / 200000000)) (hi := (40037957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688773 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688773 / 500000) = 1/(500000 / 688773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13411 : Bounds (64060731 / 200000000) (40037957 / 125000000) (Real.log (688773 / 500000)) := by
  have h := reflection_log_13411_neg
  have he : Real.log (688773 / 500000) = -Real.log (500000 / 688773) := by
    rw [show ((688773 / 500000) : ℝ) = ((500000 / 688773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13412_neg : (118521387 / 250000000) ≤ -Real.log (311227 / 500000) ∧
    -Real.log (311227 / 500000) ≤ (474085549 / 1000000000) := by
  have h := checkLog_sound (w := (188773 / 811227)) (n := 12)
    (lo := (118521387 / 250000000)) (hi := (474085549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 311227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 311227) = 1/(311227 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13412 : Bounds (-474085549 / 1000000000) (-118521387 / 250000000) (Real.log (311227 / 500000)) := by
  have h := reflection_log_13412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13413_neg : (153781893 / 1000000000) ≤ -Real.log (214364754471 / 250000000000) ∧
    -Real.log (214364754471 / 250000000000) ≤ (76890947 / 500000000) := by
  have h := checkLog_sound (w := (35635245529 / 464364754471)) (n := 12)
    (lo := (153781893 / 1000000000)) (hi := (76890947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 214364754471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 214364754471) = 1/(214364754471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13413 : Bounds (-76890947 / 500000000) (-153781893 / 1000000000) (Real.log (214364754471 / 250000000000)) := by
  have h := reflection_log_13413_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13414_neg : (18936429 / 125000000) ≤ -Real.log (859425245511 / 1000000000000) ∧
    -Real.log (859425245511 / 1000000000000) ≤ (151491433 / 1000000000) := by
  have h := checkLog_sound (w := (140574754489 / 1859425245511)) (n := 12)
    (lo := (18936429 / 125000000)) (hi := (151491433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 859425245511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 859425245511) = 1/(859425245511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13414 : Bounds (-151491433 / 1000000000) (-18936429 / 125000000) (Real.log (859425245511 / 1000000000000)) := by
  have h := reflection_log_13414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13415_neg : (788301437 / 1000000000) ≤ -Real.log (31250000000 / 68739281149) ∧
    -Real.log (31250000000 / 68739281149) ≤ (788301439 / 1000000000) := by
  have h := checkLog_sound (w := (6239281149 / 131239281149)) (n := 12)
    (lo := (95154257 / 1000000000)) (hi := (47577129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68739281149 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68739281149 / 62500000000) = 1/(31250000000 / 68739281149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13415 : Bounds (788301437 / 1000000000) (788301439 / 1000000000) (Real.log (68739281149 / 31250000000)) := by
  have h := reflection_log_13415_neg
  have he : Real.log (68739281149 / 31250000000) = -Real.log (31250000000 / 68739281149) := by
    rw [show ((68739281149 / 31250000000) : ℝ) = ((31250000000 / 68739281149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13416_neg : (794389203 / 1000000000) ≤ -Real.log (500000000000 / 1106544419347) ∧
    -Real.log (500000000000 / 1106544419347) ≤ (158877841 / 200000000) := by
  have h := checkLog_sound (w := (106544419347 / 2106544419347)) (n := 12)
    (lo := (101242023 / 1000000000)) (hi := (12655253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106544419347 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1106544419347 / 1000000000000) = 1/(500000000000 / 1106544419347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13416 : Bounds (794389203 / 1000000000) (158877841 / 200000000) (Real.log (1106544419347 / 500000000000)) := by
  have h := reflection_log_13416_neg
  have he : Real.log (1106544419347 / 500000000000) = -Real.log (500000000000 / 1106544419347) := by
    rw [show ((1106544419347 / 500000000000) : ℝ) = ((500000000000 / 1106544419347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13417_neg : (1669431419 / 1000000000) ≤ -Real.log (125000000000 / 663643533123) ∧
    -Real.log (125000000000 / 663643533123) ≤ (834715711 / 500000000) := by
  have h := checkLog_sound (w := (163643533123 / 1163643533123)) (n := 12)
    (lo := (283137059 / 1000000000)) (hi := (14156853 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663643533123 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(663643533123 / 500000000000) = 1/(125000000000 / 663643533123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13417 : Bounds (1669431419 / 1000000000) (834715711 / 500000000) (Real.log (663643533123 / 125000000000)) := by
  have h := reflection_log_13417_neg
  have he : Real.log (663643533123 / 125000000000) = -Real.log (125000000000 / 663643533123) := by
    rw [show ((663643533123 / 125000000000) : ℝ) = ((125000000000 / 663643533123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13418_neg : (1680721151 / 1000000000) ≤ -Real.log (500000000000 / 2684713375797) ∧
    -Real.log (500000000000 / 2684713375797) ≤ (840360577 / 500000000) := by
  have h := checkLog_sound (w := (684713375797 / 4684713375797)) (n := 12)
    (lo := (294426791 / 1000000000)) (hi := (36803349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2684713375797 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2684713375797 / 2000000000000) = 1/(500000000000 / 2684713375797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13418 : Bounds (1680721151 / 1000000000) (840360577 / 500000000) (Real.log (2684713375797 / 500000000000)) := by
  have h := reflection_log_13418_neg
  have he : Real.log (2684713375797 / 500000000000) = -Real.log (500000000000 / 2684713375797) := by
    rw [show ((2684713375797 / 500000000000) : ℝ) = ((500000000000 / 2684713375797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13419_neg : (524136637 / 1000000000) ≤ -Real.log (1000 / 1689) ∧
    -Real.log (1000 / 1689) ≤ (262068319 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2689)) (n := 12)
    (lo := (524136637 / 1000000000)) (hi := (262068319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1689 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1689 / 1000) = 1/(1000 / 1689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13419 : Bounds (524136637 / 1000000000) (262068319 / 500000000) (Real.log (1689 / 1000)) := by
  have h := reflection_log_13419_neg
  have he : Real.log (1689 / 1000) = -Real.log (1000 / 1689) := by
    rw [show ((1689 / 1000) : ℝ) = ((1000 / 1689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13420_neg : (583981183 / 500000000) ≤ -Real.log (311 / 1000) ∧
    -Real.log (311 / 1000) ≤ (4562353 / 3906250) := by
  have h := checkLog_sound (w := (189 / 811)) (n := 12)
    (lo := (237407593 / 500000000)) (hi := (474815187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 311) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 311) = 1/(311 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13420 : Bounds (-4562353 / 3906250) (-583981183 / 500000000) (Real.log (311 / 1000)) := by
  have h := reflection_log_13420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13421_neg : (344381 / 500000000) ≤ -Real.log (1000000 / 1000689) ∧
    -Real.log (1000000 / 1000689) ≤ (688763 / 1000000000) := by
  have h := checkLog_sound (w := (689 / 2000689)) (n := 12)
    (lo := (344381 / 500000000)) (hi := (688763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000689 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000689 / 1000000) = 1/(1000000 / 1000689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13421 : Bounds (344381 / 500000000) (688763 / 1000000000) (Real.log (1000689 / 1000000)) := by
  have h := reflection_log_13421_neg
  have he : Real.log (1000689 / 1000000) = -Real.log (1000000 / 1000689) := by
    rw [show ((1000689 / 1000000) : ℝ) = ((1000000 / 1000689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13422_neg : (689237 / 1000000000) ≤ -Real.log (999311 / 1000000) ∧
    -Real.log (999311 / 1000000) ≤ (344619 / 500000000) := by
  have h := checkLog_sound (w := (689 / 1999311)) (n := 12)
    (lo := (689237 / 1000000000)) (hi := (344619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999311) = 1/(999311 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13422 : Bounds (-344619 / 500000000) (-689237 / 1000000000) (Real.log (999311 / 1000000)) := by
  have h := reflection_log_13422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13423_neg : (319862193 / 1000000000) ≤ -Real.log (500000 / 688469) ∧
    -Real.log (500000 / 688469) ≤ (159931097 / 500000000) := by
  have h := checkLog_sound (w := (188469 / 1188469)) (n := 12)
    (lo := (319862193 / 1000000000)) (hi := (159931097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688469 / 500000) = 1/(500000 / 688469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13423 : Bounds (319862193 / 1000000000) (159931097 / 500000000) (Real.log (688469 / 500000)) := by
  have h := reflection_log_13423_neg
  have he : Real.log (688469 / 500000) = -Real.log (500000 / 688469) := by
    rw [show ((688469 / 500000) : ℝ) = ((500000 / 688469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13424_neg : (236554623 / 500000000) ≤ -Real.log (311531 / 500000) ∧
    -Real.log (311531 / 500000) ≤ (473109247 / 1000000000) := by
  have h := checkLog_sound (w := (188469 / 811531)) (n := 12)
    (lo := (236554623 / 500000000)) (hi := (473109247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 311531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 311531) = 1/(311531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13424 : Bounds (-473109247 / 1000000000) (-236554623 / 500000000) (Real.log (311531 / 500000)) := by
  have h := reflection_log_13424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13425_neg : (160881941 / 500000000) ≤ -Real.log (1000000 / 1379559) ∧
    -Real.log (1000000 / 1379559) ≤ (321763883 / 1000000000) := by
  have h := checkLog_sound (w := (379559 / 2379559)) (n := 12)
    (lo := (160881941 / 500000000)) (hi := (321763883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1379559 / 1000000) = 1/(1000000 / 1379559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13425 : Bounds (160881941 / 500000000) (321763883 / 1000000000) (Real.log (1379559 / 1000000)) := by
  have h := reflection_log_13425_neg
  have he : Real.log (1379559 / 1000000) = -Real.log (1000000 / 1379559) := by
    rw [show ((1379559 / 1000000) : ℝ) = ((1000000 / 1379559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13426_neg : (477324763 / 1000000000) ≤ -Real.log (620441 / 1000000) ∧
    -Real.log (620441 / 1000000) ≤ (119331191 / 250000000) := by
  have h := checkLog_sound (w := (379559 / 1620441)) (n := 12)
    (lo := (477324763 / 1000000000)) (hi := (119331191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 620441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 620441) = 1/(620441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13426 : Bounds (-119331191 / 250000000) (-477324763 / 1000000000) (Real.log (620441 / 1000000)) := by
  have h := reflection_log_13426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13427_neg : (1944511 / 12500000) ≤ -Real.log (855934965519 / 1000000000000) ∧
    -Real.log (855934965519 / 1000000000000) ≤ (155560881 / 1000000000) := by
  have h := checkLog_sound (w := (144065034481 / 1855934965519)) (n := 12)
    (lo := (1944511 / 12500000)) (hi := (155560881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 855934965519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 855934965519) = 1/(855934965519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13427 : Bounds (-155560881 / 1000000000) (-1944511 / 12500000) (Real.log (855934965519 / 1000000000000)) := by
  have h := reflection_log_13427_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13428_neg : (153247053 / 1000000000) ≤ -Real.log (214479436039 / 250000000000) ∧
    -Real.log (214479436039 / 250000000000) ≤ (76623527 / 500000000) := by
  have h := checkLog_sound (w := (35520563961 / 464479436039)) (n := 12)
    (lo := (153247053 / 1000000000)) (hi := (76623527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 214479436039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 214479436039) = 1/(214479436039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13428 : Bounds (-76623527 / 500000000) (-153247053 / 1000000000) (Real.log (214479436039 / 250000000000)) := by
  have h := reflection_log_13428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13429_neg : (792971439 / 1000000000) ≤ -Real.log (500000000000 / 1104976711787) ∧
    -Real.log (500000000000 / 1104976711787) ≤ (792971441 / 1000000000) := by
  have h := checkLog_sound (w := (104976711787 / 2104976711787)) (n := 12)
    (lo := (99824259 / 1000000000)) (hi := (4991213 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104976711787 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1104976711787 / 1000000000000) = 1/(500000000000 / 1104976711787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13429 : Bounds (792971439 / 1000000000) (792971441 / 1000000000) (Real.log (1104976711787 / 500000000000)) := by
  have h := reflection_log_13429_neg
  have he : Real.log (1104976711787 / 500000000000) = -Real.log (500000000000 / 1104976711787) := by
    rw [show ((1104976711787 / 500000000000) : ℝ) = ((500000000000 / 1104976711787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13430_neg : (159817729 / 200000000) ≤ -Real.log (250000000000 / 555878399397) ∧
    -Real.log (250000000000 / 555878399397) ≤ (799088647 / 1000000000) := by
  have h := checkLog_sound (w := (55878399397 / 1055878399397)) (n := 12)
    (lo := (21188293 / 200000000)) (hi := (52970733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555878399397 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(555878399397 / 500000000000) = 1/(250000000000 / 555878399397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13430 : Bounds (159817729 / 200000000) (799088647 / 1000000000) (Real.log (555878399397 / 250000000000)) := by
  have h := reflection_log_13430_neg
  have he : Real.log (555878399397 / 250000000000) = -Real.log (250000000000 / 555878399397) := by
    rw [show ((555878399397 / 250000000000) : ℝ) = ((250000000000 / 555878399397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13431_neg : (1680721151 / 1000000000) ≤ -Real.log (125000000000 / 671178343949) ∧
    -Real.log (125000000000 / 671178343949) ≤ (840360577 / 500000000) := by
  have h := checkLog_sound (w := (171178343949 / 1171178343949)) (n := 12)
    (lo := (294426791 / 1000000000)) (hi := (36803349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671178343949 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(671178343949 / 500000000000) = 1/(125000000000 / 671178343949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13431 : Bounds (1680721151 / 1000000000) (840360577 / 500000000) (Real.log (671178343949 / 125000000000)) := by
  have h := reflection_log_13431_neg
  have he : Real.log (671178343949 / 125000000000) = -Real.log (125000000000 / 671178343949) := by
    rw [show ((671178343949 / 125000000000) : ℝ) = ((125000000000 / 671178343949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13432_neg : (1692099003 / 1000000000) ≤ -Real.log (250000000000 / 1357717041801) ∧
    -Real.log (250000000000 / 1357717041801) ≤ (846049503 / 500000000) := by
  have h := checkLog_sound (w := (357717041801 / 2357717041801)) (n := 12)
    (lo := (305804643 / 1000000000)) (hi := (76451161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357717041801 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1357717041801 / 1000000000000) = 1/(250000000000 / 1357717041801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13432 : Bounds (1692099003 / 1000000000) (846049503 / 500000000) (Real.log (1357717041801 / 250000000000)) := by
  have h := reflection_log_13432_neg
  have he : Real.log (1357717041801 / 250000000000) = -Real.log (250000000000 / 1357717041801) := by
    rw [show ((1357717041801 / 250000000000) : ℝ) = ((250000000000 / 1357717041801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13433_neg : (525911261 / 1000000000) ≤ -Real.log (250 / 423) ∧
    -Real.log (250 / 423) ≤ (262955631 / 500000000) := by
  have h := checkLog_sound (w := (173 / 673)) (n := 12)
    (lo := (525911261 / 1000000000)) (hi := (262955631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((423 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(423 / 250) = 1/(250 / 423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13433 : Bounds (525911261 / 1000000000) (262955631 / 500000000) (Real.log (423 / 250)) := by
  have h := reflection_log_13433_neg
  have he : Real.log (423 / 250) = -Real.log (250 / 423) := by
    rw [show ((423 / 250) : ℝ) = ((250 / 423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13434_neg : (235531099 / 200000000) ≤ -Real.log (77 / 250) ∧
    -Real.log (77 / 250) ≤ (1177655497 / 1000000000) := by
  have h := checkLog_sound (w := (24 / 101)) (n := 12)
    (lo := (96901663 / 200000000)) (hi := (121127079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 77) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 77) = 1/(77 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13434 : Bounds (-1177655497 / 1000000000) (-235531099 / 200000000) (Real.log (77 / 250)) := by
  have h := reflection_log_13434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13435_neg : (8647 / 12500000) ≤ -Real.log (250000 / 250173) ∧
    -Real.log (250000 / 250173) ≤ (691761 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 500173)) (n := 12)
    (lo := (8647 / 12500000)) (hi := (691761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250173 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250173 / 250000) = 1/(250000 / 250173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13435 : Bounds (8647 / 12500000) (691761 / 1000000000) (Real.log (250173 / 250000)) := by
  have h := reflection_log_13435_neg
  have he : Real.log (250173 / 250000) = -Real.log (250000 / 250173) := by
    rw [show ((250173 / 250000) : ℝ) = ((250000 / 250173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13436_neg : (692239 / 1000000000) ≤ -Real.log (249827 / 250000) ∧
    -Real.log (249827 / 250000) ≤ (8653 / 12500000) := by
  have h := checkLog_sound (w := (173 / 499827)) (n := 12)
    (lo := (692239 / 1000000000)) (hi := (8653 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249827) = 1/(249827 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13436 : Bounds (-8653 / 12500000) (-692239 / 1000000000) (Real.log (249827 / 250000)) := by
  have h := reflection_log_13436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13437_neg : (321320889 / 1000000000) ≤ -Real.log (250000 / 344737) ∧
    -Real.log (250000 / 344737) ≤ (32132089 / 100000000) := by
  have h := checkLog_sound (w := (94737 / 594737)) (n := 12)
    (lo := (321320889 / 1000000000)) (hi := (32132089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344737 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344737 / 250000) = 1/(250000 / 344737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13437 : Bounds (321320889 / 1000000000) (32132089 / 100000000) (Real.log (344737 / 250000)) := by
  have h := reflection_log_13437_neg
  have he : Real.log (344737 / 250000) = -Real.log (250000 / 344737) := by
    rw [show ((344737 / 250000) : ℝ) = ((250000 / 344737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13438_neg : (29771279 / 62500000) ≤ -Real.log (155263 / 250000) ∧
    -Real.log (155263 / 250000) ≤ (95268093 / 200000000) := by
  have h := checkLog_sound (w := (94737 / 405263)) (n := 12)
    (lo := (29771279 / 62500000)) (hi := (95268093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 155263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 155263) = 1/(155263 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13438 : Bounds (-95268093 / 200000000) (-29771279 / 62500000) (Real.log (155263 / 250000)) := by
  have h := reflection_log_13438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13439_neg : (25252 / 78125) ≤ -Real.log (1000000 / 1381577) ∧
    -Real.log (1000000 / 1381577) ≤ (323225601 / 1000000000) := by
  have h := checkLog_sound (w := (381577 / 2381577)) (n := 12)
    (lo := (25252 / 78125)) (hi := (323225601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1381577 / 1000000) = 1/(1000000 / 1381577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13439 : Bounds (25252 / 78125) (323225601 / 1000000000) (Real.log (1381577 / 1000000)) := by
  have h := reflection_log_13439_neg
  have he : Real.log (1381577 / 1000000) = -Real.log (1000000 / 1381577) := by
    rw [show ((1381577 / 1000000) : ℝ) = ((1000000 / 1381577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0210 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13440_neg : (480582589 / 1000000000) ≤ -Real.log (618423 / 1000000) ∧
    -Real.log (618423 / 1000000) ≤ (48058259 / 100000000) := by
  have h := checkLog_sound (w := (381577 / 1618423)) (n := 12)
    (lo := (480582589 / 1000000000)) (hi := (48058259 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 618423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 618423) = 1/(618423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13440 : Bounds (-48058259 / 100000000) (-480582589 / 1000000000) (Real.log (618423 / 1000000)) := by
  have h := reflection_log_13440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13441_neg : (157356989 / 1000000000) ≤ -Real.log (854398993071 / 1000000000000) ∧
    -Real.log (854398993071 / 1000000000000) ≤ (15735699 / 100000000) := by
  have h := checkLog_sound (w := (145601006929 / 1854398993071)) (n := 12)
    (lo := (157356989 / 1000000000)) (hi := (15735699 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 854398993071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 854398993071) = 1/(854398993071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13441 : Bounds (-15735699 / 100000000) (-157356989 / 1000000000) (Real.log (854398993071 / 1000000000000)) := by
  have h := reflection_log_13441_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13442_neg : (6200783 / 40000000) ≤ -Real.log (53524900831 / 62500000000) ∧
    -Real.log (53524900831 / 62500000000) ≤ (19377447 / 125000000) := by
  have h := checkLog_sound (w := (8975099169 / 116024900831)) (n := 12)
    (lo := (6200783 / 40000000)) (hi := (19377447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 53524900831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 53524900831) = 1/(53524900831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13442 : Bounds (-19377447 / 125000000) (-6200783 / 40000000) (Real.log (53524900831 / 62500000000)) := by
  have h := reflection_log_13442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13443_neg : (797661353 / 1000000000) ≤ -Real.log (500000000000 / 1110171128987) ∧
    -Real.log (500000000000 / 1110171128987) ≤ (159532271 / 200000000) := by
  have h := checkLog_sound (w := (110171128987 / 2110171128987)) (n := 12)
    (lo := (104514173 / 1000000000)) (hi := (52257087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110171128987 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1110171128987 / 1000000000000) = 1/(500000000000 / 1110171128987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13443 : Bounds (797661353 / 1000000000) (159532271 / 200000000) (Real.log (1110171128987 / 500000000000)) := by
  have h := reflection_log_13443_neg
  have he : Real.log (1110171128987 / 500000000000) = -Real.log (500000000000 / 1110171128987) := by
    rw [show ((1110171128987 / 500000000000) : ℝ) = ((500000000000 / 1110171128987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13444_neg : (803808189 / 1000000000) ≤ -Real.log (100000000000 / 223403236943) ∧
    -Real.log (100000000000 / 223403236943) ≤ (803808191 / 1000000000) := by
  have h := checkLog_sound (w := (23403236943 / 423403236943)) (n := 12)
    (lo := (110661009 / 1000000000)) (hi := (11066101 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223403236943 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(223403236943 / 200000000000) = 1/(100000000000 / 223403236943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13444 : Bounds (803808189 / 1000000000) (803808191 / 1000000000) (Real.log (223403236943 / 100000000000)) := by
  have h := reflection_log_13444_neg
  have he : Real.log (223403236943 / 100000000000) = -Real.log (100000000000 / 223403236943) := by
    rw [show ((223403236943 / 100000000000) : ℝ) = ((100000000000 / 223403236943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13445_neg : (1692099003 / 1000000000) ≤ -Real.log (500000000000 / 2715434083601) ∧
    -Real.log (500000000000 / 2715434083601) ≤ (846049503 / 500000000) := by
  have h := checkLog_sound (w := (715434083601 / 4715434083601)) (n := 12)
    (lo := (305804643 / 1000000000)) (hi := (76451161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2715434083601 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2715434083601 / 2000000000000) = 1/(500000000000 / 2715434083601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13445 : Bounds (1692099003 / 1000000000) (846049503 / 500000000) (Real.log (2715434083601 / 500000000000)) := by
  have h := reflection_log_13445_neg
  have he : Real.log (2715434083601 / 500000000000) = -Real.log (500000000000 / 2715434083601) := by
    rw [show ((2715434083601 / 500000000000) : ℝ) = ((500000000000 / 2715434083601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13446_neg : (425891689 / 250000000) ≤ -Real.log (250000000000 / 1373376623377) ∧
    -Real.log (250000000000 / 1373376623377) ≤ (1703566759 / 1000000000) := by
  have h := checkLog_sound (w := (373376623377 / 2373376623377)) (n := 12)
    (lo := (79318099 / 250000000)) (hi := (317272397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1373376623377 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1373376623377 / 1000000000000) = 1/(250000000000 / 1373376623377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13446 : Bounds (425891689 / 250000000) (1703566759 / 1000000000) (Real.log (1373376623377 / 250000000000)) := by
  have h := reflection_log_13446_neg
  have he : Real.log (1373376623377 / 250000000000) = -Real.log (250000000000 / 1373376623377) := by
    rw [show ((1373376623377 / 250000000000) : ℝ) = ((250000000000 / 1373376623377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13447_neg : (26384137 / 50000000) ≤ -Real.log (200 / 339) ∧
    -Real.log (200 / 339) ≤ (527682741 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 539)) (n := 12)
    (lo := (26384137 / 50000000)) (hi := (527682741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 200) = 1/(200 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13447 : Bounds (26384137 / 50000000) (527682741 / 1000000000) (Real.log (339 / 200)) := by
  have h := reflection_log_13447_neg
  have he : Real.log (339 / 200) = -Real.log (200 / 339) := by
    rw [show ((339 / 200) : ℝ) = ((200 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13448_neg : (1187443501 / 1000000000) ≤ -Real.log (61 / 200) ∧
    -Real.log (61 / 200) ≤ (1187443503 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 61) = 1/(61 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13448 : Bounds (-1187443503 / 1000000000) (-1187443501 / 1000000000) (Real.log (61 / 200)) := by
  have h := reflection_log_13448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13449_neg : (347379 / 500000000) ≤ -Real.log (200000 / 200139) ∧
    -Real.log (200000 / 200139) ≤ (694759 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 400139)) (n := 12)
    (lo := (347379 / 500000000)) (hi := (694759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200139 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200139 / 200000) = 1/(200000 / 200139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13449 : Bounds (347379 / 500000000) (694759 / 1000000000) (Real.log (200139 / 200000)) := by
  have h := reflection_log_13449_neg
  have he : Real.log (200139 / 200000) = -Real.log (200000 / 200139) := by
    rw [show ((200139 / 200000) : ℝ) = ((200000 / 200139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13450_neg : (695241 / 1000000000) ≤ -Real.log (199861 / 200000) ∧
    -Real.log (199861 / 200000) ≤ (347621 / 500000000) := by
  have h := checkLog_sound (w := (139 / 399861)) (n := 12)
    (lo := (695241 / 1000000000)) (hi := (347621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199861) = 1/(199861 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13450 : Bounds (-347621 / 500000000) (-695241 / 1000000000) (Real.log (199861 / 200000)) := by
  have h := reflection_log_13450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13451_neg : (32278253 / 100000000) ≤ -Real.log (200000 / 276193) ∧
    -Real.log (200000 / 276193) ≤ (322782531 / 1000000000) := by
  have h := checkLog_sound (w := (76193 / 476193)) (n := 12)
    (lo := (32278253 / 100000000)) (hi := (322782531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((276193 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(276193 / 200000) = 1/(200000 / 276193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13451 : Bounds (32278253 / 100000000) (322782531 / 1000000000) (Real.log (276193 / 200000)) := by
  have h := reflection_log_13451_neg
  have he : Real.log (276193 / 200000) = -Real.log (200000 / 276193) := by
    rw [show ((276193 / 200000) : ℝ) = ((200000 / 276193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13452_neg : (95918693 / 200000000) ≤ -Real.log (123807 / 200000) ∧
    -Real.log (123807 / 200000) ≤ (239796733 / 500000000) := by
  have h := checkLog_sound (w := (76193 / 323807)) (n := 12)
    (lo := (95918693 / 200000000)) (hi := (239796733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 123807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 123807) = 1/(123807 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13452 : Bounds (-239796733 / 500000000) (-95918693 / 200000000) (Real.log (123807 / 200000)) := by
  have h := reflection_log_13452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13453_neg : (324690243 / 1000000000) ≤ -Real.log (500000 / 691801) ∧
    -Real.log (500000 / 691801) ≤ (81172561 / 250000000) := by
  have h := checkLog_sound (w := (191801 / 1191801)) (n := 12)
    (lo := (324690243 / 1000000000)) (hi := (81172561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691801 / 500000) = 1/(500000 / 691801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13453 : Bounds (324690243 / 1000000000) (81172561 / 250000000) (Real.log (691801 / 500000)) := by
  have h := reflection_log_13453_neg
  have he : Real.log (691801 / 500000) = -Real.log (500000 / 691801) := by
    rw [show ((691801 / 500000) : ℝ) = ((500000 / 691801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13454_neg : (24193121 / 50000000) ≤ -Real.log (308199 / 500000) ∧
    -Real.log (308199 / 500000) ≤ (483862421 / 1000000000) := by
  have h := checkLog_sound (w := (191801 / 808199)) (n := 12)
    (lo := (24193121 / 50000000)) (hi := (483862421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 308199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 308199) = 1/(308199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13454 : Bounds (-483862421 / 1000000000) (-24193121 / 50000000) (Real.log (308199 / 500000)) := by
  have h := reflection_log_13454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13455_neg : (9948261 / 62500000) ≤ -Real.log (213212376399 / 250000000000) ∧
    -Real.log (213212376399 / 250000000000) ≤ (159172177 / 1000000000) := by
  have h := checkLog_sound (w := (36787623601 / 463212376399)) (n := 12)
    (lo := (9948261 / 62500000)) (hi := (159172177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 213212376399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 213212376399) = 1/(213212376399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13455 : Bounds (-159172177 / 1000000000) (-9948261 / 62500000) (Real.log (213212376399 / 250000000000)) := by
  have h := reflection_log_13455_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13456_neg : (78405467 / 500000000) ≤ -Real.log (34194626751 / 40000000000) ∧
    -Real.log (34194626751 / 40000000000) ≤ (31362187 / 200000000) := by
  have h := checkLog_sound (w := (5805373249 / 74194626751)) (n := 12)
    (lo := (78405467 / 500000000)) (hi := (31362187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 34194626751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 34194626751) = 1/(34194626751 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13456 : Bounds (-31362187 / 200000000) (-78405467 / 500000000) (Real.log (34194626751 / 40000000000)) := by
  have h := reflection_log_13456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13457_neg : (401187997 / 500000000) ≤ -Real.log (500000000000 / 1115417545049) ∧
    -Real.log (500000000000 / 1115417545049) ≤ (200593999 / 250000000) := by
  have h := checkLog_sound (w := (115417545049 / 2115417545049)) (n := 12)
    (lo := (54614407 / 500000000)) (hi := (21845763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115417545049 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1115417545049 / 1000000000000) = 1/(500000000000 / 1115417545049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13457 : Bounds (401187997 / 500000000) (200593999 / 250000000) (Real.log (1115417545049 / 500000000000)) := by
  have h := reflection_log_13457_neg
  have he : Real.log (1115417545049 / 500000000000) = -Real.log (500000000000 / 1115417545049) := by
    rw [show ((1115417545049 / 500000000000) : ℝ) = ((500000000000 / 1115417545049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13458_neg : (808552663 / 1000000000) ≤ -Real.log (500000000000 / 1122328430657) ∧
    -Real.log (500000000000 / 1122328430657) ≤ (161710533 / 200000000) := by
  have h := checkLog_sound (w := (122328430657 / 2122328430657)) (n := 12)
    (lo := (115405483 / 1000000000)) (hi := (28851371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122328430657 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1122328430657 / 1000000000000) = 1/(500000000000 / 1122328430657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13458 : Bounds (808552663 / 1000000000) (161710533 / 200000000) (Real.log (1122328430657 / 500000000000)) := by
  have h := reflection_log_13458_neg
  have he : Real.log (1122328430657 / 500000000000) = -Real.log (500000000000 / 1122328430657) := by
    rw [show ((1122328430657 / 500000000000) : ℝ) = ((500000000000 / 1122328430657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13459_neg : (425891689 / 250000000) ≤ -Real.log (500000000000 / 2746753246753) ∧
    -Real.log (500000000000 / 2746753246753) ≤ (1703566759 / 1000000000) := by
  have h := checkLog_sound (w := (746753246753 / 4746753246753)) (n := 12)
    (lo := (79318099 / 250000000)) (hi := (317272397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2746753246753 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2746753246753 / 2000000000000) = 1/(500000000000 / 2746753246753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13459 : Bounds (425891689 / 250000000) (1703566759 / 1000000000) (Real.log (2746753246753 / 500000000000)) := by
  have h := reflection_log_13459_neg
  have he : Real.log (2746753246753 / 500000000000) = -Real.log (500000000000 / 2746753246753) := by
    rw [show ((2746753246753 / 500000000000) : ℝ) = ((500000000000 / 2746753246753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13460_neg : (857563121 / 500000000) ≤ -Real.log (500000000000 / 2778688524591) ∧
    -Real.log (500000000000 / 2778688524591) ≤ (343025249 / 200000000) := by
  have h := checkLog_sound (w := (778688524591 / 4778688524591)) (n := 12)
    (lo := (164415941 / 500000000)) (hi := (328831883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2778688524591 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2778688524591 / 2000000000000) = 1/(500000000000 / 2778688524591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13460 : Bounds (857563121 / 500000000) (343025249 / 200000000) (Real.log (2778688524591 / 500000000000)) := by
  have h := reflection_log_13460_neg
  have he : Real.log (2778688524591 / 500000000000) = -Real.log (500000000000 / 2778688524591) := by
    rw [show ((2778688524591 / 500000000000) : ℝ) = ((500000000000 / 2778688524591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13461_neg : (529451087 / 1000000000) ≤ -Real.log (500 / 849) ∧
    -Real.log (500 / 849) ≤ (33090693 / 62500000) := by
  have h := checkLog_sound (w := (349 / 1349)) (n := 12)
    (lo := (529451087 / 1000000000)) (hi := (33090693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849 / 500) = 1/(500 / 849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13461 : Bounds (529451087 / 1000000000) (33090693 / 62500000) (Real.log (849 / 500)) := by
  have h := reflection_log_13461_neg
  have he : Real.log (849 / 500) = -Real.log (500 / 849) := by
    rw [show ((849 / 500) : ℝ) = ((500 / 849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13462_neg : (1197328261 / 1000000000) ≤ -Real.log (151 / 500) ∧
    -Real.log (151 / 500) ≤ (1197328263 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 401)) (n := 12)
    (lo := (504181081 / 1000000000)) (hi := (252090541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 151) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 151) = 1/(151 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13462 : Bounds (-1197328263 / 1000000000) (-1197328261 / 1000000000) (Real.log (151 / 500)) := by
  have h := reflection_log_13462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13463_neg : (174439 / 250000000) ≤ -Real.log (500000 / 500349) ∧
    -Real.log (500000 / 500349) ≤ (697757 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1000349)) (n := 12)
    (lo := (174439 / 250000000)) (hi := (697757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500349 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500349 / 500000) = 1/(500000 / 500349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13463 : Bounds (174439 / 250000000) (697757 / 1000000000) (Real.log (500349 / 500000)) := by
  have h := reflection_log_13463_neg
  have he : Real.log (500349 / 500000) = -Real.log (500000 / 500349) := by
    rw [show ((500349 / 500000) : ℝ) = ((500000 / 500349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13464_neg : (698243 / 1000000000) ≤ -Real.log (499651 / 500000) ∧
    -Real.log (499651 / 500000) ≤ (174561 / 250000000) := by
  have h := checkLog_sound (w := (349 / 999651)) (n := 12)
    (lo := (698243 / 1000000000)) (hi := (174561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499651) = 1/(499651 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13464 : Bounds (-174561 / 250000000) (-698243 / 1000000000) (Real.log (499651 / 500000)) := by
  have h := reflection_log_13464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13465_neg : (2593971 / 8000000) ≤ -Real.log (250000 / 345747) ∧
    -Real.log (250000 / 345747) ≤ (40530797 / 125000000) := by
  have h := checkLog_sound (w := (95747 / 595747)) (n := 12)
    (lo := (2593971 / 8000000)) (hi := (40530797 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345747 / 250000) = 1/(250000 / 345747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13465 : Bounds (2593971 / 8000000) (40530797 / 125000000) (Real.log (345747 / 250000)) := by
  have h := reflection_log_13465_neg
  have he : Real.log (345747 / 250000) = -Real.log (250000 / 345747) := by
    rw [show ((345747 / 250000) : ℝ) = ((250000 / 345747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13466_neg : (241433403 / 500000000) ≤ -Real.log (154253 / 250000) ∧
    -Real.log (154253 / 250000) ≤ (482866807 / 1000000000) := by
  have h := checkLog_sound (w := (95747 / 404253)) (n := 12)
    (lo := (241433403 / 500000000)) (hi := (482866807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 154253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 154253) = 1/(154253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13466 : Bounds (-482866807 / 1000000000) (-241433403 / 500000000) (Real.log (154253 / 250000)) := by
  have h := reflection_log_13466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13467_neg : (326156353 / 1000000000) ≤ -Real.log (31250 / 43301) ∧
    -Real.log (31250 / 43301) ≤ (163078177 / 500000000) := by
  have h := checkLog_sound (w := (12051 / 74551)) (n := 12)
    (lo := (326156353 / 1000000000)) (hi := (163078177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43301 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43301 / 31250) = 1/(31250 / 43301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13467 : Bounds (326156353 / 1000000000) (163078177 / 500000000) (Real.log (43301 / 31250)) := by
  have h := reflection_log_13467_neg
  have he : Real.log (43301 / 31250) = -Real.log (31250 / 43301) := by
    rw [show ((43301 / 31250) : ℝ) = ((31250 / 43301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13468_neg : (487161181 / 1000000000) ≤ -Real.log (19199 / 31250) ∧
    -Real.log (19199 / 31250) ≤ (243580591 / 500000000) := by
  have h := checkLog_sound (w := (12051 / 50449)) (n := 12)
    (lo := (487161181 / 1000000000)) (hi := (243580591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 19199) = 1/(19199 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13468 : Bounds (-243580591 / 500000000) (-487161181 / 1000000000) (Real.log (19199 / 31250)) := by
  have h := reflection_log_13468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13469_neg : (40251207 / 250000000) ≤ -Real.log (831335899 / 976562500) ∧
    -Real.log (831335899 / 976562500) ≤ (161004829 / 1000000000) := by
  have h := checkLog_sound (w := (145226601 / 1807898399)) (n := 12)
    (lo := (40251207 / 250000000)) (hi := (161004829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 831335899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 831335899) = 1/(831335899 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13469 : Bounds (-161004829 / 1000000000) (-40251207 / 250000000) (Real.log (831335899 / 976562500)) := by
  have h := reflection_log_13469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13470_neg : (15862043 / 100000000) ≤ -Real.log (53332511991 / 62500000000) ∧
    -Real.log (53332511991 / 62500000000) ≤ (158620431 / 1000000000) := by
  have h := checkLog_sound (w := (9167488009 / 115832511991)) (n := 12)
    (lo := (15862043 / 100000000)) (hi := (158620431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 53332511991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 53332511991) = 1/(53332511991 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13470 : Bounds (-158620431 / 1000000000) (-15862043 / 100000000) (Real.log (53332511991 / 62500000000)) := by
  have h := reflection_log_13470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13471_neg : (807113181 / 1000000000) ≤ -Real.log (500000000000 / 1120714021769) ∧
    -Real.log (500000000000 / 1120714021769) ≤ (807113183 / 1000000000) := by
  have h := checkLog_sound (w := (120714021769 / 2120714021769)) (n := 12)
    (lo := (113966001 / 1000000000)) (hi := (56983001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120714021769 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1120714021769 / 1000000000000) = 1/(500000000000 / 1120714021769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13471 : Bounds (807113181 / 1000000000) (807113183 / 1000000000) (Real.log (1120714021769 / 500000000000)) := by
  have h := reflection_log_13471_neg
  have he : Real.log (1120714021769 / 500000000000) = -Real.log (500000000000 / 1120714021769) := by
    rw [show ((1120714021769 / 500000000000) : ℝ) = ((500000000000 / 1120714021769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13472_neg : (406658767 / 500000000) ≤ -Real.log (500000000000 / 1127688942133) ∧
    -Real.log (500000000000 / 1127688942133) ≤ (25416173 / 31250000) := by
  have h := checkLog_sound (w := (127688942133 / 2127688942133)) (n := 12)
    (lo := (60085177 / 500000000)) (hi := (24034071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127688942133 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1127688942133 / 1000000000000) = 1/(500000000000 / 1127688942133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13472 : Bounds (406658767 / 500000000) (25416173 / 31250000) (Real.log (1127688942133 / 500000000000)) := by
  have h := reflection_log_13472_neg
  have he : Real.log (1127688942133 / 500000000000) = -Real.log (500000000000 / 1127688942133) := by
    rw [show ((1127688942133 / 500000000000) : ℝ) = ((500000000000 / 1127688942133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13473_neg : (857563121 / 500000000) ≤ -Real.log (50000000000 / 277868852459) ∧
    -Real.log (50000000000 / 277868852459) ≤ (343025249 / 200000000) := by
  have h := checkLog_sound (w := (77868852459 / 477868852459)) (n := 12)
    (lo := (164415941 / 500000000)) (hi := (328831883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277868852459 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(277868852459 / 200000000000) = 1/(50000000000 / 277868852459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13473 : Bounds (857563121 / 500000000) (343025249 / 200000000) (Real.log (277868852459 / 50000000000)) := by
  have h := reflection_log_13473_neg
  have he : Real.log (277868852459 / 50000000000) = -Real.log (50000000000 / 277868852459) := by
    rw [show ((277868852459 / 50000000000) : ℝ) = ((50000000000 / 277868852459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13474_neg : (431694837 / 250000000) ≤ -Real.log (250000000000 / 1405629139073) ∧
    -Real.log (250000000000 / 1405629139073) ≤ (1726779351 / 1000000000) := by
  have h := checkLog_sound (w := (405629139073 / 2405629139073)) (n := 12)
    (lo := (85121247 / 250000000)) (hi := (340484989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1405629139073 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1405629139073 / 1000000000000) = 1/(250000000000 / 1405629139073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13474 : Bounds (431694837 / 250000000) (1726779351 / 1000000000) (Real.log (1405629139073 / 250000000000)) := by
  have h := reflection_log_13474_neg
  have he : Real.log (1405629139073 / 250000000000) = -Real.log (250000000000 / 1405629139073) := by
    rw [show ((1405629139073 / 250000000000) : ℝ) = ((250000000000 / 1405629139073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13475_neg : (531216313 / 1000000000) ≤ -Real.log (1000 / 1701) ∧
    -Real.log (1000 / 1701) ≤ (265608157 / 500000000) := by
  have h := checkLog_sound (w := (701 / 2701)) (n := 12)
    (lo := (531216313 / 1000000000)) (hi := (265608157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1701 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1701 / 1000) = 1/(1000 / 1701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13475 : Bounds (531216313 / 1000000000) (265608157 / 500000000) (Real.log (1701 / 1000)) := by
  have h := reflection_log_13475_neg
  have he : Real.log (1701 / 1000) = -Real.log (1000 / 1701) := by
    rw [show ((1701 / 1000) : ℝ) = ((1000 / 1701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13476_neg : (241462341 / 200000000) ≤ -Real.log (299 / 1000) ∧
    -Real.log (299 / 1000) ≤ (1207311707 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 799)) (n := 12)
    (lo := (20566581 / 40000000)) (hi := (257082263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 299) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 299) = 1/(299 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13476 : Bounds (-1207311707 / 1000000000) (-241462341 / 200000000) (Real.log (299 / 1000)) := by
  have h := reflection_log_13476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13477_neg : (350377 / 500000000) ≤ -Real.log (1000000 / 1000701) ∧
    -Real.log (1000000 / 1000701) ≤ (140151 / 200000000) := by
  have h := checkLog_sound (w := (701 / 2000701)) (n := 12)
    (lo := (350377 / 500000000)) (hi := (140151 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000701 / 1000000) = 1/(1000000 / 1000701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13477 : Bounds (350377 / 500000000) (140151 / 200000000) (Real.log (1000701 / 1000000)) := by
  have h := reflection_log_13477_neg
  have he : Real.log (1000701 / 1000000) = -Real.log (1000000 / 1000701) := by
    rw [show ((1000701 / 1000000) : ℝ) = ((1000000 / 1000701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13478_neg : (140249 / 200000000) ≤ -Real.log (999299 / 1000000) ∧
    -Real.log (999299 / 1000000) ≤ (350623 / 500000000) := by
  have h := checkLog_sound (w := (701 / 1999299)) (n := 12)
    (lo := (140249 / 200000000)) (hi := (350623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999299) = 1/(999299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13478 : Bounds (-350623 / 500000000) (-140249 / 200000000) (Real.log (999299 / 1000000)) := by
  have h := reflection_log_13478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13479_neg : (325712413 / 1000000000) ≤ -Real.log (1000000 / 1385017) ∧
    -Real.log (1000000 / 1385017) ≤ (162856207 / 500000000) := by
  have h := checkLog_sound (w := (385017 / 2385017)) (n := 12)
    (lo := (325712413 / 1000000000)) (hi := (162856207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385017 / 1000000) = 1/(1000000 / 1385017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13479 : Bounds (325712413 / 1000000000) (162856207 / 500000000) (Real.log (1385017 / 1000000)) := by
  have h := reflection_log_13479_neg
  have he : Real.log (1385017 / 1000000) = -Real.log (1000000 / 1385017) := by
    rw [show ((1385017 / 1000000) : ℝ) = ((1000000 / 1385017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13480_neg : (486160653 / 1000000000) ≤ -Real.log (614983 / 1000000) ∧
    -Real.log (614983 / 1000000) ≤ (243080327 / 500000000) := by
  have h := checkLog_sound (w := (385017 / 1614983)) (n := 12)
    (lo := (486160653 / 1000000000)) (hi := (243080327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 614983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 614983) = 1/(614983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13480 : Bounds (-243080327 / 500000000) (-486160653 / 1000000000) (Real.log (614983 / 1000000)) := by
  have h := reflection_log_13480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13481_neg : (327626081 / 1000000000) ≤ -Real.log (100000 / 138767) ∧
    -Real.log (100000 / 138767) ≤ (163813041 / 500000000) := by
  have h := checkLog_sound (w := (38767 / 238767)) (n := 12)
    (lo := (327626081 / 1000000000)) (hi := (163813041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138767 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138767 / 100000) = 1/(100000 / 138767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13481 : Bounds (327626081 / 1000000000) (163813041 / 500000000) (Real.log (138767 / 100000)) := by
  have h := reflection_log_13481_neg
  have he : Real.log (138767 / 100000) = -Real.log (100000 / 138767) := by
    rw [show ((138767 / 100000) : ℝ) = ((100000 / 138767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13482_neg : (245241963 / 500000000) ≤ -Real.log (61233 / 100000) ∧
    -Real.log (61233 / 100000) ≤ (490483927 / 1000000000) := by
  have h := checkLog_sound (w := (38767 / 161233)) (n := 12)
    (lo := (245241963 / 500000000)) (hi := (490483927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 61233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 61233) = 1/(61233 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13482 : Bounds (-490483927 / 1000000000) (-245241963 / 500000000) (Real.log (61233 / 100000)) := by
  have h := reflection_log_13482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13483_neg : (40714461 / 250000000) ≤ -Real.log (8497119711 / 10000000000) ∧
    -Real.log (8497119711 / 10000000000) ≤ (32571569 / 200000000) := by
  have h := checkLog_sound (w := (1502880289 / 18497119711)) (n := 12)
    (lo := (40714461 / 250000000)) (hi := (32571569 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8497119711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8497119711) = 1/(8497119711 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13483 : Bounds (-32571569 / 200000000) (-40714461 / 250000000) (Real.log (8497119711 / 10000000000)) := by
  have h := reflection_log_13483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13484_neg : (160448239 / 1000000000) ≤ -Real.log (851761909711 / 1000000000000) ∧
    -Real.log (851761909711 / 1000000000000) ≤ (2005603 / 12500000) := by
  have h := checkLog_sound (w := (148238090289 / 1851761909711)) (n := 12)
    (lo := (160448239 / 1000000000)) (hi := (2005603 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 851761909711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 851761909711) = 1/(851761909711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13484 : Bounds (-2005603 / 12500000) (-160448239 / 1000000000) (Real.log (851761909711 / 1000000000000)) := by
  have h := reflection_log_13484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13485_neg : (811873067 / 1000000000) ≤ -Real.log (100000000000 / 225212241639) ∧
    -Real.log (100000000000 / 225212241639) ≤ (811873069 / 1000000000) := by
  have h := checkLog_sound (w := (25212241639 / 425212241639)) (n := 12)
    (lo := (118725887 / 1000000000)) (hi := (463773 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225212241639 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(225212241639 / 200000000000) = 1/(100000000000 / 225212241639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13485 : Bounds (811873067 / 1000000000) (811873069 / 1000000000) (Real.log (225212241639 / 100000000000)) := by
  have h := reflection_log_13485_neg
  have he : Real.log (225212241639 / 100000000000) = -Real.log (100000000000 / 225212241639) := by
    rw [show ((225212241639 / 100000000000) : ℝ) = ((100000000000 / 225212241639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13486_neg : (818110007 / 1000000000) ≤ -Real.log (250000000000 / 566553165777) ∧
    -Real.log (250000000000 / 566553165777) ≤ (818110009 / 1000000000) := by
  have h := checkLog_sound (w := (66553165777 / 1066553165777)) (n := 12)
    (lo := (124962827 / 1000000000)) (hi := (31240707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566553165777 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(566553165777 / 500000000000) = 1/(250000000000 / 566553165777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13486 : Bounds (818110007 / 1000000000) (818110009 / 1000000000) (Real.log (566553165777 / 250000000000)) := by
  have h := reflection_log_13486_neg
  have he : Real.log (566553165777 / 250000000000) = -Real.log (250000000000 / 566553165777) := by
    rw [show ((566553165777 / 250000000000) : ℝ) = ((250000000000 / 566553165777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13487_neg : (431694837 / 250000000) ≤ -Real.log (100000000000 / 562251655629) ∧
    -Real.log (100000000000 / 562251655629) ≤ (1726779351 / 1000000000) := by
  have h := checkLog_sound (w := (162251655629 / 962251655629)) (n := 12)
    (lo := (85121247 / 250000000)) (hi := (340484989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((562251655629 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(562251655629 / 400000000000) = 1/(100000000000 / 562251655629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13487 : Bounds (431694837 / 250000000) (1726779351 / 1000000000) (Real.log (562251655629 / 100000000000)) := by
  have h := reflection_log_13487_neg
  have he : Real.log (562251655629 / 100000000000) = -Real.log (100000000000 / 562251655629) := by
    rw [show ((562251655629 / 100000000000) : ℝ) = ((100000000000 / 562251655629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13488_neg : (1738528017 / 1000000000) ≤ -Real.log (62500000000 / 355560200669) ∧
    -Real.log (62500000000 / 355560200669) ≤ (86926401 / 50000000) := by
  have h := checkLog_sound (w := (105560200669 / 605560200669)) (n := 12)
    (lo := (352233657 / 1000000000)) (hi := (176116829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355560200669 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(355560200669 / 250000000000) = 1/(62500000000 / 355560200669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13488 : Bounds (1738528017 / 1000000000) (86926401 / 50000000) (Real.log (355560200669 / 62500000000)) := by
  have h := reflection_log_13488_neg
  have he : Real.log (355560200669 / 62500000000) = -Real.log (62500000000 / 355560200669) := by
    rw [show ((355560200669 / 62500000000) : ℝ) = ((62500000000 / 355560200669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13489_neg : (133244607 / 250000000) ≤ -Real.log (125 / 213) ∧
    -Real.log (125 / 213) ≤ (532978429 / 1000000000) := by
  have h := checkLog_sound (w := (44 / 169)) (n := 12)
    (lo := (133244607 / 250000000)) (hi := (532978429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213 / 125) = 1/(125 / 213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13489 : Bounds (133244607 / 250000000) (532978429 / 1000000000) (Real.log (213 / 125)) := by
  have h := reflection_log_13489_neg
  have he : Real.log (213 / 125) = -Real.log (125 / 213) := by
    rw [show ((213 / 125) : ℝ) = ((125 / 213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13490_neg : (76087239 / 62500000) ≤ -Real.log (37 / 125) ∧
    -Real.log (37 / 125) ≤ (608697913 / 500000000) := by
  have h := checkLog_sound (w := (51 / 199)) (n := 12)
    (lo := (131062161 / 250000000)) (hi := (104849729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 74) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 74) = 1/(37 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13490 : Bounds (-608697913 / 500000000) (-76087239 / 62500000) (Real.log (37 / 125)) := by
  have h := reflection_log_13490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13491_neg : (87969 / 125000000) ≤ -Real.log (15625 / 15636) ∧
    -Real.log (15625 / 15636) ≤ (703753 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 31261)) (n := 12)
    (lo := (87969 / 125000000)) (hi := (703753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15636 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15636 / 15625) = 1/(15625 / 15636) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13491 : Bounds (87969 / 125000000) (703753 / 1000000000) (Real.log (15636 / 15625)) := by
  have h := reflection_log_13491_neg
  have he : Real.log (15636 / 15625) = -Real.log (15625 / 15636) := by
    rw [show ((15636 / 15625) : ℝ) = ((15625 / 15636) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13492_neg : (704247 / 1000000000) ≤ -Real.log (15614 / 15625) ∧
    -Real.log (15614 / 15625) ≤ (88031 / 125000000) := by
  have h := checkLog_sound (w := (11 / 31239)) (n := 12)
    (lo := (704247 / 1000000000)) (hi := (88031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15614) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15614) = 1/(15614 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13492 : Bounds (-88031 / 125000000) (-704247 / 1000000000) (Real.log (15614 / 15625)) := by
  have h := reflection_log_13492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13493_neg : (327180631 / 1000000000) ≤ -Real.log (250000 / 346763) ∧
    -Real.log (250000 / 346763) ≤ (40897579 / 125000000) := by
  have h := checkLog_sound (w := (96763 / 596763)) (n := 12)
    (lo := (327180631 / 1000000000)) (hi := (40897579 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346763 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346763 / 250000) = 1/(250000 / 346763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13493 : Bounds (327180631 / 1000000000) (40897579 / 125000000) (Real.log (346763 / 250000)) := by
  have h := reflection_log_13493_neg
  have he : Real.log (346763 / 250000) = -Real.log (250000 / 346763) := by
    rw [show ((346763 / 250000) : ℝ) = ((250000 / 346763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13494_neg : (19579007 / 40000000) ≤ -Real.log (153237 / 250000) ∧
    -Real.log (153237 / 250000) ≤ (61184397 / 125000000) := by
  have h := checkLog_sound (w := (96763 / 403237)) (n := 12)
    (lo := (19579007 / 40000000)) (hi := (61184397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 153237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 153237) = 1/(153237 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13494 : Bounds (-61184397 / 125000000) (-19579007 / 40000000) (Real.log (153237 / 250000)) := by
  have h := reflection_log_13494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13495_neg : (329097251 / 1000000000) ≤ -Real.log (1000000 / 1389713) ∧
    -Real.log (1000000 / 1389713) ≤ (82274313 / 250000000) := by
  have h := checkLog_sound (w := (389713 / 2389713)) (n := 12)
    (lo := (329097251 / 1000000000)) (hi := (82274313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1389713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1389713 / 1000000) = 1/(1000000 / 1389713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13495 : Bounds (329097251 / 1000000000) (82274313 / 250000000) (Real.log (1389713 / 1000000)) := by
  have h := reflection_log_13495_neg
  have he : Real.log (1389713 / 1000000) = -Real.log (1000000 / 1389713) := by
    rw [show ((1389713 / 1000000) : ℝ) = ((1000000 / 1389713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13496_neg : (24691297 / 50000000) ≤ -Real.log (610287 / 1000000) ∧
    -Real.log (610287 / 1000000) ≤ (493825941 / 1000000000) := by
  have h := checkLog_sound (w := (389713 / 1610287)) (n := 12)
    (lo := (24691297 / 50000000)) (hi := (493825941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 610287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 610287) = 1/(610287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13496 : Bounds (-493825941 / 1000000000) (-24691297 / 50000000) (Real.log (610287 / 1000000)) := by
  have h := reflection_log_13496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13497_neg : (164728689 / 1000000000) ≤ -Real.log (848123777631 / 1000000000000) ∧
    -Real.log (848123777631 / 1000000000000) ≤ (16472869 / 100000000) := by
  have h := checkLog_sound (w := (151876222369 / 1848123777631)) (n := 12)
    (lo := (164728689 / 1000000000)) (hi := (16472869 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 848123777631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 848123777631) = 1/(848123777631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13497 : Bounds (-16472869 / 100000000) (-164728689 / 1000000000) (Real.log (848123777631 / 1000000000000)) := by
  have h := reflection_log_13497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13498_neg : (162294543 / 1000000000) ≤ -Real.log (53136921831 / 62500000000) ∧
    -Real.log (53136921831 / 62500000000) ≤ (10143409 / 62500000) := by
  have h := checkLog_sound (w := (9363078169 / 115636921831)) (n := 12)
    (lo := (162294543 / 1000000000)) (hi := (10143409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 53136921831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 53136921831) = 1/(53136921831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13498 : Bounds (-10143409 / 62500000) (-162294543 / 1000000000) (Real.log (53136921831 / 62500000000)) := by
  have h := reflection_log_13498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13499_neg : (408327903 / 500000000) ≤ -Real.log (500000000000 / 1131459764939) ∧
    -Real.log (500000000000 / 1131459764939) ≤ (12760247 / 15625000) := by
  have h := checkLog_sound (w := (131459764939 / 2131459764939)) (n := 12)
    (lo := (61754313 / 500000000)) (hi := (123508627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131459764939 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1131459764939 / 1000000000000) = 1/(500000000000 / 1131459764939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13499 : Bounds (408327903 / 500000000) (12760247 / 15625000) (Real.log (1131459764939 / 500000000000)) := by
  have h := reflection_log_13499_neg
  have he : Real.log (1131459764939 / 500000000000) = -Real.log (500000000000 / 1131459764939) := by
    rw [show ((1131459764939 / 500000000000) : ℝ) = ((500000000000 / 1131459764939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13500_neg : (822923191 / 1000000000) ≤ -Real.log (3906250000 / 8895104117) ∧
    -Real.log (3906250000 / 8895104117) ≤ (822923193 / 1000000000) := by
  have h := checkLog_sound (w := (1082604117 / 16707604117)) (n := 12)
    (lo := (129776011 / 1000000000)) (hi := (32444003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8895104117 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8895104117 / 7812500000) = 1/(3906250000 / 8895104117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13500 : Bounds (822923191 / 1000000000) (822923193 / 1000000000) (Real.log (8895104117 / 3906250000)) := by
  have h := reflection_log_13500_neg
  have he : Real.log (8895104117 / 3906250000) = -Real.log (3906250000 / 8895104117) := by
    rw [show ((8895104117 / 3906250000) : ℝ) = ((3906250000 / 8895104117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13501_neg : (1738528017 / 1000000000) ≤ -Real.log (500000000000 / 2844481605351) ∧
    -Real.log (500000000000 / 2844481605351) ≤ (86926401 / 50000000) := by
  have h := checkLog_sound (w := (844481605351 / 4844481605351)) (n := 12)
    (lo := (352233657 / 1000000000)) (hi := (176116829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2844481605351 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2844481605351 / 2000000000000) = 1/(500000000000 / 2844481605351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13501 : Bounds (1738528017 / 1000000000) (86926401 / 50000000) (Real.log (2844481605351 / 500000000000)) := by
  have h := reflection_log_13501_neg
  have he : Real.log (2844481605351 / 500000000000) = -Real.log (500000000000 / 2844481605351) := by
    rw [show ((2844481605351 / 500000000000) : ℝ) = ((500000000000 / 2844481605351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13502_neg : (1750374251 / 1000000000) ≤ -Real.log (500000000000 / 2878378378379) ∧
    -Real.log (500000000000 / 2878378378379) ≤ (875187127 / 500000000) := by
  have h := checkLog_sound (w := (878378378379 / 4878378378379)) (n := 12)
    (lo := (364079891 / 1000000000)) (hi := (91019973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2878378378379 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2878378378379 / 2000000000000) = 1/(500000000000 / 2878378378379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13502 : Bounds (1750374251 / 1000000000) (875187127 / 500000000) (Real.log (2878378378379 / 500000000000)) := by
  have h := reflection_log_13502_neg
  have he : Real.log (2878378378379 / 500000000000) = -Real.log (500000000000 / 2878378378379) := by
    rw [show ((2878378378379 / 500000000000) : ℝ) = ((500000000000 / 2878378378379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13503_neg : (534737443 / 1000000000) ≤ -Real.log (1000 / 1707) ∧
    -Real.log (1000 / 1707) ≤ (133684361 / 250000000) := by
  have h := checkLog_sound (w := (707 / 2707)) (n := 12)
    (lo := (534737443 / 1000000000)) (hi := (133684361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1707 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1707 / 1000) = 1/(1000 / 1707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13503 : Bounds (534737443 / 1000000000) (133684361 / 250000000) (Real.log (1707 / 1000)) := by
  have h := reflection_log_13503_neg
  have he : Real.log (1707 / 1000) = -Real.log (1000 / 1707) := by
    rw [show ((1707 / 1000) : ℝ) = ((1000 / 1707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


