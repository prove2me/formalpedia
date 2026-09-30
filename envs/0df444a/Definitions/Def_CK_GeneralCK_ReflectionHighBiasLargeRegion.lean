-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionHighBiasLargeRegion
-- name    : CK_GeneralCK_ReflectionHighBiasLargeRegion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T11:58:20.185659+00:00
-- url     : https://prove2.me/theorems/849947a9-eca7-40c7-be76-a5b14a2ad897
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionHighBiasLargeRegion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionHighBiasLargeRegion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionHighBiasLargeRegion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionHighBiasLargeRegion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionHighBiasLargeRegion.lean)

import Definitions.Def_CK_GeneralCK_ReflectionHighBiasCases_v2
import Definitions.Def_CK_GeneralCK_ReflectionHighBiasEntropy
import Definitions.Def_CK_GeneralCK_ReflectionHighBiasLargeAlgebra
import Definitions.Def_CK_GeneralCK_ReflectionHighBiasRational
import Definitions.Def_CK_GeneralCK_ReflectionHighBiasRegion

-- ===== source module GeneralCK.ReflectionHighBiasLargeRegion =====
section

namespace GeneralCK.Reflection
open Certificates.Reflection

theorem curvature_high_bias_large_partner {a b : ℝ}
    (ha : (999/1000:ℝ)≤a) (ha1 : a<1) (hb : (1/2:ℝ)≤b) (hba : b<a) :
    0<curvature a b := by
  let c := HighBiasLarge.plusContact a b
  have ha0 : 0<a := by linarith
  have hb0 : 0<b := by linarith
  have hcmem := HighBiasLarge.plus_contact_mem hb0 hba.le ha1
  have hbc : b≤c := hcmem.1
  have hca : c≤a := hcmem.2
  have hc : (1/2:ℝ)≤c := hb.trans hbc
  have hc0 : 0<c := hb0.trans_le hbc
  have hc1 : c<1 := hca.trans_lt ha1
  have he : 0<(biasE a+biasE b)/2 := by
    have hEa := biasE_pos_wide (by linarith : -1<a) ha1
    have hEb := biasE_pos_wide (by linarith : -1<b) (hba.trans ha1)
    positivity
  have heq := HighBiasLarge.plus_contact_equation hb0 hba.le ha1
  have hV1 := HighBiasLarge.V1_upper ha0 ha1 hb0 hc0 hca he heq
  have hV2 := HighBiasLarge.V2_upper ha0 ha1 hb0 hc0 hc1
  have hV : HighBiasLarge.V1 a b c ((biasE a+biasE b)/2)+HighBiasLarge.V2 a b c≤
      HighBiasCases.tailUpper a b c := by
    simpa only [HighBiasCases.tailUpper,HighBiasCases.Qtail,HighBiasLarge.Qtail,
      show 2-(1-a)=1+a by ring,show 2-(1-c)=1+c by ring] using add_le_add hV1 hV2
  have hq0 := HighBiasCases.Qtail_nonneg hc0.le hca ha1
  have hu0 : 0≤(1-a)/(1-c) := div_nonneg (by linarith) (by linarith)
  have htail : HighBiasCases.tailUpper a b c<1/2 := by
    rcases le_or_gt (Real.sqrt (1-a)) (1-c) with hcase | hcase
    · have hq1 := HighBiasCases.Qtail_le_half_of_sqrt ha ha1 hc hca hcase
      have hu1 := HighBiasCases.ratio_le_small_of_sqrt ha ha1 hca hcase
      have hB := Certificates.Mixed.log_two_gt_69.le.trans
        (HighBiasCases.biasB_ge_log_two hc0.le hc1)
      exact HighBiasRational.case1_bound ha hb hc hB hq0 hq1 hu0 hu1
    · have hsep := HighBiasEntropy.large_partner_separation ha ha1 hb hba.le hcase
      change 1-b<4*(1-c) at hsep
      have hs2 := Real.sq_sqrt (show 0≤1-a by linarith)
      have hs0 := Real.sqrt_nonneg (1-a)
      have hsu : Real.sqrt (1-a)≤(4/125:ℝ) := by nlinarith
      have ht : 1-c≤4/125 := hcase.le.trans hsu
      have hb' : (109/125:ℝ)≤b := by linarith
      have hc' : (121/125:ℝ)≤c := by linarith
      have hB := HighBiasCases.biasB_large_lower hc0.le hc1 (by linarith : 1-c≤1/16)
      have hq1 := HighBiasCases.Qtail_le_one hc hca ha1
      have hu1 : (1-a)/(1-c)≤1 := (div_le_one (by linarith)).mpr (by linarith)
      exact HighBiasRational.case2_bound ha hb' hc' hB hq0 hq1 hu0 hu1
  exact HighBiasLarge.curvature_pos_of_V_lt hb0 hba ha1 (hV.trans_lt htail)

/-- Reflection curvature is positive throughout the entire high-bias tail. -/
theorem curvature_high_bias {a b : ℝ}
    (ha : (999/1000:ℝ)≤a) (ha1 : a<1) (hb : 0<b) (hba : b<a) :
    0<curvature a b := by
  rcases le_or_gt b (1/2:ℝ) with hb' | hb'
  · exact curvature_high_bias_small_partner ha ha1 hb hb'
  · exact curvature_high_bias_large_partner ha ha1 hb'.le hba

end GeneralCK.Reflection

end


