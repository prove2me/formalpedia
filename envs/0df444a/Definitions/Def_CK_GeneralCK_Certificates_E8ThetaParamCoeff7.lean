-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ThetaParamCoeff7
-- name    : CK_GeneralCK_Certificates_E8ThetaParamCoeff7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:50:01.359969+00:00
-- url     : https://prove2.me/theorems/6cc44bae-93ef-4e3f-8eb3-8bae6114a476
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ThetaParamCoeff7` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ThetaParamCoeff7` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ThetaParamCoeff7` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ThetaParamCoeff7 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ThetaParamCoeff7.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff7
import Definitions.Def_CK_GeneralCK_Certificates_E8HigherFormulaIdentities

-- ===== source module GeneralCK.Certificates.E8ThetaParamCoeff7 =====
section

namespace GeneralCK.Certificates.E8ThetaParamCoeff7

open Filter
open E8AnalyticGerm Reflection.ComplexEntropy Reflection.ComplexContactFactor
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8NormalizedCoeff7
open E8ElementaryCoeff5 E8ElementaryCoeff7 E8ParamCoeff5 E8ParamCoeff7
open E8ThetaParamCoeff5 E8ComposeCoeff7 E8HigherFormulaIdentities
open E8HigherRationalTrace E8HigherSourceBoxBridge E8AnalyticCoefficientBoxes

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

theorem analyticAt_thetaDenom : AnalyticAt ℂ thetaDenom 0 := by
  exact (analyticAt_const.sub (analyticAt_id.pow 2)).mul analyticAt_biasBExt

theorem thetaDenom_zero : thetaDenom 0 = (Real.log 2 : ℂ) := by
  simp [thetaDenom]

theorem analyticAt_thetaRatio : AnalyticAt ℂ thetaRatio 0 := by
  exact (analyticAt_id.mul
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num))).div
    analyticAt_thetaDenom (by simpa [thetaDenom_zero] using logTwo_ne)

theorem eventually_ratio_mul_denom :
    (fun z => thetaRatio z * thetaDenom z) =ᶠ[nhds (0 : ℂ)]
      (fun z => z * entropyExt z) := by
  have hd := analyticAt_thetaDenom.continuousAt.eventually_ne
    (by simpa [thetaDenom_zero] using logTwo_ne)
  filter_upwards [hd] with z hz
  simp [thetaRatio, hz]

theorem coeff_one_sub_sq (n : ℕ) :
    coeff (fun z : ℂ => 1 - z ^ 2) n =
      if n = 0 then 1 else if n = 2 then -1 else 0 := by
  rcases n with (_ | _ | _ | n) <;>
    simp [coeff, iteratedDeriv_succ', iteratedDeriv_const, iteratedDeriv_fun_pow_zero]

theorem coeff_denom_zero : coeff thetaDenom 0 = (Real.log 2 : ℂ) := by
  simp [coeff, thetaDenom_zero]

theorem coeff_denom_two : coeff thetaDenom 2 = 1 / 2 - (Real.log 2 : ℂ) := by
  have h := coeff_mul_two (fun z : ℂ => 1 - z ^ 2) biasBExt
    (analyticAt_const.sub (analyticAt_id.pow 2)) analyticAt_biasBExt
  change coeff thetaDenom 2 = _ at h
  rw [h]
  simp_rw [coeff_one_sub_sq]
  have hb1 : coeff biasBExt 1 = 0 := coeff_even_zero_of_odd biasBExt_neg (by decide)
  rw [coeff_biasBExt_two, coeff_zero, biasBExt_zero, hb1]
  norm_num
  ring

theorem coeff_denom_four : coeff thetaDenom 4 = -1 / 4 := by
  have h := coeff_mul_four (fun z : ℂ => 1 - z ^ 2) biasBExt
    (analyticAt_const.sub (analyticAt_id.pow 2)) analyticAt_biasBExt
  change coeff thetaDenom 4 = _ at h
  rw [h]
  simp_rw [coeff_one_sub_sq]
  have hb1 : coeff biasBExt 1 = 0 := coeff_even_zero_of_odd biasBExt_neg (by decide)
  have hb3 : coeff biasBExt 3 = 0 := coeff_even_zero_of_odd biasBExt_neg (by decide)
  rw [coeff_biasBExt_two, coeff_biasBExt_four, hb1, hb3, coeff_zero, biasBExt_zero]
  norm_num

theorem coeff_denom_six : coeff thetaDenom 6 = -1 / 12 := by
  have h := coeff_mul_six (fun z : ℂ => 1 - z ^ 2) biasBExt
    (analyticAt_const.sub (analyticAt_id.pow 2)) analyticAt_biasBExt
  change coeff thetaDenom 6 = _ at h
  rw [h]
  simp_rw [coeff_one_sub_sq]
  have hb1 : coeff biasBExt 1 = 0 := coeff_even_zero_of_odd biasBExt_neg (by decide)
  have hb3 : coeff biasBExt 3 = 0 := coeff_even_zero_of_odd biasBExt_neg (by decide)
  have hb5 : coeff biasBExt 5 = 0 := coeff_even_zero_of_odd biasBExt_neg (by decide)
  rw [coeff_biasBExt_four, coeff_biasBExt_six, hb1, hb3, hb5]
  norm_num

theorem coeff_denom_odd (n : ℕ) (hn : Odd n) : coeff thetaDenom n = 0 := by
  apply coeff_even_zero_of_odd (f := thetaDenom) _ hn
  intro z
  simp [thetaDenom, biasBExt_neg]

private theorem coeff_num_seven : coeff (fun z : ℂ => z * entropyExt z) 7 = -1 / 30 := by
  have h := coeff_mul_seven id entropyExt analyticAt_id
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num))
  change coeff (fun z : ℂ => z * entropyExt z) 7 = _ at h
  rw [h, coeff_entropyExt_six]
  simp [coeff, iteratedDeriv_id]

theorem coeff_thetaRatio_seven : coeff thetaRatio 7 =
    1 - 23 / (15 * (Real.log 2 : ℂ)) + 11 / (12 * (Real.log 2 : ℂ)^2) -
      1 / (4 * (Real.log 2 : ℂ)^3) := by
  have hp := coeff_mul_seven thetaRatio thetaDenom analyticAt_thetaRatio analyticAt_thetaDenom
  have he := coeff_congr eventually_ratio_mul_denom 7
  change coeff (fun z => thetaRatio z * thetaDenom z) 7 = _ at hp
  have hr0 : coeff thetaRatio 0 = 0 := by simp [coeff, thetaRatio]
  rw [hp, coeff_denom_zero, coeff_denom_two, coeff_denom_four, coeff_denom_six,
    coeff_denom_odd 1 (by decide), coeff_denom_odd 3 (by decide),
    coeff_denom_odd 5 (by decide), coeff_denom_odd 7 (by decide),
    coeff_thetaRatio_one, coeff_thetaRatio_three, coeff_thetaRatio_five,
    coeff_num_seven, hr0] at he
  ring_nf at he ⊢
  apply mul_left_cancel₀ logTwo_ne
  have hi : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ logTwo_ne
  have h2 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ ^ 2 =
      (Real.log 2 : ℂ)⁻¹ := by field_simp [logTwo_ne]
  have h3 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ ^ 3 =
      (Real.log 2 : ℂ)⁻¹ ^ 2 := by field_simp [logTwo_ne]
  ring_nf
  linear_combination he + (1 / 5) * hi - (5 / 12) * h2 + (1 / 4) * h3

private theorem thetaParam_eq : thetaParam = fun z : ℂ =>
    (2 / (Real.log 2 : ℂ)) * (atanhExt z + thetaRatio z) := by
  funext z
  rfl

theorem coeff_thetaParam_seven : coeff thetaParam 7 =
    16 / (7 * (Real.log 2 : ℂ)) - 46 / (15 * (Real.log 2 : ℂ)^2) +
      11 / (6 * (Real.log 2 : ℂ)^3) - 1 / (2 * (Real.log 2 : ℂ)^4) := by
  rw [thetaParam_eq, coeff_const_mul]
  have hs := coeff_add atanhExt thetaRatio analyticAt_atanhExt analyticAt_thetaRatio 7
  change coeff (fun z => atanhExt z + thetaRatio z) 7 = _ at hs
  rw [hs, coeff_atanhExt_seven, coeff_thetaRatio_seven]
  ring_nf

theorem thetaTaylorCoeff_seven : thetaTaylorCoeff 7 =
    256 * (120*(Real.log 2 : ℂ)^3 - 518*(Real.log 2 : ℂ)^2 +
      840*(Real.log 2 : ℂ) - 525) / (105*(Real.log 2 : ℂ)^4) := by
  change coeff thetaGerm 7 = _
  have hc := coeff_comp thetaParam xBiasGerm analyticAt_thetaParam analyticAt_xBiasGerm
    xBiasGerm_zero 7
  change coeff thetaGerm 7 = _ at hc
  rw [hc, composeCoeff_seven_odd (coeff thetaParam) (coeff xBiasGerm)
    (by simp [coeff, xBiasGerm_zero]) coeff_xBiasGerm_two coeff_xBiasGerm_four
    coeff_xBiasGerm_six, coeff_thetaParam_one, coeff_thetaParam_three,
    coeff_thetaParam_five, coeff_thetaParam_seven, coeff_xBiasGerm_one,
    coeff_xBiasGerm_three, coeff_xBiasGerm_five, coeff_xBiasGerm_seven]
  field_simp [logTwo_ne]
  ring

theorem qTaylorCoeff_seven_formula :
    qTaylorCoeff 7 = (q7Formula (Real.log 2) : ℂ) :=
  qTaylorCoeff_seven_formula_of_theta thetaTaylorCoeff_seven

theorem inverseStep_seven_formula :
    inverseStep thetaTaylorCoeff qTaylorCoeff 7 = (q7Formula (Real.log 2) : ℂ) := by
  rw [← qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 7)]
  exact qTaylorCoeff_seven_formula

theorem qTaylorCoeff_seven_in_sourceBox :
    ‖qTaylorCoeff 7 - (sourceCenter 7 : ℂ)‖ ≤ (sourceHalfWidth 7 : ℝ) := by
  rw [qTaylorCoeff_seven_formula]
  exact norm_sub_sourceCenter_le_of_real_endpoint_bounds rfl
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).1.1
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).1.2

end GeneralCK.Certificates.E8ThetaParamCoeff7

end


