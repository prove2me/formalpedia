-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ThetaParamCoeff5
-- name    : CK_GeneralCK_Certificates_E8ThetaParamCoeff5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:30:53.237667+00:00
-- url     : https://prove2.me/theorems/3343dec3-6a2d-4f68-b045-853b9c65989e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ThetaParamCoeff5` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ThetaParamCoeff5` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ThetaParamCoeff5` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ThetaParamCoeff5 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ThetaParamCoeff5.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff5

-- ===== source module GeneralCK.Certificates.E8ThetaParamCoeff5 =====
section

namespace GeneralCK.Certificates.E8ThetaParamCoeff5

open Filter
open E8AnalyticGerm Reflection.ComplexEntropy Reflection.ComplexContactFactor
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8ElementaryCoeff5 E8ParamCoeff5

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
private theorem clogTwo_eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.natCast_log (n := 2)).symm

noncomputable def thetaDenom (z : ℂ) : ℂ := (1 - z ^ 2) * biasBExt z
noncomputable def thetaRatio (z : ℂ) : ℂ := z * entropyExt z / thetaDenom z

private theorem analyticAt_thetaDenom : AnalyticAt ℂ thetaDenom 0 := by
  exact (analyticAt_const.sub (analyticAt_id.pow 2)).mul analyticAt_biasBExt

private theorem thetaDenom_zero : thetaDenom 0 = (Real.log 2 : ℂ) := by
  simp [thetaDenom]

private theorem analyticAt_thetaRatio : AnalyticAt ℂ thetaRatio 0 := by
  exact (analyticAt_id.mul
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num))).div
    analyticAt_thetaDenom (by simpa [thetaDenom_zero] using logTwo_ne)

private theorem eventually_ratio_mul_denom :
    (fun z => thetaRatio z * thetaDenom z) =ᶠ[nhds (0 : ℂ)]
      (fun z => z * entropyExt z) := by
  have hd := analyticAt_thetaDenom.continuousAt.eventually_ne
    (by simpa [thetaDenom_zero] using logTwo_ne)
  filter_upwards [hd] with z hz
  simp [thetaRatio, hz]

private theorem coeff_one_sub_sq (n : ℕ) :
    coeff (fun z : ℂ => 1 - z ^ 2) n =
      if n = 0 then 1 else if n = 2 then -1 else 0 := by
  rcases n with (_ | _ | _ | n) <;>
    simp [coeff, iteratedDeriv_succ', iteratedDeriv_const, iteratedDeriv_fun_pow_zero]

private theorem coeff_denom_zero : coeff thetaDenom 0 = (Real.log 2 : ℂ) := by
  simp [coeff, thetaDenom_zero]

private theorem coeff_denom_two : coeff thetaDenom 2 = 1 / 2 - (Real.log 2 : ℂ) := by
  have h := coeff_mul_two (fun z : ℂ => 1 - z ^ 2) biasBExt
    (analyticAt_const.sub (analyticAt_id.pow 2)) analyticAt_biasBExt
  change coeff thetaDenom 2 = _ at h
  rw [h]
  simp_rw [coeff_one_sub_sq]
  have hb1 : coeff biasBExt 1 = 0 := coeff_even_zero_of_odd biasBExt_neg (by decide)
  rw [coeff_biasBExt_two, coeff_zero, biasBExt_zero, hb1]
  norm_num
  ring

private theorem coeff_denom_four : coeff thetaDenom 4 = -1 / 4 := by
  have h := coeff_mul_four (fun z : ℂ => 1 - z ^ 2) biasBExt
    (analyticAt_const.sub (analyticAt_id.pow 2)) analyticAt_biasBExt
  change coeff thetaDenom 4 = _ at h
  rw [h]
  simp_rw [coeff_one_sub_sq]
  have hb1 : coeff biasBExt 1 = 0 := coeff_even_zero_of_odd biasBExt_neg (by decide)
  have hb3 : coeff biasBExt 3 = 0 := coeff_even_zero_of_odd biasBExt_neg (by decide)
  rw [coeff_biasBExt_two, coeff_biasBExt_four, hb1, hb3]
  rw [coeff_zero, biasBExt_zero]
  norm_num

private theorem coeff_denom_odd (n : ℕ) (hn : Odd n) : coeff thetaDenom n = 0 := by
  apply coeff_even_zero_of_odd (f := thetaDenom) _ hn
  intro z
  simp [thetaDenom, biasBExt_neg]

private theorem coeff_num_one : coeff (fun z : ℂ => z * entropyExt z) 1 =
    (Real.log 2 : ℂ) := by
  have h := coeff_mul_one id entropyExt analyticAt_id
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num))
  change coeff (fun z : ℂ => z * entropyExt z) 1 = _ at h
  rw [h, coeff_entropyExt_zero]
  simp [coeff, iteratedDeriv_id]

private theorem coeff_num_three : coeff (fun z : ℂ => z * entropyExt z) 3 = -1 / 2 := by
  have h := coeff_mul_three id entropyExt analyticAt_id
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num))
  change coeff (fun z : ℂ => z * entropyExt z) 3 = _ at h
  rw [h, coeff_entropyExt_two]
  simp [coeff, iteratedDeriv_id]

private theorem coeff_num_five : coeff (fun z : ℂ => z * entropyExt z) 5 = -1 / 12 := by
  have h := coeff_mul_five id entropyExt analyticAt_id
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num))
  change coeff (fun z : ℂ => z * entropyExt z) 5 = _ at h
  rw [h, coeff_entropyExt_four]
  simp [coeff, iteratedDeriv_id]

theorem coeff_thetaRatio_one : coeff thetaRatio 1 = 1 := by
  have hp := coeff_mul_one thetaRatio thetaDenom analyticAt_thetaRatio analyticAt_thetaDenom
  have he := coeff_congr eventually_ratio_mul_denom 1
  change coeff (fun z => thetaRatio z * thetaDenom z) 1 = _ at hp
  have hr0 : coeff thetaRatio 0 = 0 := by simp [coeff, thetaRatio]
  rw [hp, coeff_denom_zero, coeff_denom_odd 1 (by decide), coeff_num_one,
    hr0] at he
  apply (mul_right_cancel₀ logTwo_ne)
  simpa [mul_comm] using he

theorem coeff_thetaRatio_three : coeff thetaRatio 3 =
    1 - 1 / (Real.log 2 : ℂ) := by
  have hp := coeff_mul_three thetaRatio thetaDenom analyticAt_thetaRatio analyticAt_thetaDenom
  have he := coeff_congr eventually_ratio_mul_denom 3
  change coeff (fun z => thetaRatio z * thetaDenom z) 3 = _ at hp
  have hr0 : coeff thetaRatio 0 = 0 := by simp [coeff, thetaRatio]
  rw [hp, coeff_denom_zero, coeff_denom_two, coeff_denom_odd 1 (by decide),
    coeff_denom_odd 3 (by decide), coeff_thetaRatio_one, coeff_num_three,
    hr0] at he
  ring_nf at he
  apply (mul_left_cancel₀ logTwo_ne)
  have hi : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ logTwo_ne
  ring_nf
  linear_combination he + hi

theorem coeff_thetaRatio_five : coeff thetaRatio 5 =
    1 - 4 / (3 * (Real.log 2 : ℂ)) + 1 / (2 * (Real.log 2 : ℂ) ^ 2) := by
  have hp := coeff_mul_five thetaRatio thetaDenom analyticAt_thetaRatio analyticAt_thetaDenom
  have he := coeff_congr eventually_ratio_mul_denom 5
  change coeff (fun z => thetaRatio z * thetaDenom z) 5 = _ at hp
  have hr0 : coeff thetaRatio 0 = 0 := by simp [coeff, thetaRatio]
  rw [hp, coeff_denom_zero, coeff_denom_two, coeff_denom_four,
    coeff_denom_odd 1 (by decide), coeff_denom_odd 3 (by decide),
    coeff_denom_odd 5 (by decide), coeff_thetaRatio_one, coeff_thetaRatio_three,
    coeff_num_five, hr0] at he
  ring_nf at he
  apply (mul_left_cancel₀ logTwo_ne)
  have hi : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ logTwo_ne
  have hred : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ ^ 2 =
      (Real.log 2 : ℂ)⁻¹ := by field_simp [logTwo_ne]
  ring_nf
  linear_combination he + (1 / 3) * hi - (1 / 2) * hred

private theorem thetaParam_eq : thetaParam = fun z : ℂ =>
    (2 / (Real.log 2 : ℂ)) * (atanhExt z + thetaRatio z) := by
  funext z
  rfl

theorem coeff_thetaParam_one : coeff thetaParam 1 = 4 / (Real.log 2 : ℂ) := by
  rw [thetaParam_eq, coeff_const_mul]
  have hs := coeff_add atanhExt thetaRatio analyticAt_atanhExt analyticAt_thetaRatio 1
  change coeff (fun z => atanhExt z + thetaRatio z) 1 = _ at hs
  rw [hs, coeff_atanhExt_one, coeff_thetaRatio_one]
  ring

theorem coeff_thetaParam_three : coeff thetaParam 3 =
    8 / (3 * (Real.log 2 : ℂ)) - 2 / (Real.log 2 : ℂ) ^ 2 := by
  rw [thetaParam_eq, coeff_const_mul]
  have hs := coeff_add atanhExt thetaRatio analyticAt_atanhExt analyticAt_thetaRatio 3
  change coeff (fun z => atanhExt z + thetaRatio z) 3 = _ at hs
  rw [hs, coeff_atanhExt_three, coeff_thetaRatio_three]
  ring_nf

theorem coeff_thetaParam_five : coeff thetaParam 5 =
    12 / (5 * (Real.log 2 : ℂ)) - 8 / (3 * (Real.log 2 : ℂ) ^ 2) +
      1 / (Real.log 2 : ℂ) ^ 3 := by
  rw [thetaParam_eq, coeff_const_mul]
  have hs := coeff_add atanhExt thetaRatio analyticAt_atanhExt analyticAt_thetaRatio 5
  change coeff (fun z => atanhExt z + thetaRatio z) 5 = _ at hs
  rw [hs, coeff_atanhExt_five, coeff_thetaRatio_five]
  ring_nf

theorem thetaTaylorCoeff_three : thetaTaylorCoeff 3 =
    64 / (3 * (Real.log 2 : ℂ)) - 32 / (Real.log 2 : ℂ) ^ 2 := by
  change coeff thetaGerm 3 = _
  have hc := coeff_comp thetaParam xBiasGerm analyticAt_thetaParam analyticAt_xBiasGerm
    xBiasGerm_zero 3
  change coeff thetaGerm 3 = _ at hc
  rw [hc, E8LowOrderThetaCoefficients.composeCoeff_three_odd
    (coeff thetaParam) (coeff xBiasGerm) (by simp [coeff, xBiasGerm_zero])
    coeff_xBiasGerm_two, coeff_thetaParam_one, coeff_thetaParam_three,
    coeff_xBiasGerm_one, coeff_xBiasGerm_three]
  field_simp [logTwo_ne]
  ring

theorem thetaTaylorCoeff_five : thetaTaylorCoeff 5 =
    384 / (5 * (Real.log 2 : ℂ)) - 224 / (Real.log 2 : ℂ) ^ 2 +
      192 / (Real.log 2 : ℂ) ^ 3 := by
  change coeff thetaGerm 5 = _
  have hc := coeff_comp thetaParam xBiasGerm analyticAt_thetaParam analyticAt_xBiasGerm
    xBiasGerm_zero 5
  change coeff thetaGerm 5 = _ at hc
  rw [hc, E8LowOrderThetaCoefficients.composeCoeff_five_odd
    (coeff thetaParam) (coeff xBiasGerm) (by simp [coeff, xBiasGerm_zero])
    coeff_xBiasGerm_two coeff_xBiasGerm_four, coeff_thetaParam_one,
    coeff_thetaParam_three, coeff_thetaParam_five, coeff_xBiasGerm_one,
    coeff_xBiasGerm_three, coeff_xBiasGerm_five]
  field_simp [logTwo_ne]
  ring

theorem qTaylorCoeff_three_formula : qTaylorCoeff 3 =
    -(Real.log 2 : ℂ) ^ 2 * (2 * (Real.log 2 : ℂ) - 3) / 384 :=
  E8LowOrderThetaCoefficients.qTaylorCoeff_three_formula_of_theta
    thetaTaylorCoeff_three

theorem qTaylorCoeff_five_formula : qTaylorCoeff 5 = (Real.log 2 : ℂ) ^ 3 *
    (44 * (Real.log 2 : ℂ) ^ 2 - 135 * (Real.log 2 : ℂ) + 90) / 122880 :=
  E8LowOrderThetaCoefficients.qTaylorCoeff_five_formula_of_theta
    thetaTaylorCoeff_three thetaTaylorCoeff_five

theorem qTaylorCoeff_three_in_sourceBox :
    ‖qTaylorCoeff 3 - (E8AnalyticCoefficientBoxes.sourceCenter 3 : ℂ)‖ ≤
      (E8AnalyticCoefficientBoxes.sourceHalfWidth 3 : ℝ) :=
  E8LowOrderThetaCoefficients.qTaylorCoeff_three_in_sourceBox_of_theta
    thetaTaylorCoeff_three

theorem qTaylorCoeff_five_in_sourceBox :
    ‖qTaylorCoeff 5 - (E8AnalyticCoefficientBoxes.sourceCenter 5 : ℂ)‖ ≤
      (E8AnalyticCoefficientBoxes.sourceHalfWidth 5 : ℝ) :=
  E8LowOrderThetaCoefficients.qTaylorCoeff_five_in_sourceBox_of_theta
    thetaTaylorCoeff_three thetaTaylorCoeff_five

theorem qTaylorCoeff_three_five_in_sourceBoxes :
    (‖qTaylorCoeff 3 - (E8AnalyticCoefficientBoxes.sourceCenter 3 : ℂ)‖ ≤
      (E8AnalyticCoefficientBoxes.sourceHalfWidth 3 : ℝ)) ∧
    (‖qTaylorCoeff 5 - (E8AnalyticCoefficientBoxes.sourceCenter 5 : ℂ)‖ ≤
      (E8AnalyticCoefficientBoxes.sourceHalfWidth 5 : ℝ)) :=
  ⟨qTaylorCoeff_three_in_sourceBox, qTaylorCoeff_five_in_sourceBox⟩

end GeneralCK.Certificates.E8ThetaParamCoeff5

end


