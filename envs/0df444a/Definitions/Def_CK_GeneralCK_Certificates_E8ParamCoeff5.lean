-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff5
-- name    : CK_GeneralCK_Certificates_E8ParamCoeff5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:27:13.901353+00:00
-- url     : https://prove2.me/theorems/cb133287-6f97-416c-af87-1271dc712484
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ParamCoeff5` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ParamCoeff5` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ParamCoeff5` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ParamCoeff5 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ParamCoeff5.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff5

-- ===== source module GeneralCK.Certificates.E8ParamCoeff5 =====
section

namespace GeneralCK.Certificates.E8ParamCoeff5

open Filter
open E8AnalyticGerm Reflection.ComplexEntropy Reflection.ComplexContactFactor
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8ElementaryCoeff5

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

private theorem clogTwo_eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.natCast_log (n := 2)).symm

private theorem eventually_entropy_mul_xParam :
    (fun z : ℂ => entropyExt z * xParam z) =ᶠ[nhds 0]
      (fun z => (Real.log 2 : ℂ) * z / 2) := by
  have h0 : entropyExt 0 ≠ 0 := by
    rw [Reflection.ComplexContactGerm.entropyExt_zero]
    exact logTwo_ne
  have hE := (Reflection.ComplexContactGerm.analyticAt_entropyExt (c := (0 : ℂ))
    (by norm_num)).continuousAt.eventually_ne h0
  filter_upwards [hE] with z hz
  simp only [xParam]
  field_simp [hz]

private theorem coeff_entropy_odd (n : ℕ) (hn : Odd n) : coeff entropyExt n = 0 :=
  coeff_even_zero_of_odd entropyExt_neg hn

private theorem coeff_xParam_even (n : ℕ) (hn : Even n) : coeff xParam n = 0 :=
  coeff_odd_zero_of_even xParam_neg hn

theorem coeff_xParam_one : coeff xParam 1 = 1 / 2 := by
  rw [coeff, iteratedDeriv_one, hasDerivAt_xParam_zero.deriv]
  norm_num

theorem coeff_xParam_three : coeff xParam 3 = 1 / (4 * (Real.log 2 : ℂ)) := by
  have hp := coeff_mul_three entropyExt xParam
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num)) analyticAt_xParam
  have he := coeff_congr eventually_entropy_mul_xParam 3
  change coeff (fun z : ℂ => entropyExt z * xParam z) 3 = _ at hp
  rw [hp, coeff_entropyExt_zero, coeff_entropy_odd 1 (by decide),
    coeff_entropyExt_two, coeff_entropy_odd 3 (by decide), coeff_xParam_one,
    coeff_xParam_even 2 (by decide)] at he
  have hr : coeff (fun z : ℂ => (Real.log 2 : ℂ) * z / 2) 3 = 0 := by
    rw [coeff, iteratedDeriv_div_const, iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_fun_id_zero]
  rw [hr] at he
  apply (eq_div_iff (mul_ne_zero (by norm_num) logTwo_ne)).2
  linear_combination 4 * he

theorem coeff_xParam_five : coeff xParam 5 =
    1 / (24 * (Real.log 2 : ℂ)) + 1 / (8 * (Real.log 2 : ℂ) ^ 2) := by
  have hp := coeff_mul_five entropyExt xParam
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num)) analyticAt_xParam
  have he := coeff_congr eventually_entropy_mul_xParam 5
  change coeff (fun z : ℂ => entropyExt z * xParam z) 5 = _ at hp
  rw [hp, coeff_entropyExt_zero, coeff_entropy_odd 1 (by decide),
    coeff_entropyExt_two, coeff_entropy_odd 3 (by decide), coeff_entropyExt_four,
    coeff_entropy_odd 5 (by decide), coeff_xParam_one, coeff_xParam_three,
    coeff_xParam_even 2 (by decide), coeff_xParam_even 4 (by decide)] at he
  have hr : coeff (fun z : ℂ => (Real.log 2 : ℂ) * z / 2) 5 = 0 := by
    rw [coeff, iteratedDeriv_div_const, iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_fun_id_zero]
  rw [hr] at he
  ring_nf at he
  rw [show 1 / (24 * (Real.log 2 : ℂ)) + 1 / (8 * (Real.log 2 : ℂ) ^ 2) =
      ((Real.log 2 : ℂ) + 3) / (24 * (Real.log 2 : ℂ) ^ 2) by
        field_simp [logTwo_ne]
        ring]
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 logTwo_ne))).2
  have hi : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ logTwo_ne
  linear_combination (24 * (Real.log 2 : ℂ)) * he + 3 * hi

private theorem deriv_xParam_ne : deriv xParam 0 ≠ 0 := by
  rw [hasDerivAt_xParam_zero.deriv]
  norm_num

private theorem eventually_xBias_xParam :
    (xBiasGerm ∘ xParam) =ᶠ[nhds (0 : ℂ)] id := by
  have h := analyticAt_xParam.hasStrictDerivAt.eventually_left_inverse deriv_xParam_ne
  change ∀ᶠ x in nhds (0 : ℂ), xBiasGerm (xParam x) = x
  simpa only [xBiasGerm] using h

theorem coeff_xBiasGerm_one : coeff xBiasGerm 1 = 2 := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 1
  have hi := coeff_congr eventually_xBias_xParam 1
  have hid : coeff id 1 = 1 := by rw [coeff, iteratedDeriv_id]; norm_num
  rw [hc] at hi
  rw [hid] at hi
  norm_num [composeCoeff, powCoeff, Finset.sum_range_succ,
    xBiasGerm_zero, xParam_zero, coeff_xParam_one] at hi
  linear_combination 2 * hi

theorem coeff_xBiasGerm_three :
    coeff xBiasGerm 3 = -4 / (Real.log 2 : ℂ) := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 3
  have hi := coeff_congr eventually_xBias_xParam 3
  have hid : coeff id 3 = 0 := by rw [coeff, iteratedDeriv_id]; norm_num
  rw [hc, E8LowOrderThetaCoefficients.composeCoeff_three_odd
    (coeff xBiasGerm) (coeff xParam) (by simp [coeff, xParam_zero])
    (coeff_xParam_even 2 (by decide)), hid] at hi
  norm_num [coeff_xParam_one, coeff_xParam_three,
    coeff_xBiasGerm_one] at hi
  rw [clogTwo_eq] at hi
  field_simp [logTwo_ne] at hi ⊢
  linear_combination (1 / 4) * hi

theorem coeff_xBiasGerm_two : coeff xBiasGerm 2 = 0 := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 2
  have hi := coeff_congr eventually_xBias_xParam 2
  have hid : coeff id 2 = 0 := by rw [coeff, iteratedDeriv_id]; norm_num
  rw [hc] at hi
  norm_num [composeCoeff, powCoeff, Finset.sum_range_succ, coeff_xParam_one,
    coeff_xParam_even 2 (by decide), coeff_xBiasGerm_one, hid] at hi
  exact hi

theorem coeff_xBiasGerm_four : coeff xBiasGerm 4 = 0 := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 4
  have hi := coeff_congr eventually_xBias_xParam 4
  have hid : coeff id 4 = 0 := by rw [coeff, iteratedDeriv_id]; norm_num
  rw [hc] at hi
  norm_num [composeCoeff, powCoeff, Finset.sum_range_succ, coeff_xParam_one,
    coeff_xParam_three, coeff_xParam_even 2 (by decide), coeff_xParam_even 4 (by decide),
    coeff_xBiasGerm_one, coeff_xBiasGerm_two, coeff_xBiasGerm_three, hid] at hi
  exact hi

theorem coeff_xBiasGerm_five : coeff xBiasGerm 5 =
    16 / (Real.log 2 : ℂ) ^ 2 - 8 / (3 * (Real.log 2 : ℂ)) := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 5
  have hi := coeff_congr eventually_xBias_xParam 5
  have hid : coeff id 5 = 0 := by rw [coeff, iteratedDeriv_id]; norm_num
  rw [hc, E8LowOrderThetaCoefficients.composeCoeff_five_odd
    (coeff xBiasGerm) (coeff xParam) (by simp [coeff, xParam_zero])
    (coeff_xParam_even 2 (by decide)) (coeff_xParam_even 4 (by decide)), hid] at hi
  norm_num [coeff_xParam_one, coeff_xParam_three,
    coeff_xParam_five, coeff_xBiasGerm_one, coeff_xBiasGerm_three] at hi
  rw [clogTwo_eq] at hi
  ring_nf at hi
  rw [show 16 / (Real.log 2 : ℂ) ^ 2 - 8 / (3 * (Real.log 2 : ℂ)) =
      16 * (Real.log 2 : ℂ)⁻¹ ^ 2 - (8 / 3) * (Real.log 2 : ℂ)⁻¹ by
        field_simp [logTwo_ne]]
  linear_combination 32 * hi

end GeneralCK.Certificates.E8ParamCoeff5

end


