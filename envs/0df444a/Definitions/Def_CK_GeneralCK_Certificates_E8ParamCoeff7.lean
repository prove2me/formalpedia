-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff7
-- name    : CK_GeneralCK_Certificates_E8ParamCoeff7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:42:55.184189+00:00
-- url     : https://prove2.me/theorems/ab81969a-9c94-4d55-8084-2382c9bdd929
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ParamCoeff7` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ParamCoeff7` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ParamCoeff7` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ParamCoeff7 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ParamCoeff7.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff7
import Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff7

-- ===== source module GeneralCK.Certificates.E8ParamCoeff7 =====
section

namespace GeneralCK.Certificates.E8ParamCoeff7

open Filter
open E8AnalyticGerm Reflection.ComplexEntropy Reflection.ComplexContactFactor
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8NormalizedCoeff7
open E8ElementaryCoeff5 E8ElementaryCoeff7 E8ParamCoeff5 E8ComposeCoeff7

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

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

theorem coeff_xParam_seven : coeff xParam 7 =
    1 / (60 * (Real.log 2 : ℂ)) + 1 / (24 * (Real.log 2 : ℂ)^2) +
      1 / (16 * (Real.log 2 : ℂ)^3) := by
  have hp := coeff_mul_seven entropyExt xParam
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num)) analyticAt_xParam
  have he := coeff_congr eventually_entropy_mul_xParam 7
  change coeff (fun z : ℂ => entropyExt z * xParam z) 7 = _ at hp
  rw [hp, coeff_entropyExt_zero, coeff_entropy_odd 1 (by decide),
    coeff_entropyExt_two, coeff_entropy_odd 3 (by decide), coeff_entropyExt_four,
    coeff_entropy_odd 5 (by decide), coeff_entropyExt_six,
    coeff_entropy_odd 7 (by decide), coeff_xParam_one, coeff_xParam_three,
    coeff_xParam_five, coeff_xParam_even 2 (by decide),
    coeff_xParam_even 4 (by decide), coeff_xParam_even 6 (by decide)] at he
  have hr : coeff (fun z : ℂ => (Real.log 2 : ℂ) * z / 2) 7 = 0 := by
    rw [coeff, iteratedDeriv_div_const, iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_fun_id_zero]
  rw [hr] at he
  apply mul_left_cancel₀ logTwo_ne
  ring_nf at he ⊢
  have hi0 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ logTwo_ne
  have hi1 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ ^ 2 =
      (Real.log 2 : ℂ)⁻¹ := by field_simp [logTwo_ne]
  have hi2 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ ^ 3 =
      (Real.log 2 : ℂ)⁻¹ ^ 2 := by field_simp [logTwo_ne]
  linear_combination he - (1 / 60) * hi0 - (1 / 24) * hi1 - (1 / 16) * hi2

private theorem deriv_xParam_ne : deriv xParam 0 ≠ 0 := by
  rw [hasDerivAt_xParam_zero.deriv]
  norm_num

private theorem eventually_xBias_xParam :
    (xBiasGerm ∘ xParam) =ᶠ[nhds (0 : ℂ)] id := by
  have h := analyticAt_xParam.hasStrictDerivAt.eventually_left_inverse deriv_xParam_ne
  change ∀ᶠ x in nhds (0 : ℂ), xBiasGerm (xParam x) = x
  simpa only [xBiasGerm] using h

theorem coeff_xBiasGerm_six : coeff xBiasGerm 6 = 0 := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 6
  have hi := coeff_congr eventually_xBias_xParam 6
  have hid : coeff id 6 = 0 := by rw [coeff, iteratedDeriv_id]; norm_num
  have hp3 : powCoeff (coeff xParam) 3 6 = 0 := by
    simp [powCoeff, Finset.sum_range_succ, coeff_xParam_even 2 (by decide),
      coeff_xParam_even 4 (by decide), coeff_xParam_even 6 (by decide),
      show coeff xParam 0 = 0 by simp [coeff, xParam_zero]]
  rw [hc, hid] at hi
  simp only [composeCoeff, Finset.sum_range_succ] at hi
  rw [powCoeff_one, coeff_xParam_even 6 (by decide), coeff_xBiasGerm_two,
    coeff_xBiasGerm_four, hp3,
    powCoeff_next_diag_zero (coeff xParam) (by simp [coeff, xParam_zero])
      (coeff_xParam_even 2 (by decide)) 5,
    powCoeff_diag (coeff xParam) (by simp [coeff, xParam_zero]) 6] at hi
  norm_num [powCoeff, coeff_xParam_one] at hi
  have hd : iteratedDeriv 6 xBiasGerm 0 = 0 :=
    (mul_eq_zero.mp hi).resolve_right (by norm_num)
  simp [coeff, hd]

theorem coeff_xBiasGerm_seven : coeff xBiasGerm 7 =
    -64 / (15 * (Real.log 2 : ℂ)) + 32 / (Real.log 2 : ℂ)^2 -
      80 / (Real.log 2 : ℂ)^3 := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 7
  have hi := coeff_congr eventually_xBias_xParam 7
  have hid : coeff id 7 = 0 := by rw [coeff, iteratedDeriv_id]; norm_num
  rw [hc, composeCoeff_seven_odd (coeff xBiasGerm) (coeff xParam)
    (by simp [coeff, xParam_zero]) (coeff_xParam_even 2 (by decide))
    (coeff_xParam_even 4 (by decide)) (coeff_xParam_even 6 (by decide)), hid] at hi
  rw [coeff_xParam_one, coeff_xParam_three, coeff_xParam_five, coeff_xParam_seven,
    coeff_xBiasGerm_one, coeff_xBiasGerm_three, coeff_xBiasGerm_five] at hi
  ring_nf at hi ⊢
  linear_combination 128 * hi

end GeneralCK.Certificates.E8ParamCoeff7

end


