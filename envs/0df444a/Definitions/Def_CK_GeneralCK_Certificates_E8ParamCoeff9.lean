-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff9
-- name    : CK_GeneralCK_Certificates_E8ParamCoeff9
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:01:16.521957+00:00
-- url     : https://prove2.me/theorems/54232225-47df-4368-bd63-b462c8c499f2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ParamCoeff9` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ParamCoeff9` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ParamCoeff9` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ParamCoeff9 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ParamCoeff9.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff9
import Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff9

-- ===== source module GeneralCK.Certificates.E8ParamCoeff9 =====
section

namespace GeneralCK.Certificates.E8ParamCoeff9

open Filter
open E8AnalyticGerm Reflection.ComplexEntropy Reflection.ComplexContactFactor
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8NormalizedCoeff7
open E8ElementaryCoeff5 E8ElementaryCoeff7
open E8ElementaryCoeff9 E8ParamCoeff5 E8ParamCoeff7
open E8ComposeCoeff9

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

theorem coeff_xParam_nine : coeff xParam 9 =
    1 / (112 * (Real.log 2 : ℂ)) + 29 / (1440 * (Real.log 2 : ℂ)^2) +
      1 / (32 * (Real.log 2 : ℂ)^3) + 1 / (32 * (Real.log 2 : ℂ)^4) := by
  have hp := coeff_mul entropyExt xParam
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num)) analyticAt_xParam 9
  have he := coeff_congr eventually_entropy_mul_xParam 9
  change coeff (fun z : ℂ => entropyExt z * xParam z) 9 = _ at hp
  rw [hp] at he
  norm_num [Finset.sum_range_succ, coeff_entropyExt_zero, coeff_entropyExt_two,
    coeff_entropyExt_four, coeff_entropyExt_six, coeff_entropyExt_eight,
    coeff_entropy_odd, coeff_xParam_one, coeff_xParam_three, coeff_xParam_five,
    coeff_xParam_seven, coeff_xParam_even] at he
  rw [coeff_entropy_odd 3 (by decide), coeff_entropy_odd 5 (by decide),
    coeff_xParam_even 4 (by decide), coeff_xParam_even 6 (by decide)] at he
  rw [clogTwo_eq] at he
  have hr : coeff (fun z : ℂ => (Real.log 2 : ℂ) * z / 2) 9 = 0 := by
    rw [coeff, iteratedDeriv_div_const, iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_fun_id_zero]
  rw [hr] at he
  apply mul_left_cancel₀ logTwo_ne
  ring_nf at he ⊢
  have hi0 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ logTwo_ne
  have hi1 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^2 =
      (Real.log 2 : ℂ)⁻¹ := by field_simp [logTwo_ne]
  have hi2 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^3 =
      (Real.log 2 : ℂ)⁻¹^2 := by field_simp [logTwo_ne]
  have hi3 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^4 =
      (Real.log 2 : ℂ)⁻¹^3 := by field_simp [logTwo_ne]
  linear_combination he - (1 / 112) * hi0 - (29 / 1440) * hi1 -
    (1 / 32) * hi2 - (1 / 32) * hi3

private theorem deriv_xParam_ne : deriv xParam 0 ≠ 0 := by
  rw [hasDerivAt_xParam_zero.deriv]
  norm_num

private theorem eventually_xBias_xParam :
    (xBiasGerm ∘ xParam) =ᶠ[nhds (0 : ℂ)] id := by
  have h := analyticAt_xParam.hasStrictDerivAt.eventually_left_inverse deriv_xParam_ne
  change ∀ᶠ x in nhds (0 : ℂ), xBiasGerm (xParam x) = x
  simpa only [xBiasGerm] using h

theorem eventually_xBiasGerm_neg :
    (fun z : ℂ => xBiasGerm (-z)) =ᶠ[nhds 0] (fun z => -xBiasGerm z) := by
  have hs := analyticAt_xParam.hasStrictDerivAt
  have hl := hs.eventually_left_inverse deriv_xParam_ne
  have hr := hs.eventually_right_inverse deriv_xParam_ne
  rw [xParam_zero] at hr
  have tn : Tendsto (fun z : ℂ => -z) (nhds 0) (nhds 0) := by
    simpa using (continuousAt_neg.tendsto : Tendsto (fun z : ℂ => -z) (nhds 0) (nhds (-0)))
  have tb : Tendsto xBiasGerm (nhds 0) (nhds 0) := by
    simpa [xBiasGerm_zero] using analyticAt_xBiasGerm.continuousAt.tendsto
  have tnb : Tendsto (fun z : ℂ => -xBiasGerm z) (nhds 0) (nhds 0) := by
    simpa using tb.neg
  filter_upwards [hr, tn.eventually hr, tnb.eventually hl] with z hz hnz hlz
  calc
    xBiasGerm (-z) = xBiasGerm (xParam (-xBiasGerm z)) := by
      congr 1
      rw [xParam_neg]
      change -z = -xParam
        (HasStrictDerivAt.localInverse xParam (deriv xParam 0) 0 hs deriv_xParam_ne z)
      rw [hz]
    _ = -xBiasGerm z := hlz

theorem coeff_xBiasGerm_even {n : ℕ} (hn : Even n) : coeff xBiasGerm n = 0 := by
  have hd := eventually_xBiasGerm_neg.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at hd
  simp only [neg_zero, Even.neg_one_pow hn, one_smul] at hd
  unfold coeff
  have hz : iteratedDeriv n xBiasGerm 0 = 0 := by
    linear_combination (1 / 2 : ℂ) * hd
  simp [hz]

theorem coeff_xBiasGerm_nine : coeff xBiasGerm 9 =
    -64 / (7 * (Real.log 2 : ℂ)) + 3712 / (45 * (Real.log 2 : ℂ)^2) -
      896 / (3 * (Real.log 2 : ℂ)^3) + 448 / (Real.log 2 : ℂ)^4 := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 9
  have hi := coeff_congr eventually_xBias_xParam 9
  have hid : coeff id 9 = 0 := by rw [coeff, iteratedDeriv_id]; norm_num
  rw [hc, composeCoeff_nine_odd (coeff xBiasGerm) (coeff xParam)
    coeff_xBiasGerm_two coeff_xBiasGerm_four coeff_xBiasGerm_six
    (by simp [coeff, xParam_zero]) (coeff_xParam_even 2 (by decide))
    (coeff_xParam_even 4 (by decide)) (coeff_xParam_even 6 (by decide))
    (coeff_xParam_even 8 (by decide)), hid] at hi
  rw [coeff_xParam_one, coeff_xParam_three, coeff_xParam_five, coeff_xParam_seven,
    coeff_xParam_nine, coeff_xBiasGerm_one, coeff_xBiasGerm_three,
    coeff_xBiasGerm_five, coeff_xBiasGerm_seven] at hi
  ring_nf at hi ⊢
  linear_combination 512 * hi

end GeneralCK.Certificates.E8ParamCoeff9

end


