-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff15
-- name    : CK_GeneralCK_Certificates_E8ParamCoeff15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:19:42.778861+00:00
-- url     : https://prove2.me/theorems/36ff27fc-bbe3-44d7-aaf0-1d6ea666a655
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ParamCoeff15` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ParamCoeff15` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ParamCoeff15` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ParamCoeff15 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ParamCoeff15.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff15
import Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff9
import Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff11
import Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff13

-- ===== source module GeneralCK.Certificates.E8ParamCoeff15 =====
section

namespace GeneralCK.Certificates.E8ParamCoeff15

open Filter
open E8AnalyticGerm Reflection.ComplexEntropy Reflection.ComplexContactFactor
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8NormalizedCoeff7
open E8ElementaryCoeff5 E8ElementaryCoeff7 E8ElementaryCoeff9 E8ElementaryCoeff11
open E8ElementaryCoeff13 E8ElementaryCoeff15
open E8ParamCoeff5 E8ParamCoeff7 E8ParamCoeff9 E8ParamCoeff11 E8ParamCoeff13 E8ComposeCoeff15

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

theorem coeff_xParam_fifteen : coeff xParam 15 =
    1 / (364 * (Real.log 2 : ℂ)) + 883 / (166320 * (Real.log 2 : ℂ)^2) +
      191 / (25200 * (Real.log 2 : ℂ)^3) + 557 / (60480 * (Real.log 2 : ℂ)^4) +
      11 / (1152 * (Real.log 2 : ℂ)^5) + 1 / (128 * (Real.log 2 : ℂ)^6) +
      1 / (256 * (Real.log 2 : ℂ)^7) := by
  have hp := coeff_mul entropyExt xParam
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num)) analyticAt_xParam 15
  have he := coeff_congr eventually_entropy_mul_xParam 15
  change coeff (fun z : ℂ => entropyExt z * xParam z) 15 = _ at hp
  rw [hp] at he
  norm_num [Finset.sum_range_succ, coeff_entropyExt_zero, coeff_entropyExt_two,
    coeff_entropyExt_four, coeff_entropyExt_six, coeff_entropyExt_eight,
    coeff_entropyExt_ten, coeff_entropyExt_twelve, coeff_entropyExt_fourteen,
    coeff_entropy_odd,
    coeff_xParam_one, coeff_xParam_three,
    coeff_xParam_five, coeff_xParam_seven, coeff_xParam_nine,
    coeff_xParam_eleven, coeff_xParam_thirteen, coeff_xParam_even] at he
  rw [coeff_xParam_even 4 (by decide), coeff_xParam_even 6 (by decide),
    coeff_xParam_even 8 (by decide), coeff_xParam_even 10 (by decide),
    coeff_xParam_even 12 (by decide)] at he
  norm_num at he
  have hr : coeff (fun z : ℂ => (Real.log 2 : ℂ) * z / 2) 15 = 0 := by
    rw [coeff, iteratedDeriv_div_const, iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_fun_id_zero]
  rw [clogTwo_eq] at he
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
  have hi4 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^5 =
      (Real.log 2 : ℂ)⁻¹^4 := by field_simp [logTwo_ne]
  have hi5 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^6 =
      (Real.log 2 : ℂ)⁻¹^5 := by field_simp [logTwo_ne]
  have hi6 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^7 =
      (Real.log 2 : ℂ)⁻¹^6 := by field_simp [logTwo_ne]
  linear_combination he - (1 / 364) * hi0 - (883 / 166320) * hi1 -
    (191 / 25200) * hi2 - (557 / 60480) * hi3 - (11 / 1152) * hi4 -
    (1 / 128) * hi5 - (1 / 256) * hi6

private theorem deriv_xParam_ne : deriv xParam 0 ≠ 0 := by
  rw [hasDerivAt_xParam_zero.deriv]
  norm_num

private theorem eventually_xBias_xParam :
    (xBiasGerm ∘ xParam) =ᶠ[nhds (0 : ℂ)] id := by
  have h := analyticAt_xParam.hasStrictDerivAt.eventually_left_inverse deriv_xParam_ne
  change ∀ᶠ x in nhds (0 : ℂ), xBiasGerm (xParam x) = x
  simpa only [xBiasGerm] using h

theorem coeff_xBiasGerm_fifteen : coeff xBiasGerm 15 =
    -16384 / (91*(Real.log 2 : ℂ)) + 3616768 / (1485*(Real.log 2 : ℂ)^2) -
      10170368 / (675*(Real.log 2 : ℂ)^3) + 7414784 / (135*(Real.log 2 : ℂ)^4) -
      5637632 / (45*(Real.log 2 : ℂ)^5) + 512512 / (3*(Real.log 2 : ℂ)^6) -
      109824 / (Real.log 2 : ℂ)^7 := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 15
  have hi := coeff_congr eventually_xBias_xParam 15
  have hid : coeff id 15 = 0 := by rw [coeff, iteratedDeriv_id]; norm_num
  rw [hc, composeCoeff_fifteen_odd (coeff xBiasGerm) (coeff xParam)
    (coeff_xBiasGerm_even (by decide : Even 2))
    (coeff_xBiasGerm_even (by decide : Even 4))
    (coeff_xBiasGerm_even (by decide : Even 6))
    (coeff_xBiasGerm_even (by decide : Even 8))
    (coeff_xBiasGerm_even (by decide : Even 10))
    (coeff_xBiasGerm_even (by decide : Even 12))
    (by simp [coeff, xParam_zero]) (coeff_xParam_even 2 (by decide))
    (coeff_xParam_even 4 (by decide)) (coeff_xParam_even 6 (by decide))
    (coeff_xParam_even 8 (by decide)) (coeff_xParam_even 10 (by decide))
    (coeff_xParam_even 12 (by decide)) (coeff_xParam_even 14 (by decide)), hid] at hi
  rw [coeff_xParam_one, coeff_xParam_three, coeff_xParam_five, coeff_xParam_seven,
    coeff_xParam_nine, coeff_xParam_eleven, coeff_xParam_thirteen,
    coeff_xParam_fifteen, coeff_xBiasGerm_one,
    coeff_xBiasGerm_three, coeff_xBiasGerm_five, coeff_xBiasGerm_seven,
    coeff_xBiasGerm_nine, coeff_xBiasGerm_eleven, coeff_xBiasGerm_thirteen] at hi
  ring_nf at hi ⊢
  linear_combination 32768 * hi

end GeneralCK.Certificates.E8ParamCoeff15

end


