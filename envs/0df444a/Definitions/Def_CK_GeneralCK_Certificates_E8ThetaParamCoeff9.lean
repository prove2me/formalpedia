-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ThetaParamCoeff9
-- name    : CK_GeneralCK_Certificates_E8ThetaParamCoeff9
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:05:56.433357+00:00
-- url     : https://prove2.me/theorems/bec32225-f26e-411d-892c-784df923b260
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ThetaParamCoeff9` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ThetaParamCoeff9` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ThetaParamCoeff9` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ThetaParamCoeff9 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ThetaParamCoeff9.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff9

-- ===== source module GeneralCK.Certificates.E8ThetaParamCoeff9 =====
section

namespace GeneralCK.Certificates.E8ThetaParamCoeff9

open E8AnalyticGerm Reflection.ComplexEntropy Reflection.ComplexContactFactor
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8NormalizedCoeff7
open E8ElementaryCoeff5 E8ElementaryCoeff7 E8ElementaryCoeff9
open E8ParamCoeff5 E8ParamCoeff7 E8ParamCoeff9
open E8ThetaParamCoeff5 E8ThetaParamCoeff7 E8ComposeCoeff9
open E8LowOrderThetaCoefficients
open E8HigherRationalTrace E8HigherSourceBoxBridge E8AnalyticCoefficientBoxes

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

theorem coeff_denom_eight : coeff thetaDenom 8 = -1 / 24 := by
  have h := coeff_mul (fun z : ℂ => 1 - z ^ 2) biasBExt
    (analyticAt_const.sub (analyticAt_id.pow 2)) analyticAt_biasBExt 8
  change coeff thetaDenom 8 = _ at h
  rw [h]
  norm_num [Finset.sum_range_succ, coeff_one_sub_sq, coeff_biasBExt_eight,
    coeff_biasBExt_six, coeff_biasBExt_four,
    coeff_even_zero_of_odd biasBExt_neg (by decide : Odd 1),
    coeff_even_zero_of_odd biasBExt_neg (by decide : Odd 3),
    coeff_even_zero_of_odd biasBExt_neg (by decide : Odd 5),
    coeff_even_zero_of_odd biasBExt_neg (by decide : Odd 7)]

private theorem coeff_num_nine : coeff (fun z : ℂ => z * entropyExt z) 9 = -1 / 56 := by
  have h := coeff_mul id entropyExt analyticAt_id
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num)) 9
  change coeff (fun z : ℂ => z * entropyExt z) 9 = _ at h
  rw [h]
  have hid (n : ℕ) : coeff id n = if n = 1 then 1 else 0 := by
    rcases n with (_ | n)
    · simp [coeff]
    · rcases n with (_ | n)
      · simp [coeff, iteratedDeriv_id]
      · simp [coeff, iteratedDeriv_id]
  norm_num [Finset.sum_range_succ, hid, coeff_entropyExt_eight]

private theorem coeff_thetaRatio_even (n : ℕ) (hn : Even n) : coeff thetaRatio n = 0 := by
  apply coeff_odd_zero_of_even _ hn
  intro z
  simp [thetaRatio, thetaDenom, entropyExt_neg, biasBExt_neg]
  ring

theorem coeff_thetaRatio_nine : coeff thetaRatio 9 =
    1 - 176 / (105 * (Real.log 2 : ℂ)) + 19 / (15 * (Real.log 2 : ℂ)^2) -
      7 / (12 * (Real.log 2 : ℂ)^3) + 1 / (8 * (Real.log 2 : ℂ)^4) := by
  have hp := coeff_mul thetaRatio thetaDenom analyticAt_thetaRatio analyticAt_thetaDenom 9
  have he := coeff_congr eventually_ratio_mul_denom 9
  change coeff (fun z => thetaRatio z * thetaDenom z) 9 = _ at hp
  rw [hp] at he
  norm_num [Finset.sum_range_succ, coeff_denom_zero, coeff_denom_two,
    coeff_denom_four, coeff_denom_six, coeff_denom_eight, coeff_denom_odd,
    coeff_thetaRatio_one, coeff_thetaRatio_three, coeff_thetaRatio_five,
    coeff_thetaRatio_seven, coeff_num_nine] at he
  rw [coeff_thetaRatio_even 2 (by decide), coeff_thetaRatio_even 4 (by decide),
    coeff_thetaRatio_even 6 (by decide), coeff_denom_odd 3 (by decide),
    coeff_denom_odd 5 (by decide), coeff_denom_odd 7 (by decide),
    coeff_denom_odd 9 (by decide)] at he
  simp [thetaRatio, thetaDenom_zero] at he
  rw [show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) by
    exact (Complex.natCast_log (n := 2)).symm] at he
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
  linear_combination he + (1 / 7) * hi0 - (11 / 30) * hi1 +
    (7 / 24) * hi2 - (1 / 8) * hi3 + (1 / 60) * hi1 + (1 / 24) * hi2

private theorem thetaParam_eq : thetaParam = fun z : ℂ =>
    (2 / (Real.log 2 : ℂ)) * (atanhExt z + thetaRatio z) := by
  funext z
  rfl

theorem coeff_thetaParam_nine : coeff thetaParam 9 =
    20 / (9 * (Real.log 2 : ℂ)) - 352 / (105 * (Real.log 2 : ℂ)^2) +
      38 / (15 * (Real.log 2 : ℂ)^3) - 7 / (6 * (Real.log 2 : ℂ)^4) +
      1 / (4 * (Real.log 2 : ℂ)^5) := by
  rw [thetaParam_eq, coeff_const_mul]
  have hs := coeff_add atanhExt thetaRatio analyticAt_atanhExt analyticAt_thetaRatio 9
  change coeff (fun z => atanhExt z + thetaRatio z) 9 = _ at hs
  rw [hs, coeff_atanhExt_nine, coeff_thetaRatio_nine]
  ring_nf

private theorem coeff_thetaParam_even (n : ℕ) (hn : Even n) : coeff thetaParam n = 0 :=
  coeff_odd_zero_of_even thetaParam_neg hn

theorem thetaTaylorCoeff_nine : thetaTaylorCoeff 9 =
    256 * (280*(Real.log 2 : ℂ)^4 - 1599*(Real.log 2 : ℂ)^3 +
      3766*(Real.log 2 : ℂ)^2 - 4410*(Real.log 2 : ℂ) + 2205) /
      (63*(Real.log 2 : ℂ)^5) := by
  change coeff thetaGerm 9 = _
  have hc := coeff_comp thetaParam xBiasGerm analyticAt_thetaParam analyticAt_xBiasGerm
    xBiasGerm_zero 9
  change coeff thetaGerm 9 = _ at hc
  rw [hc, composeCoeff_nine_odd (coeff thetaParam) (coeff xBiasGerm)
    (coeff_thetaParam_even 2 (by decide)) (coeff_thetaParam_even 4 (by decide))
    (coeff_thetaParam_even 6 (by decide)) (by simp [coeff, xBiasGerm_zero])
    coeff_xBiasGerm_two coeff_xBiasGerm_four coeff_xBiasGerm_six
    (coeff_xBiasGerm_even (by decide : Even 8)), coeff_thetaParam_one,
    coeff_thetaParam_three, coeff_thetaParam_five, coeff_thetaParam_seven,
    coeff_thetaParam_nine, coeff_xBiasGerm_one, coeff_xBiasGerm_three,
    coeff_xBiasGerm_five, coeff_xBiasGerm_seven, coeff_xBiasGerm_nine]
  field_simp [logTwo_ne]
  ring

private theorem thetaTaylorCoeff_even (n : ℕ) (hn : Even n) :
    thetaTaylorCoeff n = 0 := by
  have heq : (fun z : ℂ => thetaGerm (-z)) =ᶠ[nhds 0]
      (fun z => -thetaGerm z) := by
    filter_upwards [eventually_xBiasGerm_neg] with z hz
    simp only [thetaGerm, Function.comp_apply, hz, thetaParam_neg]
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at hd
  simp only [neg_zero, Even.neg_one_pow hn, one_smul] at hd
  unfold thetaTaylorCoeff
  have hz : iteratedDeriv n thetaGerm 0 = 0 := by
    linear_combination (1 / 2 : ℂ) * hd
  simp [hz]

private theorem clogTwo_eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.natCast_log (n := 2)).symm
private theorem clogTwo_ne : Complex.log (2 : ℂ) ≠ 0 := by
  rw [clogTwo_eq]
  exact logTwo_ne

set_option maxHeartbeats 0 in
theorem qTaylorCoeff_nine_formula :
    qTaylorCoeff 9 = (q9Formula (Real.log 2) : ℂ) := by
  have hc := composeCoeff_theta_q 9
  rw [composeCoeff_nine_odd thetaTaylorCoeff qTaylorCoeff
    (thetaTaylorCoeff_even 2 (by decide)) (thetaTaylorCoeff_even 4 (by decide))
    (thetaTaylorCoeff_even 6 (by decide)) qTaylorCoeff_zero
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 2))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 4))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 6))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 8))] at hc
  rw [thetaTaylorCoeff_one, thetaTaylorCoeff_three, thetaTaylorCoeff_five,
    thetaTaylorCoeff_seven, thetaTaylorCoeff_nine, qTaylorCoeff_one,
    qTaylorCoeff_three_formula, qTaylorCoeff_five_formula,
    qTaylorCoeff_seven_formula] at hc
  rw [q7Formula] at hc
  push_cast at hc
  norm_num [targetCoeff] at hc
  rw [clogTwo_eq] at hc
  change qTaylorCoeff 9 = ((q9Formula (Real.log 2) : ℝ) : ℂ)
  rw [q9Formula]
  push_cast
  have hc' := congrArg (fun z => z * (Real.log 2 : ℂ)) hc
  field_simp [logTwo_ne] at hc' ⊢
  simp [mul_assoc, mul_left_comm, mul_comm] at hc' ⊢
  rcases hc' with (hzero | hc') | hzero
  · exact (clogTwo_ne hzero).elim
  · ring_nf at hc' ⊢
    linear_combination (1 / 643492329157205950464000) * hc'
  · exact (clogTwo_ne hzero).elim

theorem inverseStep_nine_formula :
    inverseStep thetaTaylorCoeff qTaylorCoeff 9 = (q9Formula (Real.log 2) : ℂ) := by
  rw [← qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 9)]
  exact qTaylorCoeff_nine_formula

theorem qTaylorCoeff_nine_in_sourceBox :
    ‖qTaylorCoeff 9 - (sourceCenter 9 : ℂ)‖ ≤ (sourceHalfWidth 9 : ℝ) := by
  rw [qTaylorCoeff_nine_formula]
  exact norm_sub_sourceCenter_le_of_real_endpoint_bounds rfl
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.1.1
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.1.2

end GeneralCK.Certificates.E8ThetaParamCoeff9

end


