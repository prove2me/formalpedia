-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ThetaParamCoeff15
-- name    : CK_GeneralCK_Certificates_E8ThetaParamCoeff15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:22:58.162271+00:00
-- url     : https://prove2.me/theorems/e965cda7-1cbd-4a65-98d7-5c7c0c40e32b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ThetaParamCoeff15` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ThetaParamCoeff15` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ThetaParamCoeff15` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ThetaParamCoeff15 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ThetaParamCoeff15.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ParamCoeff15
import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaParamCoeff13
import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaParamCoeff9
import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaParamCoeff11
import Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff15

-- ===== source module GeneralCK.Certificates.E8ThetaParamCoeff15 =====
section

namespace GeneralCK.Certificates.E8ThetaParamCoeff15

open Filter
open E8AnalyticGerm Reflection.ComplexEntropy Reflection.ComplexContactFactor
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8NormalizedCoeff7
open E8ElementaryCoeff5 E8ElementaryCoeff7 E8ElementaryCoeff9 E8ElementaryCoeff11
open E8ElementaryCoeff13 E8ElementaryCoeff15
open E8ParamCoeff5 E8ParamCoeff7 E8ParamCoeff9 E8ParamCoeff11 E8ParamCoeff13 E8ParamCoeff15
open E8ThetaParamCoeff5 E8ThetaParamCoeff7 E8ThetaParamCoeff9 E8ThetaParamCoeff11 E8ThetaParamCoeff13
open E8ComposeCoeff15
open E8LowOrderThetaCoefficients
open E8HigherRationalTrace E8HigherSourceBoxBridge E8AnalyticCoefficientBoxes

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

theorem coeff_denom_fourteen : coeff thetaDenom 14 = -1 / 84 := by
  have h := coeff_mul (fun z : ℂ => 1 - z ^ 2) biasBExt
    (analyticAt_const.sub (analyticAt_id.pow 2)) analyticAt_biasBExt 14
  change coeff thetaDenom 14 = _ at h
  rw [h]
  norm_num [Finset.sum_range_succ, coeff_one_sub_sq, coeff_biasBExt_fourteen,
    coeff_biasBExt_twelve,
    coeff_biasBExt_ten, coeff_biasBExt_eight, coeff_biasBExt_six, coeff_biasBExt_four,
    coeff_even_zero_of_odd biasBExt_neg]

private theorem coeff_num_fifteen : coeff (fun z : ℂ => z * entropyExt z) 15 = -1 / 182 := by
  have h := coeff_mul id entropyExt analyticAt_id
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num)) 15
  change coeff (fun z : ℂ => z * entropyExt z) 15 = _ at h
  rw [h]
  have hid (n : ℕ) : coeff id n = if n = 1 then 1 else 0 := by
    rcases n with (_ | n)
    · simp [coeff]
    · rcases n with (_ | n)
      · simp [coeff, iteratedDeriv_id]
      · simp [coeff, iteratedDeriv_id]
  norm_num [Finset.sum_range_succ, hid, coeff_entropyExt_fourteen]

private theorem coeff_thetaRatio_even (n : ℕ) (hn : Even n) : coeff thetaRatio n = 0 := by
  apply coeff_odd_zero_of_even _ hn
  intro z
  simp [thetaRatio, thetaDenom, entropyExt_neg, biasBExt_neg]
  ring

theorem coeff_thetaRatio_fifteen : coeff thetaRatio 15 =
    1 - 88069 / (45045*(Real.log 2 : ℂ)) + 57481 / (27720*(Real.log 2 : ℂ)^2) -
      4247 / (2520*(Real.log 2 : ℂ)^3) + 1375 / (1344*(Real.log 2 : ℂ)^4) -
      211 / (480*(Real.log 2 : ℂ)^5) + 23 / (192*(Real.log 2 : ℂ)^6) -
      1 / (64*(Real.log 2 : ℂ)^7) := by
  have hp := coeff_mul thetaRatio thetaDenom analyticAt_thetaRatio analyticAt_thetaDenom 15
  have he := coeff_congr eventually_ratio_mul_denom 15
  change coeff (fun z => thetaRatio z * thetaDenom z) 15 = _ at hp
  rw [hp] at he
  norm_num [Finset.sum_range_succ, coeff_denom_zero, coeff_denom_two,
    coeff_denom_four, coeff_denom_six, coeff_denom_eight, coeff_denom_ten,
    coeff_denom_twelve, coeff_denom_fourteen,
    coeff_denom_odd, coeff_thetaRatio_one, coeff_thetaRatio_three,
    coeff_thetaRatio_five, coeff_thetaRatio_seven, coeff_thetaRatio_nine,
    coeff_thetaRatio_eleven, coeff_thetaRatio_thirteen,
    coeff_thetaRatio_even, coeff_num_fifteen] at he
  have hd3 := coeff_denom_odd 3 (by decide)
  have hd5 := coeff_denom_odd 5 (by decide)
  have hd7 := coeff_denom_odd 7 (by decide)
  have hd9 := coeff_denom_odd 9 (by decide)
  have hd11 := coeff_denom_odd 11 (by decide)
  have hd13 := coeff_denom_odd 13 (by decide)
  have hd15 := coeff_denom_odd 15 (by decide)
  simp only [hd3, hd5, hd7, hd9, hd11, hd13, hd15, mul_zero] at he
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
  have hi5 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^6 =
      (Real.log 2 : ℂ)⁻¹^5 := by field_simp [logTwo_ne]
  have hi6 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^7 =
      (Real.log 2 : ℂ)⁻¹^6 := by field_simp [logTwo_ne]
  rw [hi0, hi1, hi2, hi3, hi4, hi5] at he
  rw [hi6]
  linear_combination he + (88069 / 45045) * hi0 - (57481 / 27720) * hi1 +
    (4247 / 2520) * hi2 - (1375 / 1344) * hi3 + (211 / 480) * hi4 -
    (23 / 192) * hi5

private theorem thetaParam_eq : thetaParam = fun z : ℂ =>
    (2 / (Real.log 2 : ℂ)) * (atanhExt z + thetaRatio z) := by
  funext z
  rfl

theorem coeff_thetaParam_fifteen : coeff thetaParam 15 =
    32 / (15*(Real.log 2 : ℂ)) - 176138 / (45045*(Real.log 2 : ℂ)^2) +
      57481 / (13860*(Real.log 2 : ℂ)^3) - 4247 / (1260*(Real.log 2 : ℂ)^4) +
      1375 / (672*(Real.log 2 : ℂ)^5) - 211 / (240*(Real.log 2 : ℂ)^6) +
      23 / (96*(Real.log 2 : ℂ)^7) - 1 / (32*(Real.log 2 : ℂ)^8) := by
  rw [thetaParam_eq, coeff_const_mul]
  have hs := coeff_add atanhExt thetaRatio analyticAt_atanhExt analyticAt_thetaRatio 15
  change coeff (fun z => atanhExt z + thetaRatio z) 15 = _ at hs
  rw [hs, coeff_atanhExt_fifteen, coeff_thetaRatio_fifteen]
  ring_nf

private theorem coeff_thetaParam_even (n : ℕ) (hn : Even n) : coeff thetaParam n = 0 :=
  coeff_odd_zero_of_even thetaParam_neg hn

theorem thetaTaylorCoeff_fifteen : thetaTaylorCoeff 15 =
    8192 * (17297280*(Real.log 2 : ℂ)^7 - 170907120*(Real.log 2 : ℂ)^6 +
      767968656*(Real.log 2 : ℂ)^5 - 2049261214*(Real.log 2 : ℂ)^4 +
      3533810280*(Real.log 2 : ℂ)^3 - 3967923960*(Real.log 2 : ℂ)^2 +
      2705402700*(Real.log 2 : ℂ) - 869593725) /
      (2027025*(Real.log 2 : ℂ)^8) := by
  change coeff thetaGerm 15 = _
  have hc := coeff_comp thetaParam xBiasGerm analyticAt_thetaParam analyticAt_xBiasGerm
    xBiasGerm_zero 15
  change coeff thetaGerm 15 = _ at hc
  rw [hc, composeCoeff_fifteen_odd (coeff thetaParam) (coeff xBiasGerm)
    (coeff_thetaParam_even 2 (by decide)) (coeff_thetaParam_even 4 (by decide))
    (coeff_thetaParam_even 6 (by decide)) (coeff_thetaParam_even 8 (by decide))
    (coeff_thetaParam_even 10 (by decide))
    (coeff_thetaParam_even 12 (by decide))
    (by simp [coeff, xBiasGerm_zero]) coeff_xBiasGerm_two coeff_xBiasGerm_four
    coeff_xBiasGerm_six (coeff_xBiasGerm_even (by decide : Even 8))
    (coeff_xBiasGerm_even (by decide : Even 10))
    (coeff_xBiasGerm_even (by decide : Even 12))
    (coeff_xBiasGerm_even (by decide : Even 14)), coeff_thetaParam_one,
    coeff_thetaParam_three, coeff_thetaParam_five, coeff_thetaParam_seven,
    coeff_thetaParam_nine, coeff_thetaParam_eleven, coeff_thetaParam_thirteen,
    coeff_thetaParam_fifteen,
    coeff_xBiasGerm_one,
    coeff_xBiasGerm_three, coeff_xBiasGerm_five, coeff_xBiasGerm_seven,
    coeff_xBiasGerm_nine, coeff_xBiasGerm_eleven, coeff_xBiasGerm_thirteen,
    coeff_xBiasGerm_fifteen]
  field_simp [logTwo_ne]
  ring

end GeneralCK.Certificates.E8ThetaParamCoeff15

end


