-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff15
-- name    : CK_GeneralCK_Certificates_E8QCoeff15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:42:47.203713+00:00
-- url     : https://prove2.me/theorems/91b39031-ff10-42fa-bb69-9c6e301f698a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8QCoeff15` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8QCoeff15` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8QCoeff15` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8QCoeff15 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8QCoeff15.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaParamCoeff15
import Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff13

-- ===== source module GeneralCK.Certificates.E8QCoeff15 =====
section

namespace GeneralCK.Certificates.E8QCoeff15

open Filter
open E8AnalyticGerm E8AnalyticInverseRecurrence E8NormalizedCoeff5
open E8ParamCoeff9
open E8ThetaParamCoeff5 E8ThetaParamCoeff7 E8ThetaParamCoeff9
open E8ThetaParamCoeff11 E8ThetaParamCoeff13 E8ThetaParamCoeff15
open E8QCoeff11 E8QCoeff13 E8ComposeCoeff15 E8LowOrderThetaCoefficients
open E8HigherRationalTrace E8HigherSourceBoxBridge E8AnalyticCoefficientBoxes

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

private theorem thetaTaylorCoeff_even (n : ℕ) (hn : Even n) :
    thetaTaylorCoeff n = 0 := by
  have heq : (fun z : ℂ => thetaGerm (-z)) =ᶠ[nhds 0]
      (fun z => -thetaGerm z) := by
    filter_upwards [eventually_xBiasGerm_neg] with z hz
    simp only [thetaGerm, hz, thetaParam_neg]
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at hd
  simp only [neg_zero, Even.neg_one_pow hn, one_smul] at hd
  unfold thetaTaylorCoeff
  have hz : iteratedDeriv n thetaGerm 0 = 0 := by
    linear_combination (1 / 2 : ℂ) * hd
  simp [hz]

private theorem clogTwo_eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.natCast_log (n := 2)).symm

private noncomputable def tq1 (L : ℂ) := 8 / L
private noncomputable def tq3 (L : ℂ) := 64 / (3*L) - 32 / L^2
private noncomputable def tq5 (L : ℂ) := 384 / (5*L) - 224 / L^2 + 192 / L^3
private noncomputable def tq7 (L : ℂ) :=
  256*(120*L^3-518*L^2+840*L-525)/(105*L^4)
private noncomputable def tq9 (L : ℂ) :=
  256*(280*L^4-1599*L^3+3766*L^2-4410*L+2205)/(63*L^5)
private noncomputable def tq11 (L : ℂ) :=
  512*(10080*L^5-71588*L^4+220110*L^3-370755*L^2+346500*L-145530)/(1155*L^6)
private noncomputable def tq13 (L : ℂ) :=
  512*(3326400*L^6-28246920*L^5+106954848*L^4-233291630*L^3+
    312161850*L^2-245270025*L+89189100)/(96525*L^7)
private noncomputable def tq15 (L : ℂ) :=
  8192*(17297280*L^7-170907120*L^6+767968656*L^5-2049261214*L^4+
    3533810280*L^3-3967923960*L^2+2705402700*L-869593725)/(2027025*L^8)
private noncomputable def qq1 (L : ℂ) := L/8
private noncomputable def qq3 (L : ℂ) := -L^2*(2*L-3)/384
private noncomputable def qq5 (L : ℂ) := L^3*(44*L^2-135*L+90)/122880
private noncomputable def qq7 (L : ℂ) :=
  -(L^4*(584*L^3-2730*L^2+3780*L-1575))/20643840
private noncomputable def qq9 (L : ℂ) :=
  L^5*(56768*L^4-358050*L^3+763875*L^2-661500*L+198450)/23781703680
private noncomputable def qq11 (L : ℂ) :=
  -(L^6*(4380256*L^5-34864236*L^4+101226510*L^3-135394875*L^2+
    84199500*L-19646550))/20927899238400
private noncomputable def qq13 (L : ℂ) :=
  L^7*(983051392*L^6-9463894440*L^5+34914199320*L^4-63733044375*L^3+
    61183722600*L^2-29499294825*L+5618913300)/52236036499046400
private noncomputable def qq15 (L : ℂ) :=
  -L^8*(37788392576*L^7-427290803472*L^6+1917356641200*L^5-
    4459512026970*L^4+5845031992800*L^3-4343647007700*L^2+
    1704403701000*L-273922023375)/21939135329599488000

set_option maxHeartbeats 0 in
private theorem lower_fifteen_identity (L : ℂ) (hL : L ≠ 0) :
    tq3 L*(3*qq1 L^2*qq13 L + 6*qq1 L*qq3 L*qq11 L +
      6*qq1 L*qq5 L*qq9 L + 3*qq1 L*qq7 L^2 + 3*qq3 L^2*qq9 L +
      6*qq3 L*qq5 L*qq7 L + qq5 L^3) +
    tq5 L*(5*qq1 L^4*qq11 L + 20*qq1 L^3*qq3 L*qq9 L +
      20*qq1 L^3*qq5 L*qq7 L + 30*qq1 L^2*qq3 L^2*qq7 L +
      30*qq1 L^2*qq3 L*qq5 L^2 + 20*qq1 L*qq3 L^3*qq5 L + qq3 L^5) +
    tq7 L*(7*qq1 L^6*qq9 L + 42*qq1 L^5*qq3 L*qq7 L +
      21*qq1 L^5*qq5 L^2 + 105*qq1 L^4*qq3 L^2*qq5 L +
      35*qq1 L^3*qq3 L^4) +
    tq9 L*(9*qq1 L^8*qq7 L + 72*qq1 L^7*qq3 L*qq5 L +
      84*qq1 L^6*qq3 L^3) +
    tq11 L*(11*qq1 L^10*qq5 L + 55*qq1 L^9*qq3 L^2) +
    tq13 L*(13*qq1 L^12*qq3 L) + tq15 L*qq1 L^15 = -tq1 L*qq15 L := by
  simp [tq1, tq3, tq5, tq7, tq9, tq11, tq13, tq15, qq1, qq3, qq5, qq7,
    qq9, qq11, qq13, qq15]
  field_simp [hL]
  ring

set_option maxHeartbeats 0 in
theorem qTaylorCoeff_fifteen_formula :
    qTaylorCoeff 15 = (q15Formula (Real.log 2) : ℂ) := by
  have hc := composeCoeff_theta_q 15
  rw [composeCoeff_fifteen_odd thetaTaylorCoeff qTaylorCoeff
    (thetaTaylorCoeff_even 2 (by decide)) (thetaTaylorCoeff_even 4 (by decide))
    (thetaTaylorCoeff_even 6 (by decide)) (thetaTaylorCoeff_even 8 (by decide))
    (thetaTaylorCoeff_even 10 (by decide)) (thetaTaylorCoeff_even 12 (by decide))
    qTaylorCoeff_zero (qTaylorCoeff_eq_zero_of_even (by decide : Even 2))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 4))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 6))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 8))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 10))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 12))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 14))] at hc
  let L : ℂ := Real.log 2
  have ht1 : thetaTaylorCoeff 1 = tq1 L := thetaTaylorCoeff_one
  have ht3 : thetaTaylorCoeff 3 = tq3 L := thetaTaylorCoeff_three
  have ht5 : thetaTaylorCoeff 5 = tq5 L := thetaTaylorCoeff_five
  have ht7 : thetaTaylorCoeff 7 = tq7 L := thetaTaylorCoeff_seven
  have ht9 : thetaTaylorCoeff 9 = tq9 L := thetaTaylorCoeff_nine
  have ht11 : thetaTaylorCoeff 11 = tq11 L := thetaTaylorCoeff_eleven
  have ht13 : thetaTaylorCoeff 13 = tq13 L := thetaTaylorCoeff_thirteen
  have ht15 : thetaTaylorCoeff 15 = tq15 L := thetaTaylorCoeff_fifteen
  have hq1 : qTaylorCoeff 1 = qq1 L := qTaylorCoeff_one
  have hq3 : qTaylorCoeff 3 = qq3 L := qTaylorCoeff_three_formula
  have hq5 : qTaylorCoeff 5 = qq5 L := qTaylorCoeff_five_formula
  have hq7 := qTaylorCoeff_seven_formula
  rw [q7Formula] at hq7
  push_cast at hq7
  norm_num [targetCoeff] at hq7
  rw [clogTwo_eq] at hq7
  change qTaylorCoeff 7 = qq7 L at hq7
  have hq9 := qTaylorCoeff_nine_formula
  rw [q9Formula] at hq9
  push_cast at hq9
  norm_num [targetCoeff] at hq9
  rw [clogTwo_eq] at hq9
  change qTaylorCoeff 9 = qq9 L at hq9
  have hq11 := qTaylorCoeff_eleven_formula
  rw [q11Formula] at hq11
  push_cast at hq11
  norm_num [targetCoeff] at hq11
  rw [clogTwo_eq] at hq11
  change qTaylorCoeff 11 = qq11 L at hq11
  have hq13 := qTaylorCoeff_thirteen_formula
  rw [q13Formula] at hq13
  push_cast at hq13
  norm_num [targetCoeff] at hq13
  rw [clogTwo_eq] at hq13
  change qTaylorCoeff 13 = qq13 L at hq13
  rw [ht1, ht3, ht5, ht7, ht9, ht11, ht13, ht15, hq1, hq3, hq5, hq7,
    hq9, hq11, hq13] at hc
  norm_num [targetCoeff] at hc
  simp only [add_assoc] at hc
  have hL : L ≠ 0 := by simpa [L] using logTwo_ne
  change qTaylorCoeff 15 = ((q15Formula (Real.log 2) : ℝ) : ℂ)
  rw [q15Formula]
  push_cast
  change qTaylorCoeff 15 = qq15 (Real.log 2 : ℂ)
  have hlow := lower_fifteen_identity L hL
  simp only [add_assoc] at hlow
  rw [hlow] at hc
  unfold tq1 at hc
  change qTaylorCoeff 15 = qq15 L
  field_simp [hL] at hc
  linear_combination (1 / 8) * hc

theorem inverseStep_fifteen_formula :
    inverseStep thetaTaylorCoeff qTaylorCoeff 15 = (q15Formula (Real.log 2) : ℂ) := by
  rw [← qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 15)]
  exact qTaylorCoeff_fifteen_formula

theorem qTaylorCoeff_fifteen_in_sourceBox :
    ‖qTaylorCoeff 15 - (sourceCenter 15 : ℂ)‖ ≤ (sourceHalfWidth 15 : ℝ) := by
  rw [qTaylorCoeff_fifteen_formula]
  exact norm_sub_sourceCenter_le_of_real_endpoint_bounds rfl
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.2.2.2.1
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.2.2.2.2

theorem higherThetaFormulaIdentities :
    E8HigherFormulaIdentities.HigherThetaFormulaIdentities :=
  ⟨thetaTaylorCoeff_seven, thetaTaylorCoeff_nine, thetaTaylorCoeff_eleven,
    thetaTaylorCoeff_thirteen, thetaTaylorCoeff_fifteen⟩

theorem higherInverseStepFormulaIdentities : HigherInverseStepFormulaIdentities :=
  ⟨E8ThetaParamCoeff7.inverseStep_seven_formula,
    E8ThetaParamCoeff9.inverseStep_nine_formula,
    E8QCoeff11.inverseStep_eleven_formula,
    E8QCoeff13.inverseStep_thirteen_formula,
    inverseStep_fifteen_formula⟩

noncomputable def higherInverseStepInRetainedBoxes : HigherInverseStepInRetainedBoxes :=
  retainedCertificate_of_formula_identities higherInverseStepFormulaIdentities

theorem higherOddQCoefficientsInSourceBoxes : HigherOddQCoefficientsInSourceBoxes := by
  have h := higher_source_boxes_of_retained_endpoint_checks
    higherInverseStepInRetainedBoxes
  exact ⟨E8ThetaParamCoeff5.qTaylorCoeff_three_in_sourceBox,
    E8ThetaParamCoeff5.qTaylorCoeff_five_in_sourceBox,
    h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem oddQCoefficientsInSourceBoxes : OddQCoefficientsInSourceBoxes :=
  higherOddQCoefficientsInSourceBoxes.toOdd

theorem exists_unconditional_source_center_remainder :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧
      (∀ z, qGerm z =
        (∑ n ∈ Finset.range 16, z ^ n * (sourceCenter n : ℂ)) +
        (∑ n ∈ Finset.range 16,
          z ^ n * (qTaylorCoeff n - (sourceCenter n : ℂ))) +
        z ^ 17 * r z) ∧
      (∀ z, ‖z‖ ≤ (E8OriginRemainder.radius : ℝ) →
        ‖∑ n ∈ Finset.range 16,
          z ^ n * (qTaylorCoeff n - (sourceCenter n : ℂ))‖ ≤
            (coefficientErrorBudget : ℝ)) :=
  exists_source_center_remainder higherOddQCoefficientsInSourceBoxes

end GeneralCK.Certificates.E8QCoeff15

end


