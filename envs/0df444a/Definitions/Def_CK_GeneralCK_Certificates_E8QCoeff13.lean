-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff13
-- name    : CK_GeneralCK_Certificates_E8QCoeff13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:36:17.629167+00:00
-- url     : https://prove2.me/theorems/5a1f8b9d-a149-405c-bc91-41b7572cac26
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8QCoeff13` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8QCoeff13` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8QCoeff13` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8QCoeff13 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8QCoeff13.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaParamCoeff13
import Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff11

-- ===== source module GeneralCK.Certificates.E8QCoeff13 =====
section

namespace GeneralCK.Certificates.E8QCoeff13

open Filter
open E8AnalyticGerm E8AnalyticInverseRecurrence E8NormalizedCoeff5
open E8ParamCoeff9 E8ThetaParamCoeff5 E8ThetaParamCoeff7 E8ThetaParamCoeff9
open E8ThetaParamCoeff11 E8ThetaParamCoeff13 E8QCoeff11
open E8ComposeCoeff13 E8LowOrderThetaCoefficients
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
private theorem clogTwo_ne : Complex.log (2 : ℂ) ≠ 0 := by
  rw [clogTwo_eq]
  exact logTwo_ne

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

set_option maxHeartbeats 0 in
private theorem lower_thirteen_identity (L : ℂ) (hL : L ≠ 0) :
    tq3 L*(3*qq1 L^2*qq11 L + 6*qq1 L*qq3 L*qq9 L +
      6*qq1 L*qq5 L*qq7 L + 3*qq3 L^2*qq7 L + 3*qq3 L*qq5 L^2) +
    tq5 L*(5*qq1 L^4*qq9 L + 20*qq1 L^3*qq3 L*qq7 L +
      10*qq1 L^3*qq5 L^2 + 30*qq1 L^2*qq3 L^2*qq5 L + 5*qq1 L*qq3 L^4) +
    tq7 L*(7*qq1 L^6*qq7 L + 42*qq1 L^5*qq3 L*qq5 L +
      35*qq1 L^4*qq3 L^3) +
    tq9 L*(9*qq1 L^8*qq5 L + 36*qq1 L^7*qq3 L^2) +
    tq11 L*(11*qq1 L^10*qq3 L) + tq13 L*qq1 L^13 =
      -tq1 L*qq13 L := by
  simp [tq1, tq3, tq5, tq7, tq9, tq11, tq13, qq1, qq3, qq5, qq7, qq9,
    qq11, qq13]
  field_simp [hL]
  ring

set_option maxHeartbeats 0 in
theorem qTaylorCoeff_thirteen_formula :
    qTaylorCoeff 13 = (q13Formula (Real.log 2) : ℂ) := by
  have hc := composeCoeff_theta_q 13
  rw [composeCoeff_thirteen_odd thetaTaylorCoeff qTaylorCoeff
    (thetaTaylorCoeff_even 2 (by decide)) (thetaTaylorCoeff_even 4 (by decide))
    (thetaTaylorCoeff_even 6 (by decide)) (thetaTaylorCoeff_even 8 (by decide))
    (thetaTaylorCoeff_even 10 (by decide))
    qTaylorCoeff_zero (qTaylorCoeff_eq_zero_of_even (by decide : Even 2))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 4))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 6))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 8))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 10))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 12))] at hc
  let L : ℂ := Real.log 2
  have ht1 : thetaTaylorCoeff 1 = tq1 L := thetaTaylorCoeff_one
  have ht3 : thetaTaylorCoeff 3 = tq3 L := thetaTaylorCoeff_three
  have ht5 : thetaTaylorCoeff 5 = tq5 L := thetaTaylorCoeff_five
  have ht7 : thetaTaylorCoeff 7 = tq7 L := thetaTaylorCoeff_seven
  have ht9 : thetaTaylorCoeff 9 = tq9 L := thetaTaylorCoeff_nine
  have ht11 : thetaTaylorCoeff 11 = tq11 L := thetaTaylorCoeff_eleven
  have ht13 : thetaTaylorCoeff 13 = tq13 L := thetaTaylorCoeff_thirteen
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
  rw [ht1, ht3, ht5, ht7, ht9, ht11, ht13, hq1, hq3, hq5, hq7, hq9,
    hq11] at hc
  norm_num [targetCoeff] at hc
  simp only [add_assoc] at hc
  have hL : L ≠ 0 := by simpa [L] using logTwo_ne
  change qTaylorCoeff 13 = ((q13Formula (Real.log 2) : ℝ) : ℂ)
  rw [q13Formula]
  push_cast
  change qTaylorCoeff 13 = qq13 (Real.log 2 : ℂ)
  have hlow := lower_thirteen_identity L hL
  simp only [add_assoc] at hlow
  rw [hlow] at hc
  unfold tq1 at hc
  change qTaylorCoeff 13 = qq13 L
  field_simp [hL] at hc
  linear_combination (1 / 8) * hc

theorem inverseStep_thirteen_formula :
    inverseStep thetaTaylorCoeff qTaylorCoeff 13 = (q13Formula (Real.log 2) : ℂ) := by
  rw [← qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 13)]
  exact qTaylorCoeff_thirteen_formula

theorem qTaylorCoeff_thirteen_in_sourceBox :
    ‖qTaylorCoeff 13 - (sourceCenter 13 : ℂ)‖ ≤ (sourceHalfWidth 13 : ℝ) := by
  rw [qTaylorCoeff_thirteen_formula]
  exact norm_sub_sourceCenter_le_of_real_endpoint_bounds rfl
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.2.2.1.1
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.2.2.1.2

end GeneralCK.Certificates.E8QCoeff13

end


