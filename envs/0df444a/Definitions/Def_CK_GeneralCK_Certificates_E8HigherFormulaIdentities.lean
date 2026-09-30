-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8HigherFormulaIdentities
-- name    : CK_GeneralCK_Certificates_E8HigherFormulaIdentities
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:42:52.378077+00:00
-- url     : https://prove2.me/theorems/bbf2e80d-020c-4952-8375-cfde5bd36c13
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8HigherFormulaIdentities` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8HigherFormulaIdentities` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8HigherFormulaIdentities` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8HigherFormulaIdentities (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8HigherFormulaIdentities.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff7
import Definitions.Def_CK_GeneralCK_Certificates_E8HigherRationalTrace

-- ===== source module GeneralCK.Certificates.E8HigherFormulaIdentities =====
section

namespace GeneralCK.Certificates.E8HigherFormulaIdentities

open E8AnalyticGerm E8AnalyticInverseRecurrence E8HigherSourceBoxBridge
open E8HigherRationalTrace E8ThetaParamCoeff5 E8LowOrderThetaCoefficients
open E8ComposeCoeff7

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
private theorem clogTwo_eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.natCast_log (n := 2)).symm
private theorem clogTwo_ne : Complex.log (2 : ℂ) ≠ 0 := by
  rw [clogTwo_eq]
  exact logTwo_ne
structure HigherThetaFormulaIdentities : Prop where
  h7 : thetaTaylorCoeff 7 =
    256 * (120*(Real.log 2 : ℂ)^3 - 518*(Real.log 2 : ℂ)^2 +
      840*(Real.log 2 : ℂ) - 525) / (105*(Real.log 2 : ℂ)^4)
  h9 : thetaTaylorCoeff 9 =
    256 * (280*(Real.log 2 : ℂ)^4 - 1599*(Real.log 2 : ℂ)^3 +
      3766*(Real.log 2 : ℂ)^2 - 4410*(Real.log 2 : ℂ) + 2205) /
      (63*(Real.log 2 : ℂ)^5)
  h11 : thetaTaylorCoeff 11 =
    512 * (10080*(Real.log 2 : ℂ)^5 - 71588*(Real.log 2 : ℂ)^4 +
      220110*(Real.log 2 : ℂ)^3 - 370755*(Real.log 2 : ℂ)^2 +
      346500*(Real.log 2 : ℂ) - 145530) / (1155*(Real.log 2 : ℂ)^6)
  h13 : thetaTaylorCoeff 13 =
    512 * (3326400*(Real.log 2 : ℂ)^6 - 28246920*(Real.log 2 : ℂ)^5 +
      106954848*(Real.log 2 : ℂ)^4 - 233291630*(Real.log 2 : ℂ)^3 +
      312161850*(Real.log 2 : ℂ)^2 - 245270025*(Real.log 2 : ℂ) + 89189100) /
      (96525*(Real.log 2 : ℂ)^7)
  h15 : thetaTaylorCoeff 15 =
    8192 * (17297280*(Real.log 2 : ℂ)^7 - 170907120*(Real.log 2 : ℂ)^6 +
      767968656*(Real.log 2 : ℂ)^5 - 2049261214*(Real.log 2 : ℂ)^4 +
      3533810280*(Real.log 2 : ℂ)^3 - 3967923960*(Real.log 2 : ℂ)^2 +
      2705402700*(Real.log 2 : ℂ) - 869593725) / (2027025*(Real.log 2 : ℂ)^8)

theorem qTaylorCoeff_seven_formula_of_theta
    (h7 : thetaTaylorCoeff 7 =
      256 * (120*(Real.log 2 : ℂ)^3 - 518*(Real.log 2 : ℂ)^2 +
        840*(Real.log 2 : ℂ) - 525) / (105*(Real.log 2 : ℂ)^4)) :
    qTaylorCoeff 7 = (q7Formula (Real.log 2) : ℂ) := by
  have hc := composeCoeff_theta_q 7
  rw [composeCoeff_seven_odd thetaTaylorCoeff qTaylorCoeff qTaylorCoeff_zero
    (qTaylorCoeff_eq_zero_of_even (show Even 2 by decide))
    (qTaylorCoeff_eq_zero_of_even (show Even 4 by decide))
    (qTaylorCoeff_eq_zero_of_even (show Even 6 by decide))] at hc
  rw [thetaTaylorCoeff_one, thetaTaylorCoeff_three, thetaTaylorCoeff_five, h7,
    qTaylorCoeff_one, qTaylorCoeff_three_formula, qTaylorCoeff_five_formula] at hc
  norm_num [targetCoeff] at hc
  rw [clogTwo_eq] at hc
  change qTaylorCoeff 7 = ((q7Formula (Real.log 2) : ℝ) : ℂ)
  rw [q7Formula]
  push_cast
  have hc' := congrArg (fun z => z * (Real.log 2 : ℂ)) hc
  field_simp [logTwo_ne] at hc' ⊢
  simp [mul_assoc, mul_left_comm, mul_comm, logTwo_ne] at hc' ⊢
  rcases hc' with (hzero | hc') | hzero
  · exact (clogTwo_ne hzero).elim
  · ring_nf at hc' ⊢
    linear_combination (1 / 1546188226560) * hc'
  · exact (clogTwo_ne hzero).elim

theorem inverseStep_seven_formula_of_theta (h : HigherThetaFormulaIdentities) :
    inverseStep thetaTaylorCoeff qTaylorCoeff 7 =
      (q7Formula (Real.log 2) : ℂ) := by
  rw [← qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 7)]
  exact qTaylorCoeff_seven_formula_of_theta h.h7

end GeneralCK.Certificates.E8HigherFormulaIdentities


end


