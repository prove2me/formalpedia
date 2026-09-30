-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff11_part01
-- name    : CK_GeneralCK_Certificates_E8QCoeff11_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:59:03.496233+00:00
-- url     : https://prove2.me/theorems/ea983ad5-9ee8-4f86-9b4e-2b72e5ee9585
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8QCoeff11 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8QCoeff11 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8QCoeff11 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8QCoeff11 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8QCoeff11 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff11_part01_q100

namespace GeneralCK.Certificates.E8QCoeff11
open Filter
open E8AnalyticGerm E8AnalyticInverseRecurrence E8NormalizedCoeff5
open E8ParamCoeff9 E8ThetaParamCoeff5 E8ThetaParamCoeff7 E8ThetaParamCoeff9
open E8ThetaParamCoeff11 E8ComposeCoeff11 E8LowOrderThetaCoefficients
open E8HigherRationalTrace E8HigherSourceBoxBridge E8AnalyticCoefficientBoxes
set_option maxHeartbeats 0 in
theorem qTaylorCoeff_eleven_formula :
    qTaylorCoeff 11 = (q11Formula (Real.log 2) : ℂ) := by
  have hc := composeCoeff_theta_q 11
  rw [composeCoeff_eleven_odd thetaTaylorCoeff qTaylorCoeff
    (thetaTaylorCoeff_even_priv 2 (by decide)) (thetaTaylorCoeff_even_priv 4 (by decide))
    (thetaTaylorCoeff_even_priv 6 (by decide)) (thetaTaylorCoeff_even_priv 8 (by decide))
    qTaylorCoeff_zero (qTaylorCoeff_eq_zero_of_even (by decide : Even 2))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 4))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 6))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 8))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 10))] at hc
  rw [thetaTaylorCoeff_one, thetaTaylorCoeff_three, thetaTaylorCoeff_five,
    thetaTaylorCoeff_seven, thetaTaylorCoeff_nine, thetaTaylorCoeff_eleven,
    qTaylorCoeff_one, qTaylorCoeff_three_formula, qTaylorCoeff_five_formula,
    qTaylorCoeff_seven_formula, qTaylorCoeff_nine_formula] at hc
  rw [q7Formula, q9Formula] at hc
  push_cast at hc
  norm_num [targetCoeff] at hc
  rw [clogTwo_eq_priv] at hc
  change qTaylorCoeff 11 = ((q11Formula (Real.log 2) : ℝ) : ℂ)
  rw [q11Formula]
  push_cast
  -- same algebra as the source, with `L = log 2` kept opaque: clear denominators with `field_simp`
  -- and close the polynomial identity with `ring` (the source's AC-`simp` step takes ~440 s)
  have hL0 := logTwo_ne_priv
  generalize ((Real.log 2 : ℝ) : ℂ) = L at hc hL0 ⊢
  linear_combination (norm := skip) (L / 8) * hc
  field_simp
  ring


end GeneralCK.Certificates.E8QCoeff11


