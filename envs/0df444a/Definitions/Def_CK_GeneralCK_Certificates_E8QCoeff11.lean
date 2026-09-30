-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff11
-- name    : CK_GeneralCK_Certificates_E8QCoeff11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:30:00.284473+00:00
-- url     : https://prove2.me/theorems/4ac6f5fd-6c8e-49d4-bf3d-d75ad71152bd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8QCoeff11` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8QCoeff11` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8QCoeff11` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8QCoeff11 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8QCoeff11.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff11_part01

namespace GeneralCK.Certificates.E8QCoeff11

open Filter
open E8AnalyticGerm E8AnalyticInverseRecurrence E8NormalizedCoeff5
open E8ParamCoeff9 E8ThetaParamCoeff5 E8ThetaParamCoeff7 E8ThetaParamCoeff9
open E8ThetaParamCoeff11 E8ComposeCoeff11 E8LowOrderThetaCoefficients
open E8HigherRationalTrace E8HigherSourceBoxBridge E8AnalyticCoefficientBoxes

theorem inverseStep_eleven_formula :
    inverseStep thetaTaylorCoeff qTaylorCoeff 11 = (q11Formula (Real.log 2) : ℂ) := by
  rw [← qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 11)]
  exact qTaylorCoeff_eleven_formula

theorem qTaylorCoeff_eleven_in_sourceBox :
    ‖qTaylorCoeff 11 - (sourceCenter 11 : ℂ)‖ ≤ (sourceHalfWidth 11 : ℝ) := by
  rw [qTaylorCoeff_eleven_formula]
  exact norm_sub_sourceCenter_le_of_real_endpoint_bounds rfl
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.2.1.1
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.2.1.2

end GeneralCK.Certificates.E8QCoeff11


