-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKResidualLower_q01
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKResidualLower_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:00:22.031463+00:00
-- url     : https://prove2.me/theorems/d58f947f-64aa-4b4c-ad04-bf85343ecf83
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKResidualLower (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKResidualLower (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKResidualLower (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKResidualLower (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKResidualLower (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKResidualLower_q00

namespace GeneralCK.Certificates.E8OriginSourceKResidualLower
open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay
open E8OriginSourceKExactAssembly
open E8OriginRemainder
set_option maxRecDepth 100000
theorem residual_negative_coefficients :
    coefficientsNonpositive (negativePart residualData) = true := by
  norm_num [coefficientsNonpositive, negativePart, residualData]

theorem residual_degrees :
    degreesAtLeastThree (negativePart residualData) = true := by
  norm_num [degreesAtLeastThree, negativePart, residualData]

def aggregate : Rat := (101643953669287839100007660148833103635498326613427815161637556586939977457363062498781951182788104584861073501658040307577304961649076350048421 / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)

end GeneralCK.Certificates.E8OriginSourceKResidualLower


