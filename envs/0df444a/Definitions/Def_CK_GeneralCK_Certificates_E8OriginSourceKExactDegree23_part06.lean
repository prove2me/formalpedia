-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree23_part06
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactDegree23_part06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:12:16.815921+00:00
-- url     : https://prove2.me/theorems/cdaad23d-0478-4e3c-842b-3fa813571724
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactDegree23 (part 7 of 8)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactDegree23 (part 7 of 8)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKExactDegree23 (part 7 of 8)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactDegree23 (part 7 of 8) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactDegree23 (part 7 of 8).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree23_part05

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
theorem coeff_18_5 : coeffAt productData 18 5 = coeffAt kData 18 5 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_19_4 : coeffAt productData 19 4 = coeffAt kData 19 4 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_20_3 : coeffAt productData 20 3 = coeffAt kData 20 3 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]


end GeneralCK.Certificates.E8OriginSourceKExactReplay


