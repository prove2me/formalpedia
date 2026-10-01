-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree9_part02
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactDegree9_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T18:11:13.349986+00:00
-- url     : https://prove2.me/theorems/74cc8085-d484-41ed-9ce1-713ece22db5a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactDegree9 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactDegree9 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKExactDegree9 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactDegree9 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactDegree9 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree9_part01

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
theorem coeff_6_3 : coeffAt productData 6 3 = coeffAt kData 6 3 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_7_2 : coeffAt productData 7 2 = coeffAt kData 7 2 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_8_1 : coeffAt productData 8 1 = coeffAt kData 8 1 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]


end GeneralCK.Certificates.E8OriginSourceKExactReplay


