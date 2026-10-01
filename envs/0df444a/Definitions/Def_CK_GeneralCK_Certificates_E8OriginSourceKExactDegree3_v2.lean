-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree3_v2
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactDegree3_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:17:52.960068+00:00
-- url     : https://prove2.me/theorems/f469530c-f4ee-43c6-b0f3-cf1da4ccb5f6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactDegree3 (v2)` (transplant)
-- statement:
--   Platform version of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactDegree3 (v2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). Every theorem statement is exactly the source's (`coeffAt productData i j = coeffAt kData i j`, exact rational polynomial-coefficient identities). The only change is the proof method: each identity is checked by kernel evaluation (`decide +kernel`) instead of the source's `norm_num [...]` unfolding. The `norm_num` proofs produce very large proof terms (about 100 MB of compiled output per handful of theorems), so a module importing all degrees exceeds the platform's time limit. Project imports are redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactDegree3 with kernel-decided proofs (browse copy: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactDegree3.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem coeff_0_3 : coeffAt productData 0 3 = coeffAt kData 0 3 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_1_2 : coeffAt productData 1 2 = coeffAt kData 1 2 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_2_1 : coeffAt productData 2 1 = coeffAt kData 2 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_3_0 : coeffAt productData 3 0 = coeffAt kData 3 0 := by decide +kernel

end GeneralCK.Certificates.E8OriginSourceKExactReplay


