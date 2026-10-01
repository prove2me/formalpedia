-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree7_v2
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactDegree7_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:32:43.928485+00:00
-- url     : https://prove2.me/theorems/f668f01f-3dc3-48cf-b034-2de4340ce4e5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactDegree7 (v2)` (transplant)
-- statement:
--   Platform version of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactDegree7 (v2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). Every theorem statement is exactly the source's (`coeffAt productData i j = coeffAt kData i j`, exact rational polynomial-coefficient identities). The only change is the proof method: each identity is checked by kernel evaluation (`decide +kernel`) instead of the source's `norm_num [...]` unfolding. The `norm_num` proofs produce very large proof terms (about 100 MB of compiled output per handful of theorems), so a module importing all degrees exceeds the platform's time limit. Project imports are redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactDegree7 with kernel-decided proofs (browse copy: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactDegree7.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem coeff_0_7 : coeffAt productData 0 7 = coeffAt kData 0 7 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_1_6 : coeffAt productData 1 6 = coeffAt kData 1 6 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_2_5 : coeffAt productData 2 5 = coeffAt kData 2 5 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_3_4 : coeffAt productData 3 4 = coeffAt kData 3 4 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_4_3 : coeffAt productData 4 3 = coeffAt kData 4 3 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_5_2 : coeffAt productData 5 2 = coeffAt kData 5 2 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_6_1 : coeffAt productData 6 1 = coeffAt kData 6 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_7_0 : coeffAt productData 7 0 = coeffAt kData 7 0 := by decide +kernel

end GeneralCK.Certificates.E8OriginSourceKExactReplay


