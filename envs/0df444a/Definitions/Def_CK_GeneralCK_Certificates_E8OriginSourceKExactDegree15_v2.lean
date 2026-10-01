-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree15_v2
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactDegree15_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:02:45.850996+00:00
-- url     : https://prove2.me/theorems/ee2c3ea8-98ed-453d-8167-d33ac9cdae41
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactDegree15 (v2)` (transplant)
-- statement:
--   Platform version of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactDegree15 (v2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). Every theorem statement is exactly the source's (`coeffAt productData i j = coeffAt kData i j`, exact rational polynomial-coefficient identities). The only change is the proof method: each identity is checked by kernel evaluation (`decide +kernel`) instead of the source's `norm_num [...]` unfolding. The `norm_num` proofs produce very large proof terms (about 100 MB of compiled output per handful of theorems), so a module importing all degrees exceeds the platform's time limit. Project imports are redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactDegree15 with kernel-decided proofs (browse copy: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactDegree15.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem coeff_0_15 : coeffAt productData 0 15 = coeffAt kData 0 15 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_1_14 : coeffAt productData 1 14 = coeffAt kData 1 14 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_2_13 : coeffAt productData 2 13 = coeffAt kData 2 13 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_3_12 : coeffAt productData 3 12 = coeffAt kData 3 12 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_4_11 : coeffAt productData 4 11 = coeffAt kData 4 11 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_5_10 : coeffAt productData 5 10 = coeffAt kData 5 10 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_6_9 : coeffAt productData 6 9 = coeffAt kData 6 9 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_7_8 : coeffAt productData 7 8 = coeffAt kData 7 8 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_8_7 : coeffAt productData 8 7 = coeffAt kData 8 7 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_9_6 : coeffAt productData 9 6 = coeffAt kData 9 6 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_10_5 : coeffAt productData 10 5 = coeffAt kData 10 5 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_11_4 : coeffAt productData 11 4 = coeffAt kData 11 4 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_12_3 : coeffAt productData 12 3 = coeffAt kData 12 3 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_13_2 : coeffAt productData 13 2 = coeffAt kData 13 2 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_14_1 : coeffAt productData 14 1 = coeffAt kData 14 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_15_0 : coeffAt productData 15 0 = coeffAt kData 15 0 := by decide +kernel

end GeneralCK.Certificates.E8OriginSourceKExactReplay


