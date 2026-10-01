-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree19_v2
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactDegree19_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:11:55.831683+00:00
-- url     : https://prove2.me/theorems/66efe276-9c9b-47ca-b2d6-da171946d0f1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactDegree19 (v2)` (transplant)
-- statement:
--   Platform version of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactDegree19 (v2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). Every theorem statement is exactly the source's (`coeffAt productData i j = coeffAt kData i j`, exact rational polynomial-coefficient identities). The only change is the proof method: each identity is checked by kernel evaluation (`decide +kernel`) instead of the source's `norm_num [...]` unfolding. The `norm_num` proofs produce very large proof terms (about 100 MB of compiled output per handful of theorems), so a module importing all degrees exceeds the platform's time limit. Project imports are redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactDegree19 with kernel-decided proofs (browse copy: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactDegree19.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem coeff_0_19 : coeffAt productData 0 19 = coeffAt kData 0 19 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_1_18 : coeffAt productData 1 18 = coeffAt kData 1 18 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_2_17 : coeffAt productData 2 17 = coeffAt kData 2 17 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_3_16 : coeffAt productData 3 16 = coeffAt kData 3 16 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_4_15 : coeffAt productData 4 15 = coeffAt kData 4 15 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_5_14 : coeffAt productData 5 14 = coeffAt kData 5 14 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_6_13 : coeffAt productData 6 13 = coeffAt kData 6 13 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_7_12 : coeffAt productData 7 12 = coeffAt kData 7 12 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_8_11 : coeffAt productData 8 11 = coeffAt kData 8 11 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_9_10 : coeffAt productData 9 10 = coeffAt kData 9 10 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_10_9 : coeffAt productData 10 9 = coeffAt kData 10 9 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_11_8 : coeffAt productData 11 8 = coeffAt kData 11 8 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_12_7 : coeffAt productData 12 7 = coeffAt kData 12 7 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_13_6 : coeffAt productData 13 6 = coeffAt kData 13 6 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_14_5 : coeffAt productData 14 5 = coeffAt kData 14 5 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_15_4 : coeffAt productData 15 4 = coeffAt kData 15 4 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_16_3 : coeffAt productData 16 3 = coeffAt kData 16 3 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_17_2 : coeffAt productData 17 2 = coeffAt kData 17 2 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_18_1 : coeffAt productData 18 1 = coeffAt kData 18 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_19_0 : coeffAt productData 19 0 = coeffAt kData 19 0 := by decide +kernel

end GeneralCK.Certificates.E8OriginSourceKExactReplay


