-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree25_v2
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactDegree25_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:39:23.618497+00:00
-- url     : https://prove2.me/theorems/79952a6c-231e-4ffe-a315-c847febbdfeb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactDegree25 (v2)` (transplant)
-- statement:
--   Platform version of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactDegree25 (v2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). Every theorem statement is exactly the source's (`coeffAt productData i j = coeffAt kData i j`, exact rational polynomial-coefficient identities). The only change is the proof method: each identity is checked by kernel evaluation (`decide +kernel`) instead of the source's `norm_num [...]` unfolding. The `norm_num` proofs produce very large proof terms (about 100 MB of compiled output per handful of theorems), so a module importing all degrees exceeds the platform's time limit. Project imports are redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactDegree25 with kernel-decided proofs (browse copy: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactDegree25.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem coeff_0_25 : coeffAt productData 0 25 = coeffAt kData 0 25 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_1_24 : coeffAt productData 1 24 = coeffAt kData 1 24 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_2_23 : coeffAt productData 2 23 = coeffAt kData 2 23 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_3_22 : coeffAt productData 3 22 = coeffAt kData 3 22 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_4_21 : coeffAt productData 4 21 = coeffAt kData 4 21 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_5_20 : coeffAt productData 5 20 = coeffAt kData 5 20 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_6_19 : coeffAt productData 6 19 = coeffAt kData 6 19 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_7_18 : coeffAt productData 7 18 = coeffAt kData 7 18 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_8_17 : coeffAt productData 8 17 = coeffAt kData 8 17 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_9_16 : coeffAt productData 9 16 = coeffAt kData 9 16 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_10_15 : coeffAt productData 10 15 = coeffAt kData 10 15 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_11_14 : coeffAt productData 11 14 = coeffAt kData 11 14 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_12_13 : coeffAt productData 12 13 = coeffAt kData 12 13 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_13_12 : coeffAt productData 13 12 = coeffAt kData 13 12 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_14_11 : coeffAt productData 14 11 = coeffAt kData 14 11 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_15_10 : coeffAt productData 15 10 = coeffAt kData 15 10 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_16_9 : coeffAt productData 16 9 = coeffAt kData 16 9 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_17_8 : coeffAt productData 17 8 = coeffAt kData 17 8 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_18_7 : coeffAt productData 18 7 = coeffAt kData 18 7 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_19_6 : coeffAt productData 19 6 = coeffAt kData 19 6 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_20_5 : coeffAt productData 20 5 = coeffAt kData 20 5 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_21_4 : coeffAt productData 21 4 = coeffAt kData 21 4 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_22_3 : coeffAt productData 22 3 = coeffAt kData 22 3 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_23_2 : coeffAt productData 23 2 = coeffAt kData 23 2 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_24_1 : coeffAt productData 24 1 = coeffAt kData 24 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_25_0 : coeffAt productData 25 0 = coeffAt kData 25 0 := by decide +kernel

end GeneralCK.Certificates.E8OriginSourceKExactReplay


