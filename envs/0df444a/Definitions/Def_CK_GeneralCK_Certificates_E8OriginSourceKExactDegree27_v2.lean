-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree27_v2
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactDegree27_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:05:36.859987+00:00
-- url     : https://prove2.me/theorems/c4884404-892a-476d-80ec-787a34d59dca
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactDegree27 (v2)` (transplant)
-- statement:
--   Platform version of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactDegree27 (v2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). Every theorem statement is exactly the source's (`coeffAt productData i j = coeffAt kData i j`, exact rational polynomial-coefficient identities). The only change is the proof method: each identity is checked by kernel evaluation (`decide +kernel`) instead of the source's `norm_num [...]` unfolding. The `norm_num` proofs produce very large proof terms (about 100 MB of compiled output per handful of theorems), so a module importing all degrees exceeds the platform's time limit. Project imports are redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactDegree27 with kernel-decided proofs (browse copy: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactDegree27.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem coeff_0_27 : coeffAt productData 0 27 = coeffAt kData 0 27 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_1_26 : coeffAt productData 1 26 = coeffAt kData 1 26 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_2_25 : coeffAt productData 2 25 = coeffAt kData 2 25 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_3_24 : coeffAt productData 3 24 = coeffAt kData 3 24 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_4_23 : coeffAt productData 4 23 = coeffAt kData 4 23 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_5_22 : coeffAt productData 5 22 = coeffAt kData 5 22 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_6_21 : coeffAt productData 6 21 = coeffAt kData 6 21 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_7_20 : coeffAt productData 7 20 = coeffAt kData 7 20 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_8_19 : coeffAt productData 8 19 = coeffAt kData 8 19 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_9_18 : coeffAt productData 9 18 = coeffAt kData 9 18 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_10_17 : coeffAt productData 10 17 = coeffAt kData 10 17 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_11_16 : coeffAt productData 11 16 = coeffAt kData 11 16 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_12_15 : coeffAt productData 12 15 = coeffAt kData 12 15 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_13_14 : coeffAt productData 13 14 = coeffAt kData 13 14 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_14_13 : coeffAt productData 14 13 = coeffAt kData 14 13 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_15_12 : coeffAt productData 15 12 = coeffAt kData 15 12 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_16_11 : coeffAt productData 16 11 = coeffAt kData 16 11 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_17_10 : coeffAt productData 17 10 = coeffAt kData 17 10 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_18_9 : coeffAt productData 18 9 = coeffAt kData 18 9 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_19_8 : coeffAt productData 19 8 = coeffAt kData 19 8 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_20_7 : coeffAt productData 20 7 = coeffAt kData 20 7 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_21_6 : coeffAt productData 21 6 = coeffAt kData 21 6 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_22_5 : coeffAt productData 22 5 = coeffAt kData 22 5 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_23_4 : coeffAt productData 23 4 = coeffAt kData 23 4 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_24_3 : coeffAt productData 24 3 = coeffAt kData 24 3 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_25_2 : coeffAt productData 25 2 = coeffAt kData 25 2 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_26_1 : coeffAt productData 26 1 = coeffAt kData 26 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_27_0 : coeffAt productData 27 0 = coeffAt kData 27 0 := by decide +kernel

end GeneralCK.Certificates.E8OriginSourceKExactReplay


