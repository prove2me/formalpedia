-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactDegree9_v2
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactDegree9_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:20:08.632119+00:00
-- url     : https://prove2.me/theorems/9617e106-d6bb-4cc4-8e22-5936de100792
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactDegree9 (v2)` (transplant)
-- statement:
--   Platform version of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactDegree9 (v2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). Every theorem statement is exactly the source's (`coeffAt productData i j = coeffAt kData i j`, exact rational polynomial-coefficient identities). The only change is the proof method: each identity is checked by kernel evaluation (`decide +kernel`) instead of the source's `norm_num [...]` unfolding. The `norm_num` proofs produce very large proof terms (about 100 MB of compiled output per handful of theorems), so a module importing all degrees exceeds the platform's time limit. Project imports are redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactDegree9 with kernel-decided proofs (browse copy: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactDegree9.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem coeff_0_9 : coeffAt productData 0 9 = coeffAt kData 0 9 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_1_8 : coeffAt productData 1 8 = coeffAt kData 1 8 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_2_7 : coeffAt productData 2 7 = coeffAt kData 2 7 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_3_6 : coeffAt productData 3 6 = coeffAt kData 3 6 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_4_5 : coeffAt productData 4 5 = coeffAt kData 4 5 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_5_4 : coeffAt productData 5 4 = coeffAt kData 5 4 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_6_3 : coeffAt productData 6 3 = coeffAt kData 6 3 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_7_2 : coeffAt productData 7 2 = coeffAt kData 7 2 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_8_1 : coeffAt productData 8 1 = coeffAt kData 8 1 := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coeff_9_0 : coeffAt productData 9 0 = coeffAt kData 9 0 := by decide +kernel

end GeneralCK.Certificates.E8OriginSourceKExactReplay


