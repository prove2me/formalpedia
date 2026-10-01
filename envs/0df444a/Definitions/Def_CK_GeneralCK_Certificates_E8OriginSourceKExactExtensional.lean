-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactExtensional
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactExtensional
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:57:33.787983+00:00
-- url     : https://prove2.me/theorems/e861b05f-7d8d-4cb8-b1b6-c4884cbf97e3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactExtensional` (transplant)
-- statement:
--   Transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactExtensional` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). Every statement is the source's. One kind of proof is changed: the support-membership lemmas `*_mem_kSupport` (each listed term's exponent pair lies in `kSupport`) are proved by one kernel evaluation (`decide +kernel` over the finite term list) instead of the source's case split with one `norm_num [kSupport]` per term, which exceeds the platform's time limit. Everything else is the original source, with project imports redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKExactExtensional` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactExtensional (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactExtensional.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactExtensional_part01

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

theorem productData_eval_eq_kData (s t : Real) :
    evalTerms productData s t = evalTerms kData s t := by
  exact evalTerms_eq_of_coeffAtOn kSupport productData kData s t
    productData_mem_kSupport kData_mem_kSupport
    coeffAt_productData_eq_kData_on_support

end GeneralCK.Certificates.E8OriginSourceKExactReplay


