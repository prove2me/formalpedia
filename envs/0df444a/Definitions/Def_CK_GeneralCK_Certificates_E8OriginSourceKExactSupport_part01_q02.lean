-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part01_q02
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:54:19.799869+00:00
-- url     : https://prove2.me/theorems/219e13f1-d321-40eb-842f-a7245c5c54c6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 3 of 4)` (transplant)
-- statement:
--   Transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture). Every statement is the source's. One kind of proof is changed: the support-membership lemmas `pNData_mem_kSupport` (each product-data term's exponent pair lies in `kSupport`) are proved by one kernel evaluation (`decide +kernel` over the finite term list) instead of the source's case split with one `norm_num [kSupport]` per term, which exceeds the platform's time limit. Everything else is the original source, with project imports redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKExactSupport` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactSupport (part 2 of 3) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part01_q01

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay
open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceKCoefficientReplay
set_option maxRecDepth 100000
theorem p5Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p5Data) : (r.i, r.j) ∈ kSupport := by
  have h : ∀ r ∈ E8OriginSourceKProducts.p5Data, (r.i, r.j) ∈ kSupport := by decide +kernel
  exact h r hr

theorem p6Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p6Data) : (r.i, r.j) ∈ kSupport := by
  have h : ∀ r ∈ E8OriginSourceKProducts.p6Data, (r.i, r.j) ∈ kSupport := by decide +kernel
  exact h r hr

theorem p7Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p7Data) : (r.i, r.j) ∈ kSupport := by
  have h : ∀ r ∈ E8OriginSourceKProducts.p7Data, (r.i, r.j) ∈ kSupport := by decide +kernel
  exact h r hr

theorem p8Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p8Data) : (r.i, r.j) ∈ kSupport := by
  have h : ∀ r ∈ E8OriginSourceKProducts.p8Data, (r.i, r.j) ∈ kSupport := by decide +kernel
  exact h r hr

end GeneralCK.Certificates.E8OriginSourceKExactReplay


