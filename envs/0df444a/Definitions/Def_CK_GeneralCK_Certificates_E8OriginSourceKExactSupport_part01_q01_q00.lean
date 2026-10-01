-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part01_q01_q00
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part01_q01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:17:32.098351+00:00
-- url     : https://prove2.me/theorems/a74427f3-2a84-4436-be0d-28f9cd987a8c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 2 of 4) (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 2 of 4) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 2 of 4) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 2 of 4) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactSupport (part 2 of 3) (piece 2 of 4) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part01_q00


namespace GeneralCK.Certificates.E8OriginSourceKExactReplay
open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceKCoefficientReplay
set_option maxRecDepth 100000
theorem p1Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p1Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p1Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

end GeneralCK.Certificates.E8OriginSourceKExactReplay


