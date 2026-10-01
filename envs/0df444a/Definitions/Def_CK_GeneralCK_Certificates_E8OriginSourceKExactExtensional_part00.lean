-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactExtensional_part00
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactExtensional_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:03:42.941491+00:00
-- url     : https://prove2.me/theorems/ac1f10c2-a8c9-4f5c-b1f0-4240673a4721
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactExtensional (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactExtensional (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKExactExtensional (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactExtensional (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactExtensional (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactSupport

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

theorem productData_mem_kSupport (r : Term) (hr : r ∈ productData) :
    (r.i, r.j) ∈ kSupport := by
  rw [productData] at hr
  rcases List.mem_append.mp hr with hr | h11
  ·
    rcases List.mem_append.mp hr with hr | h10
    ·
      rcases List.mem_append.mp hr with hr | h9
      ·
        rcases List.mem_append.mp hr with hr | h8
        ·
          rcases List.mem_append.mp hr with hr | h7
          ·
            rcases List.mem_append.mp hr with hr | h6
            ·
              rcases List.mem_append.mp hr with hr | h5
              ·
                rcases List.mem_append.mp hr with hr | h4
                ·
                  rcases List.mem_append.mp hr with hr | h3
                  ·
                    rcases List.mem_append.mp hr with hr | h2
                    ·
                      rcases List.mem_append.mp hr with hr | h1
                      ·
                        exact p0Data_mem_kSupport r hr
                      · exact p1Data_mem_kSupport r h1
                    · exact p2Data_mem_kSupport r h2
                  · exact p3Data_mem_kSupport r h3
                · exact p4Data_mem_kSupport r h4
              · exact p5Data_mem_kSupport r h5
            · exact p6Data_mem_kSupport r h6
          · exact p7Data_mem_kSupport r h7
        · exact p8Data_mem_kSupport r h8
      · exact p9Data_mem_kSupport r h9
    · exact p10Data_mem_kSupport r h10
  · exact p11Data_mem_kSupport r h11


end GeneralCK.Certificates.E8OriginSourceKExactReplay


