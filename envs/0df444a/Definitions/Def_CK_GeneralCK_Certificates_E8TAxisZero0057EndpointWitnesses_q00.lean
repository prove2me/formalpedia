-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:21:35.906979+00:00
-- url     : https://prove2.me/theorems/649c3675-b5df-40ba-84fa-faf9a019dd46
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057EndpointWitnesses (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057EndpointWitnesses_q00_q02

namespace GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0057Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def centerDLowerExp : DyadicInterval precision := ⟨478559189448815119699945348173357165094884054232, 478559189448815119699945348173357165094884185305⟩
end GeneralCK.Certificates.E8TAxisZero0057EndpointWitnesses


