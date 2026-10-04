-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S04_0047_part00
-- name    : CK_CKLaneC_RSC2_S04_0047_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T22:35:00.12933+00:00
-- url     : https://prove2.me/theorems/0a5534c9-ccc9-4dd4-b00d-473d890e895f
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S04_0047 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S04_0047 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S04_0047 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S04_0047 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S04_0047 (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneC_RSC2_S04_0047_part00_q02

namespace CKLaneC.RSC2.S04_0047
open CKLaneC.TM3 CKLaneC.RSCell
theorem s2_6 : stageC2 w6 q6 = true := by decide +kernel
theorem s3_6 : stageC3 w6 q6 = true := by decide +kernel

end CKLaneC.RSC2.S04_0047


