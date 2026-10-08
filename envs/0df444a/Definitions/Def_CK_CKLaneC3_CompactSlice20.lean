-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactSlice20
-- name    : CK_CKLaneC3_CompactSlice20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T05:54:01.633996+00:00
-- url     : https://prove2.me/theorems/0fe499c0-c47e-4d10-9cbf-89dde079dc70
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactSlice20` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactSlice20` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactSlice20` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactSlice20 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactSlice20.lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch20
import Definitions.Def_CK_CKLaneC3_CompactTreeA

-- ===== source module CKLaneC3.CompactSlice20 =====
section

/-! Lane C3: leaf rectangles of CompactBatch20 = slice 20 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice20
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch20.tags.map tagRect = CompactTreeA.rects20 := by
  decide +kernel

end CKLaneC3.CompactSlice20

end


