-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactSlice27
-- name    : CK_CKLaneC3_CompactSlice27
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T05:09:17.49398+00:00
-- url     : https://prove2.me/theorems/7c4b0b22-807c-4071-936f-b0fe21c9521b
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactSlice27` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactSlice27` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactSlice27` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactSlice27 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactSlice27.lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch27
import Definitions.Def_CK_CKLaneC3_CompactTreeA

-- ===== source module CKLaneC3.CompactSlice27 =====
section

/-! Lane C3: leaf rectangles of CompactBatch27 = slice 27 of the tree leaves (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactSlice27
open CKLaneC3.CompactCover

theorem slice_eq : CompactBatch27.tags.map tagRect = CompactTreeA.rects27 := by
  decide +kernel

end CKLaneC3.CompactSlice27

end


