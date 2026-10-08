-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactTable_q00
-- name    : CK_CKLaneC3_CompactTable_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T20:25:22.733971+00:00
-- url     : https://prove2.me/theorems/7ec5d818-7c86-49c5-971a-df542ad89603
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactTable (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactTable (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactTable (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactTable (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactTable (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneC3_CompactChunk00
import Definitions.Def_CK_CKLaneC3_CompactChunk01
import Definitions.Def_CK_CKLaneC3_CompactChunk02
import Definitions.Def_CK_CKLaneC3_CompactChunk03
import Definitions.Def_CK_CKLaneC3_CompactChunk04
import Definitions.Def_CK_CKLaneC3_CompactChunk05
import Definitions.Def_CK_CKLaneC3_CompactChunk06
import Definitions.Def_CK_CKLaneC3_CompactChunk07
import Definitions.Def_CK_CKLaneC3_CompactChunk08
import Definitions.Def_CK_CKLaneC3_CompactChunk09
import Definitions.Def_CK_CKLaneC3_CompactChunk10
import Definitions.Def_CK_CKLaneC3_CompactChunk11
import Definitions.Def_CK_CKLaneC3_CompactChunk12
import Definitions.Def_CK_CKLaneC3_CompactChunk13
import Definitions.Def_CK_CKLaneC3_CompactChunk14
import Definitions.Def_CK_CKLaneC3_CompactChunk15
import Definitions.Def_CK_CKLaneC3_CompactChunk16
import Definitions.Def_CK_CKLaneC3_CompactChunk17
import Definitions.Def_CK_CKLaneC3_CompactChunk18
import Definitions.Def_CK_CKLaneC3_CompactChunk19
import Definitions.Def_CK_CKLaneC3_CompactChunk20
import Definitions.Def_CK_CKLaneC3_CompactChunk21
import Definitions.Def_CK_CKLaneC3_CompactChunk22
import Definitions.Def_CK_CKLaneC3_CompactChunk23
import Definitions.Def_CK_CKLaneC3_CompactChunk24
import Definitions.Def_CK_CKLaneC3_CompactChunk25
import Definitions.Def_CK_CKLaneC3_CompactChunk26
import Definitions.Def_CK_CKLaneC3_CompactChunk27
import Definitions.Def_CK_CKLaneC3_CompactChunk28
import Definitions.Def_CK_CKLaneC3_CompactChunk29
import Definitions.Def_CK_CKLaneC3_CompactChunk30
import Definitions.Def_CK_CKLaneC3_CompactChunk31
import Definitions.Def_CK_CKLaneC3_CompactChunk32
import Definitions.Def_CK_CKLaneC3_CompactChunk33
import Definitions.Def_CK_CKLaneC3_CompactChunk34
import Definitions.Def_CK_CKLaneC3_CompactChunk35
import Definitions.Def_CK_CKLaneC3_CompactChunk36
import Definitions.Def_CK_CKLaneC3_CompactChunk37
import Definitions.Def_CK_CKLaneC3_CompactChunk38
import Definitions.Def_CK_CKLaneC3_CompactChunk39



/-! Lane C3 compact slope table (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactTable
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain
open CKLaneC3

def T : List (List Piece) := [CompactChunk00.chunk, CompactChunk01.chunk, CompactChunk02.chunk, CompactChunk03.chunk, CompactChunk04.chunk, CompactChunk05.chunk, CompactChunk06.chunk, CompactChunk07.chunk, CompactChunk08.chunk, CompactChunk09.chunk, CompactChunk10.chunk, CompactChunk11.chunk, CompactChunk12.chunk, CompactChunk13.chunk, CompactChunk14.chunk, CompactChunk15.chunk, CompactChunk16.chunk, CompactChunk17.chunk, CompactChunk18.chunk, CompactChunk19.chunk, CompactChunk20.chunk, CompactChunk21.chunk, CompactChunk22.chunk, CompactChunk23.chunk, CompactChunk24.chunk, CompactChunk25.chunk, CompactChunk26.chunk, CompactChunk27.chunk, CompactChunk28.chunk, CompactChunk29.chunk, CompactChunk30.chunk, CompactChunk31.chunk, CompactChunk32.chunk, CompactChunk33.chunk, CompactChunk34.chunk, CompactChunk35.chunk, CompactChunk36.chunk, CompactChunk37.chunk, CompactChunk38.chunk, CompactChunk39.chunk]

end CKLaneC3.CompactTable


