-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactTable_q01
-- name    : CK_CKLaneC3_CompactTable_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T02:07:00.097345+00:00
-- url     : https://prove2.me/theorems/78036f2e-6e7c-42d5-af1f-af4e8b39de91
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactTable (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactTable (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactTable (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactTable (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactTable (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneC3_CompactTable_q00

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactTable
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain
open CKLaneC3
theorem T_all : T.all (fun c => c.all Piece.check) = true := by
  simp only [T, List.all_cons, List.all_nil, CompactChunk00.chunk_ok, CompactChunk01.chunk_ok, CompactChunk02.chunk_ok, CompactChunk03.chunk_ok, CompactChunk04.chunk_ok, CompactChunk05.chunk_ok, CompactChunk06.chunk_ok, CompactChunk07.chunk_ok, CompactChunk08.chunk_ok, CompactChunk09.chunk_ok, CompactChunk10.chunk_ok, CompactChunk11.chunk_ok, CompactChunk12.chunk_ok, CompactChunk13.chunk_ok, CompactChunk14.chunk_ok, CompactChunk15.chunk_ok, CompactChunk16.chunk_ok, CompactChunk17.chunk_ok, CompactChunk18.chunk_ok, CompactChunk19.chunk_ok, CompactChunk20.chunk_ok, CompactChunk21.chunk_ok, CompactChunk22.chunk_ok, CompactChunk23.chunk_ok, CompactChunk24.chunk_ok, CompactChunk25.chunk_ok, CompactChunk26.chunk_ok, CompactChunk27.chunk_ok, CompactChunk28.chunk_ok, CompactChunk29.chunk_ok, CompactChunk30.chunk_ok, CompactChunk31.chunk_ok, CompactChunk32.chunk_ok, CompactChunk33.chunk_ok, CompactChunk34.chunk_ok, CompactChunk35.chunk_ok, CompactChunk36.chunk_ok, CompactChunk37.chunk_ok, CompactChunk38.chunk_ok, CompactChunk39.chunk_ok, Bool.and_self]

end CKLaneC3.CompactTable


