-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactData
-- name    : CK_CKLaneC3_CompactData
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:19:44.413223+00:00
-- url     : https://prove2.me/theorems/e19ee261-ae39-42fe-a1e6-39926431d0db
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactData` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactData` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactData` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactData (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactData.lean)

import Definitions.Def_CK_CKLaneC3_CompactData_q15



/-! Lane C3 compact tables as pure data (generated): the same literals as
`CompactChunk*` (pieces) and `CompactFull*` (full-piece jets), without checks.
Validity is transported from the checked tables in `CompactBridge` (by `rfl`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactData
open GeneralCK GeneralCK.Certificates
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain CKLaneC3.SlopeChainF

def T : List (List Piece) := [chunk00, chunk01, chunk02, chunk03, chunk04, chunk05, chunk06, chunk07, chunk08, chunk09, chunk10, chunk11, chunk12, chunk13, chunk14, chunk15, chunk16, chunk17, chunk18, chunk19, chunk20, chunk21, chunk22, chunk23, chunk24, chunk25, chunk26, chunk27, chunk28, chunk29, chunk30, chunk31, chunk32, chunk33, chunk34, chunk35, chunk36, chunk37, chunk38, chunk39]

def F : JTable := [fchunk00, fchunk01, fchunk02, fchunk03, fchunk04, fchunk05, fchunk06, fchunk07, fchunk08, fchunk09, fchunk10, fchunk11, fchunk12, fchunk13, fchunk14, fchunk15, fchunk16, fchunk17, fchunk18, fchunk19, fchunk20, fchunk21, fchunk22, fchunk23, fchunk24, fchunk25, fchunk26, fchunk27, fchunk28, fchunk29, fchunk30, fchunk31, fchunk32, fchunk33, fchunk34, fchunk35, fchunk36, fchunk37, fchunk38, fchunk39]

end CKLaneC3.CompactData


