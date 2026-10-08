-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactFullTable_q00
-- name    : CK_CKLaneC3_CompactFullTable_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T02:01:50.993039+00:00
-- url     : https://prove2.me/theorems/2ae67238-be69-44db-b155-e65e3ab3714e
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactFullTable (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactFullTable (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactFullTable (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactFullTable (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactFullTable (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC3_CompactTable
import Definitions.Def_CK_CKLaneC3_CompactFull00
import Definitions.Def_CK_CKLaneC3_CompactFull01
import Definitions.Def_CK_CKLaneC3_CompactFull02
import Definitions.Def_CK_CKLaneC3_CompactFull03
import Definitions.Def_CK_CKLaneC3_CompactFull04
import Definitions.Def_CK_CKLaneC3_CompactFull05
import Definitions.Def_CK_CKLaneC3_CompactFull06
import Definitions.Def_CK_CKLaneC3_CompactFull07
import Definitions.Def_CK_CKLaneC3_CompactFull08
import Definitions.Def_CK_CKLaneC3_CompactFull09
import Definitions.Def_CK_CKLaneC3_CompactFull10
import Definitions.Def_CK_CKLaneC3_CompactFull11
import Definitions.Def_CK_CKLaneC3_CompactFull12
import Definitions.Def_CK_CKLaneC3_CompactFull13
import Definitions.Def_CK_CKLaneC3_CompactFull14
import Definitions.Def_CK_CKLaneC3_CompactFull15
import Definitions.Def_CK_CKLaneC3_CompactFull16
import Definitions.Def_CK_CKLaneC3_CompactFull17
import Definitions.Def_CK_CKLaneC3_CompactFull18
import Definitions.Def_CK_CKLaneC3_CompactFull19
import Definitions.Def_CK_CKLaneC3_CompactFull20
import Definitions.Def_CK_CKLaneC3_CompactFull21
import Definitions.Def_CK_CKLaneC3_CompactFull22
import Definitions.Def_CK_CKLaneC3_CompactFull23
import Definitions.Def_CK_CKLaneC3_CompactFull24
import Definitions.Def_CK_CKLaneC3_CompactFull25
import Definitions.Def_CK_CKLaneC3_CompactFull26
import Definitions.Def_CK_CKLaneC3_CompactFull27
import Definitions.Def_CK_CKLaneC3_CompactFull28
import Definitions.Def_CK_CKLaneC3_CompactFull29
import Definitions.Def_CK_CKLaneC3_CompactFull30
import Definitions.Def_CK_CKLaneC3_CompactFull31
import Definitions.Def_CK_CKLaneC3_CompactFull32
import Definitions.Def_CK_CKLaneC3_CompactFull33
import Definitions.Def_CK_CKLaneC3_CompactFull34
import Definitions.Def_CK_CKLaneC3_CompactFull35
import Definitions.Def_CK_CKLaneC3_CompactFull36
import Definitions.Def_CK_CKLaneC3_CompactFull37
import Definitions.Def_CK_CKLaneC3_CompactFull38
import Definitions.Def_CK_CKLaneC3_CompactFull39



/-! Lane C3 compact full-piece jet table (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactFullTable
open GeneralCK GeneralCK.Certificates
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain CKLaneC3.SlopeChainF
open CKLaneC3

def F : JTable := [CompactFull00.fchunk, CompactFull01.fchunk, CompactFull02.fchunk, CompactFull03.fchunk, CompactFull04.fchunk, CompactFull05.fchunk, CompactFull06.fchunk, CompactFull07.fchunk, CompactFull08.fchunk, CompactFull09.fchunk, CompactFull10.fchunk, CompactFull11.fchunk, CompactFull12.fchunk, CompactFull13.fchunk, CompactFull14.fchunk, CompactFull15.fchunk, CompactFull16.fchunk, CompactFull17.fchunk, CompactFull18.fchunk, CompactFull19.fchunk, CompactFull20.fchunk, CompactFull21.fchunk, CompactFull22.fchunk, CompactFull23.fchunk, CompactFull24.fchunk, CompactFull25.fchunk, CompactFull26.fchunk, CompactFull27.fchunk, CompactFull28.fchunk, CompactFull29.fchunk, CompactFull30.fchunk, CompactFull31.fchunk, CompactFull32.fchunk, CompactFull33.fchunk, CompactFull34.fchunk, CompactFull35.fchunk, CompactFull36.fchunk, CompactFull37.fchunk, CompactFull38.fchunk, CompactFull39.fchunk]

end CKLaneC3.CompactFullTable


