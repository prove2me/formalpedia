-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactFullTable
-- name    : CK_CKLaneC3_CompactFullTable
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T02:08:59.530611+00:00
-- url     : https://prove2.me/theorems/3dcf67c2-aaf1-4a9f-a961-c4b98f21584a
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactFullTable` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactFullTable` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactFullTable` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactFullTable (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactFullTable.lean)

import Definitions.Def_CK_CKLaneC3_CompactFullTable_q00

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactFullTable
open GeneralCK GeneralCK.Certificates
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain CKLaneC3.SlopeChainF
open CKLaneC3
theorem F_valid : FullValid CompactTable.T F :=
  fullValid_of_forall2 (.cons CompactFull00.fchunk_ok (.cons CompactFull01.fchunk_ok (.cons CompactFull02.fchunk_ok (.cons CompactFull03.fchunk_ok (.cons CompactFull04.fchunk_ok (.cons CompactFull05.fchunk_ok (.cons CompactFull06.fchunk_ok (.cons CompactFull07.fchunk_ok (.cons CompactFull08.fchunk_ok (.cons CompactFull09.fchunk_ok (.cons CompactFull10.fchunk_ok (.cons CompactFull11.fchunk_ok (.cons CompactFull12.fchunk_ok (.cons CompactFull13.fchunk_ok (.cons CompactFull14.fchunk_ok (.cons CompactFull15.fchunk_ok (.cons CompactFull16.fchunk_ok (.cons CompactFull17.fchunk_ok (.cons CompactFull18.fchunk_ok (.cons CompactFull19.fchunk_ok (.cons CompactFull20.fchunk_ok (.cons CompactFull21.fchunk_ok (.cons CompactFull22.fchunk_ok (.cons CompactFull23.fchunk_ok (.cons CompactFull24.fchunk_ok (.cons CompactFull25.fchunk_ok (.cons CompactFull26.fchunk_ok (.cons CompactFull27.fchunk_ok (.cons CompactFull28.fchunk_ok (.cons CompactFull29.fchunk_ok (.cons CompactFull30.fchunk_ok (.cons CompactFull31.fchunk_ok (.cons CompactFull32.fchunk_ok (.cons CompactFull33.fchunk_ok (.cons CompactFull34.fchunk_ok (.cons CompactFull35.fchunk_ok (.cons CompactFull36.fchunk_ok (.cons CompactFull37.fchunk_ok (.cons CompactFull38.fchunk_ok (.cons CompactFull39.fchunk_ok (.nil)))))))))))))))))))))))))))))))))))))))))

end CKLaneC3.CompactFullTable


