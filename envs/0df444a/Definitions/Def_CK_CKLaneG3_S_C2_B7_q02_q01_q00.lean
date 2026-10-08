-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B7_q02_q01_q00
-- name    : CK_CKLaneG3_S_C2_B7_q02_q01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T22:59:43.319684+00:00
-- url     : https://prove2.me/theorems/1e4d6fe9-a087-4e0a-a1ed-da426526582f
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B7 (piece 3 of 4) (piece 2 of 3) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B7 (piece 3 of 4) (piece 2 of 3) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B7 (piece 3 of 4) (piece 2 of 3) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B7 (piece 3 of 4) (piece 2 of 3) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B7 (piece 3 of 4) (piece 2 of 3) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B7_q02_q00


set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B7
open CKLaneD CKLaneG3
/-- chunk `5030010521`: 1 label-2 leaves. -/
theorem c_5030010521 : ∀ q ∈ CKLaneG3.S.Chunk.C_5030010521.t.leavesR [1, 2, 5, 0, 1, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5030010521.t 2 [1, 2, 5, 0, 1, 0, 0, 3, 0, 5] SH id SH_ok
    (r_5030010521_0) (by decide +kernel)

end CKLaneG3.S.C2.B7


