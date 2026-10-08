-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B2_q01
-- name    : CK_CKLaneG3_S_C2_B2_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T21:18:22.545379+00:00
-- url     : https://prove2.me/theorems/d11f7d0a-aca5-43d5-ba38-2966817737bd
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B2 (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B2 (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B2 (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B2 (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B2 (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B2_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B2
open CKLaneD CKLaneG3
/-- chunk `502020300431512`: 415 label-2 leaves. -/
theorem c_502020300431512 : ∀ q ∈ CKLaneG3.S.Chunk.C_502020300431512.t.leavesR [2, 1, 5, 1, 3, 4, 0, 0, 3, 0, 2, 0, 2, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_502020300431512.t 2 [2, 1, 5, 1, 3, 4, 0, 0, 3, 0, 2, 0, 2, 0, 5] SH id SH_ok
    (r_502020300431512_0) (by decide +kernel)

def r_502020300431513_0 : List (ℕ × ℕ × ℕ) := [(5, 0, 120), (6, 0, 120), (7, 0, 118), (8, 0, 119), (9, 0, 58)]
/-- chunk `502020300431513`: 535 label-2 leaves. -/
theorem c_502020300431513 : ∀ q ∈ CKLaneG3.S.Chunk.C_502020300431513.t.leavesR [3, 1, 5, 1, 3, 4, 0, 0, 3, 0, 2, 0, 2, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_502020300431513.t 2 [3, 1, 5, 1, 3, 4, 0, 0, 3, 0, 2, 0, 2, 0, 5] SH id SH_ok
    (r_502020300431513_0) (by decide +kernel)

end CKLaneG3.S.C2.B2


