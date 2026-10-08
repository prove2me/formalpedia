-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B9_q01
-- name    : CK_CKLaneG3_S_C2_B9_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T01:17:56.238994+00:00
-- url     : https://prove2.me/theorems/76c97988-114a-4173-9413-e3b5f75ce69f
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B9 (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B9 (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B9 (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B9 (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B9 (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B9_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B9
open CKLaneD CKLaneG3
def r_5030010530431531_0 : List (ℕ × ℕ × ℕ) := [(9, 80, 33), (10, 0, 113), (11, 0, 113), (12, 0, 119), (13, 0, 119), (14, 0, 55), (15, 0, 109), (16, 0, 90)]
/-- chunk `5030010530431531`: 751 label-2 leaves. -/
theorem c_5030010530431531 : ∀ q ∈ CKLaneG3.S.Chunk.C_5030010530431531.t.leavesR [1, 3, 5, 1, 3, 4, 0, 3, 5, 0, 1, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5030010530431531.t 2 [1, 3, 5, 1, 3, 4, 0, 3, 5, 0, 1, 0, 0, 3, 0, 5] SH id SH_ok
    (r_5030010530431531_0) (by decide +kernel)

/-- chunk `50300105305`: 0 label-2 leaves. -/
theorem c_50300105305 : ∀ q ∈ CKLaneG3.S.Chunk.C_50300105305.t.leavesR [5, 0, 3, 5, 0, 1, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_none (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50300105305.t 2 [5, 0, 3, 5, 0, 1, 0, 0, 3, 0, 5] (by decide +kernel)

def r_503001053142_0 : List (ℕ × ℕ × ℕ) := [(16, 90, 30), (17, 0, 104), (18, 0, 119), (19, 0, 120), (20, 0, 9)]
end CKLaneG3.S.C2.B9


