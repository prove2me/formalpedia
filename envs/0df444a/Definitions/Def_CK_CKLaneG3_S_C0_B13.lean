-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B13
-- name    : CK_CKLaneG3_S_C0_B13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-12T03:47:41.799535+00:00
-- url     : https://prove2.me/theorems/cce73e34-ef58-49aa-9e71-6937bc17e28c
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B13` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B13` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B13` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B13 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B13.lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B13_q02

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B13
open CKLaneD CKLaneG3
def r_50300015212403_4 : List (ℕ × ℕ × ℕ) := [(49, 42, 4), (49, 47, 2), (49, 50, 2), (49, 53, 2), (49, 46, 1), (49, 49, 1), (49, 52, 1), (49, 55, 4), (49, 60, 3), (49, 65, 3), (49, 69, 3), (49, 59, 1), (49, 63, 2), (49, 68, 1), (49, 72, 4), (49, 78, 2), (49, 81, 2), (49, 84, 2), (49, 76, 1), (49, 80, 1), (49, 86, 3), (49, 90, 1), (50, 0, 2), (50, 3, 2), (50, 6, 2), (49, 89, 1), (50, 2, 1), (50, 5, 1), (50, 8, 4), (50, 13, 3), (50, 20, 2), (50, 23, 2), (50, 16, 1), (46, 113, 1), (46, 118, 2), (46, 114, 1), (46, 120, 1), (51, 78, 2), (47, 7, 2), (47, 11, 2), (51, 80, 1), (49, 40, 2), (51, 81, 1), (45, 47, 1), (50, 12, 1), (50, 17, 2), (50, 22, 1), (50, 19, 1), (51, 82, 2)]
/-- chunk `50300015212403`: 1283 label-0 leaves. -/
theorem c_50300015212403 : ∀ q ∈ CKLaneG3.S.Chunk.C_50300015212403.t.leavesR [3, 0, 4, 2, 1, 2, 5, 1, 0, 0, 0, 3, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50300015212403.t 0 [3, 0, 4, 2, 1, 2, 5, 1, 0, 0, 0, 3, 0, 5] SH id SH_ok
    (r_50300015212403_0 ++ (r_50300015212403_1 ++ (r_50300015212403_2 ++ (r_50300015212403_3 ++ (r_50300015212403_4))))) (by decide +kernel)

end CKLaneG3.S.C0.B13


