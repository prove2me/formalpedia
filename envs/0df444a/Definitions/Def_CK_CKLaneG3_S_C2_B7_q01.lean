-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B7_q01
-- name    : CK_CKLaneG3_S_C2_B7_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T18:32:14.009911+00:00
-- url     : https://prove2.me/theorems/ed26f48a-60b3-4c2a-870a-79b23d87d432
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B7 (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B7 (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B7 (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B7 (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B7 (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B7_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B7
open CKLaneD CKLaneG3
def r_50300105203402_0 : List (ℕ × ℕ × ℕ) := [(16, 59, 61), (17, 0, 91), (18, 0, 120), (19, 0, 60)]
/-- chunk `50300105203402`: 332 label-2 leaves. -/
theorem c_50300105203402 : ∀ q ∈ CKLaneG3.S.Chunk.C_50300105203402.t.leavesR [2, 0, 4, 3, 0, 2, 5, 0, 1, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50300105203402.t 2 [2, 0, 4, 3, 0, 2, 5, 0, 1, 0, 0, 3, 0, 5] SH id SH_ok
    (r_50300105203402_0) (by decide +kernel)

def r_50300105203403_0 : List (ℕ × ℕ × ℕ) := [(19, 60, 58), (20, 0, 120), (21, 0, 117), (22, 0, 113), (23, 0, 120), (24, 0, 118), (25, 0, 103)]
/-- chunk `50300105203403`: 749 label-2 leaves. -/
theorem c_50300105203403 : ∀ q ∈ CKLaneG3.S.Chunk.C_50300105203403.t.leavesR [3, 0, 4, 3, 0, 2, 5, 0, 1, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50300105203403.t 2 [3, 0, 4, 3, 0, 2, 5, 0, 1, 0, 0, 3, 0, 5] SH id SH_ok
    (r_50300105203403_0) (by decide +kernel)

def r_5030010520341_0 : List (ℕ × ℕ × ℕ) := [(25, 103, 14), (26, 0, 120), (27, 0, 66)]
/-- chunk `5030010520341`: 200 label-2 leaves. -/
theorem c_5030010520341 : ∀ q ∈ CKLaneG3.S.Chunk.C_5030010520341.t.leavesR [1, 4, 3, 0, 2, 5, 0, 1, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5030010520341.t 2 [1, 4, 3, 0, 2, 5, 0, 1, 0, 0, 3, 0, 5] SH id SH_ok
    (r_5030010520341_0) (by decide +kernel)

end CKLaneG3.S.C2.B7


