-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B13_q02_q01
-- name    : CK_CKLaneG3_S_C0_B13_q02_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-11T08:45:19.334317+00:00
-- url     : https://prove2.me/theorems/0bfb422e-a37a-4c8c-b57c-2771c50d67a6
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B13 (piece 3 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B13 (piece 3 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B13 (piece 3 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B13 (piece 3 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B13 (piece 3 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B13_q02_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B13
open CKLaneD CKLaneG3
def r_50300015212402_9 : List (ℕ × ℕ × ℕ) := [(42, 48, 1), (44, 27, 1), (44, 29, 2), (44, 32, 2), (44, 25, 1), (44, 28, 1), (44, 31, 1), (44, 34, 4), (44, 39, 4), (44, 45, 3), (44, 49, 3), (44, 38, 1), (44, 43, 2), (44, 48, 1), (44, 52, 4), (22, 55, 1), (44, 16, 1), (44, 19, 1), (44, 7, 1), (44, 22, 1), (44, 56, 4), (22, 56, 1), (44, 60, 2), (22, 61, 1), (13, 24, 2), (13, 30, 2), (13, 26, 1), (13, 32, 2), (13, 27, 1), (13, 34, 1), (21, 31, 1), (13, 136, 2), (21, 33, 2), (13, 138, 2), (21, 35, 2), (13, 140, 1), (21, 37, 1), (13, 141, 1), (21, 38, 1), (14, 56, 1), (14, 62, 1), (14, 57, 1), (14, 63, 1), (21, 39, 2), (14, 127, 2), (14, 133, 2), (14, 129, 1), (14, 135, 2), (14, 130, 1), (14, 137, 1), (21, 41, 3), (21, 53, 1), (21, 32, 1), (21, 44, 5), (21, 54, 1), (21, 56, 1), (21, 59, 1), (21, 55, 1), (21, 57, 1), (21, 64, 1), (21, 60, 2), (21, 69, 2), (21, 65, 1), (21, 62, 1), (21, 66, 2), (21, 63, 1), (21, 68, 1), (21, 71, 5), (21, 82, 1), (21, 86, 1), (21, 88, 1), (21, 87, 1), (21, 76, 4), (21, 89, 2), (21, 92, 2), (21, 99, 2), (21, 94, 2), (21, 101, 2), (21, 96, 1), (21, 103, 1), (21, 97, 1), (21, 104, 2), (21, 107, 1), (21, 109, 1), (21, 106, 1), (21, 108, 1), (21, 114, 1), (21, 110, 2), (21, 119, 2), (21, 115, 1), (21, 112, 1), (21, 116, 2), (21, 113, 1), (21, 118, 1), (21, 121, 2), (21, 125, 1), (21, 80, 2), (21, 91, 1), (21, 123, 2), (21, 130, 2)]
def r_50300015212402_10 : List (ℕ × ℕ × ℕ) := [(21, 126, 1), (21, 132, 3), (21, 139, 1), (21, 145, 1), (21, 151, 1), (21, 153, 1), (21, 158, 1), (21, 164, 1), (21, 159, 1), (21, 165, 1), (21, 169, 1), (21, 152, 1), (21, 170, 2), (21, 154, 1), (22, 0, 1), (22, 4, 1), (22, 7, 2), (21, 155, 2), (22, 9, 2), (21, 157, 1), (22, 11, 4), (22, 18, 2), (22, 15, 1), (22, 20, 2), (22, 23, 1), (22, 25, 1), (22, 27, 2), (22, 33, 2), (22, 29, 2), (22, 35, 2), (22, 31, 1), (22, 37, 1), (22, 32, 1), (22, 38, 2), (22, 45, 1), (22, 40, 1), (22, 47, 1), (22, 50, 4), (22, 57, 2), (22, 54, 1), (22, 59, 2), (22, 62, 4), (22, 24, 1), (22, 26, 1), (22, 66, 5)]
/-- chunk `50300015212402`: 2513 label-0 leaves. -/
theorem c_50300015212402 : ∀ q ∈ CKLaneG3.S.Chunk.C_50300015212402.t.leavesR [2, 0, 4, 2, 1, 2, 5, 1, 0, 0, 0, 3, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50300015212402.t 0 [2, 0, 4, 2, 1, 2, 5, 1, 0, 0, 0, 3, 0, 5] SH id SH_ok
    (r_50300015212402_0 ++ (r_50300015212402_1 ++ (r_50300015212402_2 ++ (r_50300015212402_3 ++ (r_50300015212402_4 ++ (r_50300015212402_5 ++ (r_50300015212402_6 ++ (r_50300015212402_7 ++ (r_50300015212402_8 ++ (r_50300015212402_9 ++ (r_50300015212402_10))))))))))) (by decide +kernel)

end CKLaneG3.S.C0.B13


