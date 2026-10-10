-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B14_q00
-- name    : CK_CKLaneG3_S_C0_B14_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T21:07:58.613003+00:00
-- url     : https://prove2.me/theorems/b5177faa-b659-4601-9f45-63b97bfe73c0
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B14 (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B14 (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B14 (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B14 (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B14 (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B14_q00_q01

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B14
open CKLaneD CKLaneG3
def r_50300015212412_4 : List (ℕ × ℕ × ℕ) := [(17, 0, 2), (16, 43, 1), (17, 3, 3), (17, 8, 2), (17, 11, 3), (17, 2, 1), (17, 6, 2), (17, 10, 1), (17, 14, 2), (17, 17, 3), (17, 21, 1), (17, 23, 4), (17, 28, 3), (17, 32, 4), (17, 27, 1), (17, 31, 1), (17, 36, 1), (31, 35, 2), (31, 40, 3), (31, 37, 2), (31, 43, 2), (31, 39, 1), (31, 45, 2), (18, 19, 1), (18, 30, 1), (31, 47, 2), (18, 63, 1), (18, 67, 1), (18, 70, 1), (18, 73, 1), (31, 53, 4), (31, 49, 1), (19, 46, 1), (19, 49, 1), (31, 57, 2), (31, 50, 2), (31, 59, 2), (31, 52, 1), (31, 61, 1), (15, 30, 1), (31, 62, 2), (15, 31, 1), (15, 38, 1), (31, 64, 4), (31, 71, 3), (31, 68, 2), (31, 75, 2), (31, 70, 1), (31, 74, 1), (31, 77, 1)]
/-- chunk `50300015212412`: 999 label-0 leaves. -/
theorem c_50300015212412 : ∀ q ∈ CKLaneG3.S.Chunk.C_50300015212412.t.leavesR [2, 1, 4, 2, 1, 2, 5, 1, 0, 0, 0, 3, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50300015212412.t 0 [2, 1, 4, 2, 1, 2, 5, 1, 0, 0, 0, 3, 0, 5] SH id SH_ok
    (r_50300015212412_0 ++ (r_50300015212412_1 ++ (r_50300015212412_2 ++ (r_50300015212412_3 ++ (r_50300015212412_4))))) (by decide +kernel)

def r_50300015212413_0 : List (ℕ × ℕ × ℕ) := [(31, 84, 5), (32, 41, 10), (32, 52, 1), (32, 54, 3), (37, 75, 2), (38, 0, 1), (38, 4, 7), (38, 12, 2), (38, 1, 2), (38, 16, 2), (38, 11, 1), (38, 14, 2), (38, 19, 13), (38, 33, 3), (38, 37, 2), (38, 40, 2), (38, 43, 3), (38, 47, 3), (38, 51, 2), (38, 54, 3), (38, 46, 1), (38, 50, 1), (38, 53, 1), (38, 57, 5), (39, 0, 3), (39, 5, 4), (39, 10, 2), (39, 3, 2), (39, 13, 2), (38, 3, 1), (38, 18, 1), (39, 15, 2), (38, 32, 1), (38, 36, 1), (38, 39, 1), (38, 42, 1), (39, 19, 5), (39, 9, 1), (39, 12, 1), (39, 25, 2), (39, 29, 7), (39, 38, 5), (39, 44, 3), (39, 49, 14), (39, 64, 2), (40, 0, 1), (40, 2, 2), (40, 5, 3), (40, 9, 2), (40, 14, 5), (40, 20, 2), (39, 36, 2), (40, 38, 2), (39, 43, 1), (39, 47, 2), (40, 40, 4), (40, 45, 3), (40, 49, 2), (40, 52, 2), (40, 44, 1), (40, 48, 1), (40, 51, 1), (40, 54, 1), (39, 63, 1), (40, 1, 1), (40, 4, 1), (40, 8, 1), (40, 55, 2), (40, 11, 2), (40, 57, 2), (40, 19, 1), (40, 60, 2), (40, 13, 1), (40, 59, 1), (41, 0, 3), (41, 4, 2), (41, 7, 2), (41, 10, 2), (41, 3, 1), (41, 6, 1), (41, 9, 1), (41, 12, 4), (41, 17, 2), (41, 21, 1), (41, 23, 3), (41, 16, 1), (41, 19, 2), (41, 22, 1), (41, 26, 1), (32, 51, 1), (32, 53, 1), (41, 27, 4), (41, 32, 1), (41, 31, 1), (41, 33, 6), (41, 40, 3), (41, 44, 2), (41, 47, 3), (41, 51, 6), (41, 60, 4)]
end CKLaneG3.S.C0.B14


