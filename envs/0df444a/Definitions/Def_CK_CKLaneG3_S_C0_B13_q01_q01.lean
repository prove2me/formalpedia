-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B13_q01_q01
-- name    : CK_CKLaneG3_S_C0_B13_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-10T18:33:40.326978+00:00
-- url     : https://prove2.me/theorems/72be8140-73e8-4195-9b5e-e016aa6116da
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B13 (piece 2 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B13 (piece 2 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B13 (piece 2 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B13 (piece 2 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B13 (piece 2 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B13_q01_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B13
open CKLaneD CKLaneG3
/-- chunk `5030001520`: 406 label-0 leaves. -/
theorem c_5030001520 : ∀ q ∈ CKLaneG3.S.Chunk.C_5030001520.t.leavesR [0, 2, 5, 1, 0, 0, 0, 3, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5030001520.t 0 [0, 2, 5, 1, 0, 0, 0, 3, 0, 5] SH id SH_ok
    (r_5030001520_0 ++ (r_5030001520_1)) (by decide +kernel)

def r_50300015212402_0 : List (ℕ × ℕ × ℕ) := [(10, 21, 9), (10, 31, 7), (10, 41, 3), (10, 47, 1), (10, 30, 1), (10, 48, 1), (10, 51, 3), (10, 57, 17), (10, 75, 1), (10, 74, 1), (10, 76, 12), (11, 0, 12), (11, 13, 3), (11, 17, 2), (11, 20, 2), (11, 23, 5), (11, 29, 11), (11, 43, 2), (11, 28, 1), (11, 45, 6), (11, 54, 3), (11, 60, 1), (11, 62, 2), (11, 61, 1), (11, 64, 10), (11, 75, 1), (11, 77, 5), (12, 0, 11), (12, 12, 1), (12, 11, 1), (12, 14, 1), (12, 13, 1), (12, 15, 18), (12, 34, 2), (12, 37, 2), (12, 36, 1), (12, 39, 5), (14, 140, 5), (14, 146, 4), (15, 0, 1), (15, 2, 1), (15, 1, 1), (15, 3, 8), (14, 7, 1), (15, 11, 6), (14, 1, 2), (14, 4, 2), (14, 8, 2), (14, 11, 2), (15, 17, 3), (15, 21, 15), (15, 20, 1), (14, 17, 1), (15, 36, 2), (14, 21, 1), (14, 23, 2), (15, 38, 2), (14, 26, 1), (15, 40, 2), (14, 29, 1), (15, 42, 2), (14, 32, 1), (15, 44, 1), (14, 145, 1), (15, 45, 1), (15, 47, 3), (14, 30, 1), (14, 33, 2), (15, 46, 1), (15, 50, 12), (16, 0, 5), (16, 6, 1), (16, 5, 1), (16, 7, 6), (14, 39, 2), (14, 42, 2), (14, 45, 2), (14, 48, 2), (16, 13, 1), (16, 15, 7), (16, 23, 1), (16, 14, 1), (16, 25, 2), (16, 28, 1), (16, 27, 1), (16, 29, 8), (14, 73, 1), (16, 22, 1), (16, 37, 1), (16, 24, 1), (16, 38, 4), (16, 43, 2), (16, 42, 1), (16, 45, 1), (14, 79, 1), (16, 46, 4), (16, 53, 7), (17, 0, 1), (16, 60, 1), (17, 2, 1)]
def r_50300015212402_1 : List (ℕ × ℕ × ℕ) := [(17, 1, 1), (17, 3, 14), (17, 18, 6), (14, 96, 1), (17, 24, 2), (14, 100, 1), (17, 26, 1), (17, 17, 1), (14, 102, 1), (17, 27, 2), (14, 105, 1), (17, 29, 1), (17, 31, 14), (17, 30, 1), (17, 45, 2), (17, 48, 1), (17, 47, 1), (17, 49, 6), (10, 38, 2), (10, 44, 2), (10, 49, 1), (10, 54, 2), (10, 40, 1), (10, 46, 1), (10, 50, 1), (10, 56, 1), (13, 0, 2), (13, 3, 2), (13, 6, 2), (13, 9, 2), (13, 2, 1), (13, 5, 1), (13, 8, 1), (13, 11, 1), (11, 12, 1), (11, 16, 1), (11, 19, 1), (11, 22, 1), (13, 12, 2), (11, 40, 2), (13, 14, 2), (11, 51, 2), (11, 57, 2), (11, 42, 1), (13, 16, 1), (11, 53, 1), (11, 59, 1), (13, 17, 2), (13, 21, 1), (13, 19, 2), (13, 28, 1), (13, 22, 2), (13, 35, 2), (13, 29, 1), (13, 37, 3), (13, 43, 3), (11, 74, 1), (11, 76, 1), (13, 49, 1), (13, 52, 3), (13, 40, 2), (13, 46, 2), (13, 50, 1), (13, 55, 2), (13, 58, 2), (11, 82, 1), (13, 60, 10), (13, 71, 1), (13, 70, 1), (13, 72, 9), (13, 82, 2), (13, 85, 2), (13, 88, 2), (13, 91, 2), (13, 94, 3), (13, 98, 2), (13, 101, 2), (13, 93, 1), (13, 97, 1), (13, 100, 1), (13, 103, 4), (12, 33, 1), (13, 110, 2), (13, 113, 1), (13, 112, 1), (13, 114, 3), (13, 120, 3), (13, 107, 2), (13, 126, 2), (13, 117, 2), (13, 123, 2), (13, 42, 1), (13, 48, 1), (13, 51, 1), (13, 57, 1), (13, 129, 1), (13, 131, 1), (13, 81, 1), (13, 84, 1), (13, 87, 1)]
end CKLaneG3.S.C0.B13


