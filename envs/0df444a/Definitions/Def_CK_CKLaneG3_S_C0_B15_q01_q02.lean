-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B15_q01_q02
-- name    : CK_CKLaneG3_S_C0_B15_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T02:38:31.442458+00:00
-- url     : https://prove2.me/theorems/3287ec10-0335-4b2b-aff3-b64663fd0227
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 3 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B15 (piece 2 of 4) (piece 3 of 5).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B15_q01_q01

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B15
open CKLaneD CKLaneG3
def r_50300105202_0 : List (ℕ × ℕ × ℕ) := [(6, 90, 2), (6, 93, 3), (6, 97, 2), (6, 100, 2), (6, 92, 1), (6, 96, 1), (6, 99, 1), (6, 102, 4), (6, 107, 6), (7, 0, 3), (7, 4, 4), (6, 106, 1), (7, 9, 2), (7, 3, 1), (7, 8, 1), (0, 53, 1), (7, 11, 2), (0, 63, 1), (0, 68, 1), (7, 13, 4), (7, 18, 3), (7, 22, 2), (7, 25, 2), (7, 17, 1), (7, 21, 1), (7, 24, 1), (7, 27, 3), (7, 31, 3), (7, 35, 24), (7, 60, 3), (7, 64, 2), (7, 67, 2), (7, 70, 9), (7, 80, 1), (8, 0, 8), (8, 9, 4), (8, 14, 4), (8, 19, 8), (8, 28, 6), (8, 18, 1), (8, 34, 2), (8, 27, 1), (8, 36, 19), (8, 56, 3), (8, 60, 2), (8, 63, 3), (7, 59, 1), (7, 63, 1), (7, 66, 1), (7, 69, 1), (8, 67, 1), (7, 79, 1), (9, 0, 2), (8, 8, 1), (8, 13, 1), (9, 2, 5), (8, 55, 1), (8, 59, 1), (8, 62, 1), (8, 66, 1), (9, 8, 1), (3, 94, 1), (3, 98, 1), (3, 101, 1), (3, 104, 1), (9, 10, 1), (4, 4, 1), (9, 12, 2), (4, 13, 1), (9, 14, 7), (4, 30, 1), (4, 33, 1), (4, 36, 1), (4, 38, 1), (9, 22, 2), (9, 11, 1), (9, 24, 2), (9, 21, 1), (9, 26, 4), (9, 31, 3), (9, 35, 2), (9, 38, 3), (9, 30, 1), (9, 34, 1), (9, 37, 1), (9, 41, 9), (9, 51, 6), (9, 50, 1), (9, 57, 6), (5, 26, 1), (9, 63, 4), (10, 0, 1), (10, 2, 1), (10, 4, 2), (10, 7, 1), (10, 1, 1), (10, 3, 1), (10, 6, 1), (10, 8, 3), (10, 12, 3)]
end CKLaneG3.S.C0.B15


