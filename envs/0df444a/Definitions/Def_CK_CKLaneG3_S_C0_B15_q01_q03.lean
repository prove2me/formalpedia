-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B15_q01_q03
-- name    : CK_CKLaneG3_S_C0_B15_q01_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T03:11:18.364909+00:00
-- url     : https://prove2.me/theorems/750d04f1-341b-4e07-9562-a0ffad43e33f
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 4 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B15 (piece 2 of 4) (piece 4 of 5).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B15_q01_q02

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B15
open CKLaneD CKLaneG3
def r_50300105202_1 : List (ℕ × ℕ × ℕ) := [(10, 16, 5), (7, 30, 1), (7, 34, 1), (11, 9, 2), (8, 68, 1), (11, 12, 2), (9, 7, 1), (9, 9, 1), (11, 14, 2), (11, 17, 2), (11, 11, 1), (10, 11, 1), (10, 15, 1), (11, 19, 1), (11, 16, 1), (12, 66, 3), (13, 0, 23), (13, 25, 8), (13, 34, 17), (13, 52, 3), (13, 56, 2), (13, 59, 2), (13, 51, 1), (13, 55, 1), (13, 58, 1), (13, 61, 5), (13, 67, 6), (14, 0, 3), (14, 4, 4), (13, 66, 1), (14, 9, 2), (14, 3, 1), (14, 8, 1), (13, 23, 2), (14, 11, 2), (13, 33, 1), (14, 13, 6), (14, 20, 3), (14, 24, 2), (14, 27, 3), (14, 19, 1), (14, 23, 1), (14, 26, 1), (14, 30, 1), (16, 13, 1), (17, 44, 16), (14, 44, 2), (17, 60, 2), (14, 47, 1), (17, 62, 2), (18, 0, 8), (14, 52, 1), (18, 8, 8), (14, 56, 1), (18, 16, 3), (14, 58, 1), (18, 19, 5), (18, 26, 7), (18, 34, 4), (18, 24, 2), (18, 38, 2), (18, 33, 1), (18, 40, 13), (14, 66, 2), (18, 53, 2), (14, 69, 1), (14, 71, 2), (18, 55, 2), (14, 74, 1), (16, 14, 4), (16, 19, 2), (16, 22, 2), (16, 25, 3), (16, 29, 4), (16, 34, 6), (16, 41, 2), (16, 44, 3), (16, 48, 1), (16, 50, 1), (16, 18, 1), (16, 21, 1), (16, 24, 1), (16, 28, 1), (14, 80, 1), (16, 52, 4), (16, 33, 1), (16, 56, 4), (16, 40, 1), (16, 43, 1), (16, 60, 1), (14, 84, 1), (16, 47, 1), (16, 61, 1), (16, 49, 1), (16, 51, 1), (16, 62, 2), (17, 0, 5), (17, 6, 2), (17, 9, 2), (17, 12, 3)]
end CKLaneG3.S.C0.B15


