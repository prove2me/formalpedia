-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B11_q00_q02
-- name    : CK_CKLaneG3_S_C0_B11_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T00:26:37.082576+00:00
-- url     : https://prove2.me/theorems/4cfdeb48-0d82-4c93-8f9a-425658261637
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B11 (piece 1 of 3) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B11 (piece 1 of 3) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B11 (piece 1 of 3) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B11 (piece 1 of 3) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B11 (piece 1 of 3) (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B11_q00_q01

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B11
open CKLaneD CKLaneG3
def r_50203001431_2 : List (ℕ × ℕ × ℕ) := [(12, 96, 1), (12, 85, 1), (12, 97, 2), (12, 94, 1), (12, 99, 3), (12, 103, 2), (12, 106, 2), (12, 109, 2), (12, 102, 1), (12, 105, 1), (12, 108, 1), (12, 111, 2), (12, 114, 1), (12, 116, 2), (12, 119, 2), (12, 113, 1), (12, 115, 1), (12, 118, 1), (12, 121, 1), (12, 186, 2), (13, 84, 3), (13, 88, 1), (13, 90, 1), (13, 87, 1), (13, 89, 1), (13, 92, 13), (13, 106, 1), (13, 108, 1), (13, 105, 1), (13, 91, 1), (13, 109, 2), (13, 116, 2), (13, 119, 2), (13, 111, 1), (13, 107, 1), (13, 121, 2), (13, 125, 1), (13, 127, 2), (13, 126, 1), (13, 129, 4), (13, 135, 7), (14, 0, 2), (13, 142, 1), (14, 2, 3), (13, 133, 1), (14, 6, 2), (14, 9, 2), (14, 12, 3), (14, 16, 6), (14, 23, 1), (14, 25, 2), (14, 28, 1), (14, 30, 1), (14, 15, 1), (14, 29, 1), (14, 31, 4), (14, 38, 5), (14, 44, 1), (14, 22, 1), (14, 24, 1), (14, 45, 1), (14, 27, 1), (14, 43, 1), (14, 46, 4), (14, 51, 13), (14, 65, 1), (14, 64, 1), (14, 66, 2), (14, 50, 1), (14, 68, 2), (14, 71, 2), (14, 74, 3), (14, 80, 3), (10, 232, 1), (10, 235, 1), (10, 237, 2), (10, 240, 1), (10, 242, 1), (10, 244, 5), (10, 252, 1), (10, 254, 1), (10, 256, 4), (10, 249, 2), (10, 253, 1), (10, 255, 1), (10, 261, 1), (10, 263, 2), (10, 266, 3), (10, 270, 2), (10, 273, 5), (10, 269, 1), (10, 272, 1), (10, 279, 2), (10, 278, 1), (10, 281, 1), (10, 283, 3), (10, 282, 1), (10, 288, 2), (10, 291, 6), (11, 0, 5)]
def r_50203001431_3 : List (ℕ × ℕ × ℕ) := [(11, 6, 4), (11, 11, 2), (11, 5, 1), (11, 14, 2), (11, 17, 2), (10, 260, 1), (10, 251, 1), (10, 262, 1), (10, 265, 1), (11, 20, 1), (11, 22, 1), (11, 21, 1), (11, 23, 2), (10, 286, 2), (10, 290, 1), (11, 29, 2), (10, 297, 2), (11, 32, 1), (11, 31, 1), (10, 299, 1), (11, 10, 1), (11, 13, 1), (11, 16, 1), (11, 19, 1), (11, 33, 1), (11, 35, 1), (11, 37, 2), (10, 233, 1), (11, 40, 2), (11, 43, 2), (11, 39, 1), (10, 234, 1), (11, 42, 1), (11, 45, 1), (10, 236, 1), (10, 239, 1), (10, 241, 1), (10, 243, 1), (11, 46, 5), (11, 52, 3), (11, 56, 3), (11, 51, 1), (11, 55, 1), (11, 61, 2), (11, 59, 1), (11, 64, 2), (11, 67, 2), (11, 70, 3), (11, 74, 2), (11, 66, 1), (11, 69, 1), (11, 73, 1), (11, 76, 4), (11, 81, 2), (11, 84, 1), (11, 63, 1), (11, 60, 1), (11, 86, 1), (11, 85, 1), (11, 89, 2), (14, 85, 1), (14, 87, 7), (14, 95, 8), (15, 0, 13), (14, 86, 1), (15, 13, 2), (15, 16, 2), (15, 19, 3), (14, 94, 1), (15, 24, 2), (15, 15, 1), (15, 18, 1), (15, 22, 2), (15, 26, 3), (14, 103, 1), (15, 29, 2), (15, 32, 2), (15, 35, 1), (15, 31, 1), (15, 34, 1), (15, 37, 9), (15, 49, 13), (15, 46, 2), (15, 63, 2), (15, 66, 2), (15, 69, 3), (15, 73, 2), (15, 76, 3), (15, 81, 3), (15, 72, 1), (15, 75, 1), (15, 79, 2), (15, 84, 2), (15, 87, 1), (15, 89, 3), (15, 86, 1), (15, 88, 1), (15, 93, 1), (15, 95, 2), (16, 0, 3)]
end CKLaneG3.S.C0.B11


