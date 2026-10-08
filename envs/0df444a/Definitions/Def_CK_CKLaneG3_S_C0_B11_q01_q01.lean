-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B11_q01_q01
-- name    : CK_CKLaneG3_S_C0_B11_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T01:59:26.791346+00:00
-- url     : https://prove2.me/theorems/100b67b8-1434-437f-a721-16411f9a3a15
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B11 (piece 2 of 3) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B11_q01_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B11
open CKLaneD CKLaneG3
def r_50203001431_7 : List (ℕ × ℕ × ℕ) := [(24, 41, 1), (24, 43, 1), (24, 46, 1), (24, 49, 1), (24, 27, 1), (24, 50, 1), (24, 30, 1), (24, 51, 5), (24, 57, 2), (24, 60, 1), (24, 56, 1), (24, 59, 1), (24, 61, 1), (25, 0, 1), (25, 4, 1), (25, 6, 1), (25, 1, 2), (25, 9, 2), (25, 5, 1), (25, 7, 2), (25, 12, 2), (25, 15, 1), (25, 17, 2), (25, 20, 3), (26, 29, 1), (26, 31, 1), (26, 33, 2), (26, 36, 1), (26, 30, 1), (26, 32, 1), (26, 35, 1), (26, 37, 2), (26, 41, 2), (26, 44, 2), (26, 39, 1), (26, 47, 2), (26, 131, 5), (26, 137, 10), (27, 0, 19), (27, 20, 7), (27, 28, 3), (27, 33, 2), (26, 136, 1), (27, 35, 6), (27, 42, 3), (27, 31, 1), (27, 46, 2), (27, 41, 1), (27, 45, 1), (27, 49, 1), (27, 51, 2), (27, 50, 1), (27, 53, 5), (28, 0, 8), (28, 9, 1), (28, 8, 1), (28, 10, 4), (28, 15, 3), (28, 19, 2), (28, 22, 2), (28, 25, 2), (28, 28, 3), (28, 32, 2), (28, 35, 2), (28, 27, 1), (28, 31, 1), (28, 34, 1), (28, 37, 1), (27, 19, 1), (28, 38, 3), (28, 43, 9), (28, 53, 2), (27, 27, 1), (28, 55, 3), (28, 41, 1), (28, 58, 2), (28, 52, 1), (28, 61, 5), (29, 0, 3), (29, 99, 3), (29, 103, 1), (29, 102, 1), (29, 104, 9), (29, 114, 2), (29, 3, 1), (29, 116, 5), (29, 122, 1), (29, 124, 1), (29, 121, 1), (29, 123, 1), (30, 0, 2), (30, 3, 2), (30, 2, 1), (30, 6, 1), (30, 5, 1), (30, 7, 9), (30, 202, 1), (30, 204, 2), (30, 203, 1), (30, 206, 9)]
def r_50203001431_8 : List (ℕ × ℕ × ℕ) := [(31, 0, 8), (31, 9, 3), (31, 13, 2), (31, 16, 3), (31, 20, 1), (31, 22, 8), (31, 31, 1), (31, 30, 1), (31, 32, 2), (31, 21, 1), (31, 34, 3), (31, 38, 6)]
end CKLaneG3.S.C0.B11


