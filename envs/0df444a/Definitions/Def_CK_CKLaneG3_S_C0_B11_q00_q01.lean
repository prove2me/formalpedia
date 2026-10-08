-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B11_q00_q01
-- name    : CK_CKLaneG3_S_C0_B11_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T00:18:41.802433+00:00
-- url     : https://prove2.me/theorems/0e9561de-d995-48f0-b860-00555d2c3c56
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B11 (piece 1 of 3) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B11 (piece 1 of 3) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B11 (piece 1 of 3) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B11 (piece 1 of 3) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B11 (piece 1 of 3) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B11_q00_q01_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B11
open CKLaneD CKLaneG3
def r_50203001431_1 : List (ℕ × ℕ × ℕ) := [(9, 125, 1), (9, 127, 4), (9, 83, 1), (9, 133, 2), (9, 136, 2), (9, 131, 2), (9, 135, 1), (9, 138, 1), (9, 97, 2), (9, 139, 2), (9, 106, 1), (9, 142, 1), (9, 141, 1), (9, 107, 1), (9, 145, 3), (9, 111, 1), (9, 154, 1), (9, 148, 1), (9, 155, 1), (9, 157, 1), (9, 156, 1), (9, 158, 4), (9, 163, 1), (9, 162, 1), (9, 164, 1), (9, 149, 3), (9, 165, 4), (9, 171, 2), (9, 174, 2), (9, 177, 3), (9, 124, 1), (9, 126, 1), (9, 180, 1), (9, 173, 1), (9, 176, 1), (9, 181, 2), (11, 92, 3), (11, 97, 1), (11, 99, 1), (11, 98, 1), (11, 100, 2), (11, 104, 1), (11, 95, 2), (11, 107, 2), (11, 102, 1), (11, 105, 1), (11, 109, 3), (11, 114, 4), (11, 112, 2), (11, 118, 6), (11, 126, 1), (11, 124, 2), (11, 129, 2), (12, 0, 3), (12, 4, 1), (12, 3, 1), (12, 5, 3), (12, 9, 4), (12, 14, 1), (12, 16, 1), (12, 19, 1), (12, 17, 1), (12, 20, 1), (12, 18, 1), (12, 21, 2), (12, 29, 1), (12, 8, 1), (12, 30, 4), (12, 35, 1), (12, 13, 1), (12, 15, 1), (12, 36, 1), (12, 34, 1), (12, 37, 2), (12, 40, 2), (12, 43, 2), (12, 39, 1), (12, 42, 1), (12, 47, 1), (12, 45, 1), (12, 49, 2), (12, 52, 2), (12, 55, 2), (12, 58, 2), (12, 51, 1), (12, 54, 1), (12, 57, 1), (12, 60, 5), (12, 67, 2), (12, 70, 2), (12, 73, 1), (12, 75, 2), (12, 74, 1), (12, 77, 4), (12, 83, 2), (12, 86, 4), (12, 91, 1), (12, 93, 1), (12, 90, 1), (12, 92, 1)]
end CKLaneG3.S.C0.B11


