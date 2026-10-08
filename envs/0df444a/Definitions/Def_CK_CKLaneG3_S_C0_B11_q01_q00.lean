-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B11_q01_q00
-- name    : CK_CKLaneG3_S_C0_B11_q01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T01:55:25.551072+00:00
-- url     : https://prove2.me/theorems/7a144d18-25ba-494e-a637-2a1826a9c5db
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B11 (piece 2 of 3) (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B11_q00


set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B11
open CKLaneD CKLaneG3
def r_50203001431_5 : List (ℕ × ℕ × ℕ) := [(17, 212, 2), (17, 205, 1), (17, 208, 1), (17, 211, 1), (17, 214, 3), (17, 218, 2), (17, 221, 2), (17, 224, 2), (17, 227, 1), (17, 230, 1), (17, 234, 2), (17, 237, 1), (18, 0, 1), (18, 3, 2), (18, 6, 1), (18, 1, 1), (18, 8, 2), (18, 5, 1), (18, 7, 1), (18, 11, 2), (18, 14, 1), (18, 16, 2), (18, 19, 2), (18, 22, 2), (18, 25, 1), (18, 27, 2), (18, 30, 4), (18, 35, 2), (18, 24, 1), (18, 37, 4), (18, 42, 2), (18, 45, 2), (18, 41, 1), (18, 44, 1), (18, 47, 1), (18, 26, 1), (18, 29, 1), (18, 49, 1), (18, 51, 1), (18, 50, 1), (18, 52, 2), (18, 34, 1), (18, 54, 5), (18, 60, 1), (18, 62, 2), (18, 65, 2), (18, 59, 1), (18, 61, 1), (18, 64, 1), (18, 67, 2), (18, 71, 2), (18, 74, 2), (18, 69, 1), (18, 77, 2), (18, 80, 2), (18, 83, 2), (18, 86, 1), (18, 88, 2), (18, 82, 1), (18, 85, 1), (18, 87, 1), (18, 90, 3), (18, 94, 1), (18, 96, 2), (19, 0, 2), (18, 93, 1), (18, 95, 1), (18, 98, 1), (19, 2, 1), (21, 29, 3), (21, 35, 3), (21, 40, 1), (21, 44, 2), (21, 47, 1), (21, 49, 2), (21, 52, 2), (21, 55, 1), (21, 59, 1), (21, 62, 3), (21, 67, 2), (21, 70, 2), (21, 65, 1), (21, 73, 2), (21, 76, 1), (21, 78, 1), (22, 0, 2), (22, 3, 1), (22, 5, 3), (22, 11, 2), (19, 143, 1), (19, 145, 1), (19, 147, 5), (19, 153, 2), (19, 156, 1), (19, 158, 2), (19, 161, 1), (19, 163, 2), (19, 162, 1), (19, 165, 2), (19, 168, 7)]
def r_50203001431_6 : List (ℕ × ℕ × ℕ) := [(19, 152, 1), (19, 155, 1), (19, 157, 1), (19, 160, 1), (19, 177, 3), (19, 167, 1), (19, 180, 1), (19, 182, 3), (19, 186, 2), (19, 189, 1), (19, 191, 2), (19, 194, 3), (20, 0, 5), (20, 6, 2), (20, 9, 1), (20, 11, 2), (20, 5, 1), (20, 8, 1), (20, 10, 1), (20, 13, 1), (19, 188, 1), (20, 14, 1), (19, 190, 1), (19, 193, 1), (20, 15, 16), (20, 32, 2), (20, 31, 1), (20, 34, 1), (19, 144, 1), (20, 35, 1), (19, 146, 1), (20, 36, 11), (20, 48, 3), (20, 52, 2), (20, 55, 2), (20, 58, 6), (20, 65, 2), (20, 68, 2), (21, 0, 1), (21, 2, 2), (21, 1, 1), (21, 4, 2), (21, 7, 2), (21, 10, 5), (20, 64, 1), (21, 18, 1), (20, 67, 1), (20, 70, 1), (21, 19, 5), (21, 6, 1), (21, 9, 1), (21, 25, 2), (23, 82, 1), (23, 84, 1), (23, 87, 2), (23, 90, 1), (23, 83, 1), (23, 85, 2), (23, 89, 1), (23, 91, 2), (23, 96, 2), (23, 99, 2), (23, 93, 2), (23, 102, 2), (23, 105, 2), (23, 108, 2), (23, 111, 2), (23, 114, 2), (23, 107, 1), (23, 110, 1), (23, 113, 1), (23, 116, 2), (23, 120, 1), (23, 122, 1), (23, 118, 1), (23, 124, 2), (23, 121, 1), (23, 123, 1), (23, 127, 1), (23, 130, 3), (23, 134, 1), (23, 136, 1), (24, 0, 5), (24, 6, 1), (24, 8, 2), (24, 11, 2), (24, 14, 1), (24, 18, 3), (24, 22, 1), (24, 25, 2), (24, 28, 2), (24, 31, 1), (24, 33, 2), (24, 36, 2), (24, 32, 1), (24, 35, 1), (24, 38, 3), (24, 42, 1), (24, 44, 2), (24, 47, 2)]
end CKLaneG3.S.C0.B11


