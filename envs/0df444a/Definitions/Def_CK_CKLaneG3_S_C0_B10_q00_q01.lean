-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B10_q00_q01
-- name    : CK_CKLaneG3_S_C0_B10_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T23:01:11.632759+00:00
-- url     : https://prove2.me/theorems/5e465c4b-3108-4cec-b9dc-35adccee5d29
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B10 (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B10_q00_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B10
open CKLaneD CKLaneG3
def r_50203001420_0 : List (ℕ × ℕ × ℕ) := [(0, 63, 4), (0, 75, 2), (0, 86, 15), (0, 124, 2), (0, 144, 1), (0, 126, 2), (0, 145, 2), (0, 128, 2), (0, 147, 2), (0, 101, 13), (0, 130, 2), (0, 149, 1), (0, 132, 2), (0, 150, 2), (0, 134, 2), (0, 152, 2), (0, 136, 1), (0, 154, 2), (0, 114, 6), (0, 164, 1), (0, 137, 1), (0, 156, 2), (0, 138, 1), (0, 158, 1), (0, 139, 1), (0, 159, 1), (0, 140, 1), (0, 160, 1), (0, 120, 4), (0, 165, 2), (0, 141, 1), (0, 161, 1), (0, 142, 1), (0, 162, 1), (0, 143, 1), (0, 163, 1), (0, 167, 1), (0, 198, 2), (0, 218, 2), (0, 200, 2), (0, 220, 2), (0, 238, 3), (1, 0, 1), (0, 241, 2), (1, 20, 2), (1, 1, 1), (0, 202, 2), (0, 222, 1), (0, 204, 2), (0, 223, 2), (0, 206, 2), (0, 225, 2), (0, 243, 2), (1, 2, 2), (0, 245, 2), (1, 4, 2), (0, 208, 2), (0, 227, 2), (0, 210, 1), (0, 229, 2), (0, 211, 1), (0, 231, 1), (0, 212, 1), (0, 232, 1), (0, 247, 2), (1, 6, 2), (0, 249, 2), (1, 8, 2), (0, 251, 1), (1, 10, 1), (0, 252, 1), (1, 11, 1), (0, 213, 1), (0, 233, 1), (0, 214, 1), (0, 234, 1), (0, 215, 1), (0, 235, 1), (0, 216, 1), (0, 236, 1), (0, 253, 2), (1, 12, 2), (0, 255, 1), (1, 14, 2), (0, 256, 1), (1, 16, 1), (0, 257, 1), (1, 17, 1), (0, 67, 2), (0, 77, 2), (0, 69, 1), (0, 79, 2), (0, 70, 1), (0, 81, 1), (0, 71, 1), (0, 82, 1), (1, 26, 12), (0, 72, 1), (0, 83, 1), (0, 73, 1)]
def r_50203001420_1 : List (ℕ × ℕ × ℕ) := [(0, 84, 1), (0, 74, 1), (0, 85, 1), (1, 52, 1), (1, 38, 10), (1, 59, 4), (1, 48, 4), (1, 63, 2), (1, 53, 2), (1, 65, 1), (1, 55, 4), (1, 83, 2), (1, 99, 1), (1, 85, 2), (1, 100, 2), (1, 87, 2), (1, 102, 2), (1, 89, 1), (1, 104, 2), (1, 115, 2), (1, 132, 1), (1, 117, 2), (1, 133, 2), (1, 119, 2), (1, 135, 2), (1, 90, 2), (1, 106, 2), (1, 92, 2), (1, 108, 2), (1, 94, 1), (1, 110, 1), (1, 95, 1), (1, 111, 1), (1, 121, 2), (1, 137, 1), (1, 123, 2), (1, 138, 2), (1, 125, 1), (1, 140, 2), (1, 126, 1), (1, 142, 1), (1, 96, 1), (1, 112, 1), (1, 97, 1), (1, 113, 1), (1, 148, 2), (1, 127, 1), (1, 143, 1), (1, 128, 1), (1, 144, 1), (1, 129, 1), (1, 145, 1), (1, 150, 1), (1, 98, 1), (1, 114, 1), (1, 155, 3), (1, 130, 1), (1, 146, 1), (1, 131, 1), (1, 147, 1), (1, 158, 6), (1, 170, 1), (1, 189, 2), (1, 164, 4), (1, 191, 6), (1, 171, 1), (1, 197, 1), (1, 172, 2), (1, 215, 2), (1, 198, 1), (1, 217, 5), (1, 240, 4), (1, 252, 4), (1, 262, 6), (1, 174, 2), (1, 199, 2), (1, 176, 2), (1, 201, 2), (1, 178, 1), (1, 203, 2), (1, 179, 1), (1, 205, 1), (1, 222, 2), (1, 168, 2), (1, 272, 1), (1, 224, 2), (1, 273, 2), (1, 226, 2), (1, 275, 2), (1, 228, 2), (1, 277, 2), (1, 180, 2), (1, 206, 2), (1, 182, 2), (1, 208, 2), (1, 184, 1), (1, 210, 1), (1, 185, 1), (1, 211, 1), (1, 230, 2)]
end CKLaneG3.S.C0.B10


