-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B10_q00_q02
-- name    : CK_CKLaneG3_S_C0_B10_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T23:07:32.729318+00:00
-- url     : https://prove2.me/theorems/1975ceb6-9d51-447c-8cef-30765563fb2b
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B10 (piece 1 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B10_q00_q01

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B10
open CKLaneD CKLaneG3
def r_50203001420_2 : List (ℕ × ℕ × ℕ) := [(1, 279, 2), (1, 232, 2), (1, 281, 2), (1, 234, 1), (1, 283, 2), (1, 235, 1), (1, 285, 1), (1, 244, 4), (1, 290, 1), (1, 309, 1), (1, 248, 4), (1, 291, 1), (1, 310, 1), (1, 328, 12), (1, 342, 1), (1, 340, 2), (1, 292, 2), (1, 311, 2), (1, 294, 2), (1, 313, 2), (1, 343, 8), (1, 296, 1), (1, 256, 2), (1, 297, 1), (1, 315, 1), (1, 298, 1), (1, 316, 1), (1, 299, 1), (1, 317, 1), (1, 258, 4), (1, 351, 2), (1, 268, 4), (1, 353, 2), (1, 300, 2), (1, 318, 2), (1, 302, 1), (1, 320, 2), (1, 355, 6), (1, 377, 1), (1, 385, 9), (1, 403, 5), (1, 422, 2), (1, 408, 2), (1, 424, 5), (1, 441, 1), (1, 429, 8), (1, 442, 8), (2, 379, 1), (2, 395, 2), (2, 380, 1), (2, 397, 1), (2, 405, 8), (2, 415, 4), (2, 381, 1), (2, 419, 1), (2, 382, 1), (2, 420, 1), (2, 383, 1), (2, 421, 1), (3, 0, 1), (3, 12, 4), (3, 1, 1), (3, 16, 1), (1, 394, 9), (1, 410, 12), (1, 437, 4), (4, 434, 2), (1, 450, 6), (4, 436, 1), (2, 384, 1), (2, 398, 1), (2, 385, 1), (2, 399, 1), (2, 386, 1), (2, 400, 1), (2, 387, 1), (2, 401, 1), (3, 2, 1), (2, 413, 2), (3, 3, 1), (4, 447, 1), (3, 4, 1), (4, 448, 1), (3, 5, 1), (4, 449, 1), (2, 388, 1), (2, 402, 1), (2, 389, 1), (2, 403, 1), (3, 6, 1), (4, 450, 1), (4, 453, 3), (2, 390, 1), (2, 422, 1), (4, 461, 1), (2, 391, 1), (2, 423, 1), (4, 462, 1), (3, 7, 1), (3, 17, 1)]
def r_50203001420_3 : List (ℕ × ℕ × ℕ) := [(3, 8, 1), (3, 18, 1), (3, 9, 1), (3, 19, 1), (4, 465, 1), (2, 392, 1), (2, 424, 1), (2, 393, 1), (2, 425, 1), (4, 466, 4), (2, 167, 1), (2, 174, 2), (2, 168, 1), (2, 176, 1), (2, 181, 4), (2, 190, 2), (2, 169, 2), (2, 177, 1), (2, 171, 1), (2, 178, 1), (2, 185, 1), (2, 192, 1), (2, 186, 1), (2, 193, 1), (2, 197, 2), (2, 209, 1), (2, 221, 3), (2, 229, 2), (2, 199, 1), (2, 210, 1), (2, 200, 1), (2, 211, 1), (2, 237, 6), (2, 246, 1), (2, 251, 1), (2, 256, 1), (2, 252, 1), (2, 257, 1), (2, 253, 1), (2, 258, 1), (2, 261, 2), (2, 243, 3), (2, 254, 1), (2, 259, 1), (2, 255, 1), (2, 260, 1), (2, 263, 8), (2, 275, 1), (2, 271, 2), (2, 276, 1), (2, 284, 2), (2, 289, 2), (2, 286, 1), (2, 291, 4), (2, 297, 4), (2, 311, 8), (2, 321, 5), (2, 331, 3), (2, 340, 1), (2, 343, 1), (2, 341, 1), (2, 344, 1), (2, 346, 1), (2, 349, 1), (2, 172, 1), (2, 179, 1), (2, 173, 1), (2, 180, 1), (2, 352, 2), (2, 187, 1), (2, 194, 1), (2, 188, 1), (2, 195, 1), (2, 354, 2), (2, 358, 4), (2, 189, 1), (2, 196, 1), (2, 362, 5), (2, 356, 2), (2, 367, 5), (2, 224, 1), (2, 231, 2), (2, 225, 1), (2, 233, 1), (2, 226, 1), (2, 234, 1), (3, 47, 1), (2, 201, 2), (2, 212, 2), (2, 203, 1), (2, 214, 2), (2, 204, 1), (2, 216, 1), (2, 205, 1), (2, 217, 1), (2, 227, 1), (2, 235, 1), (2, 228, 1), (2, 236, 1), (3, 51, 2)]
end CKLaneG3.S.C0.B10


