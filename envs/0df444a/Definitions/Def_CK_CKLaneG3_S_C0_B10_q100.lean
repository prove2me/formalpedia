-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B10_q100
-- name    : CK_CKLaneG3_S_C0_B10_q100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T00:58:27.937898+00:00
-- url     : https://prove2.me/theorems/b51319b7-78b2-4789-b9f7-e7445aebd7cf
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B10 (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B10 (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B10 (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B10 (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B10 (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B10_q02


set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B10
open CKLaneD CKLaneG3
def r_50203001430_1 : List (ℕ × ℕ × ℕ) := [(10, 218, 4), (10, 226, 3), (10, 234, 1), (10, 241, 7), (10, 252, 4), (10, 258, 3), (10, 263, 2), (10, 271, 2), (10, 265, 1), (10, 273, 2), (10, 279, 4), (11, 0, 4), (11, 6, 2), (11, 12, 2), (11, 8, 2), (11, 14, 2), (11, 10, 1), (11, 16, 1), (11, 11, 1), (11, 17, 3), (11, 22, 4), (11, 20, 2), (11, 26, 4), (11, 32, 1), (11, 30, 1), (11, 33, 2), (11, 37, 2), (11, 40, 4), (11, 46, 2), (11, 44, 2), (11, 50, 1), (11, 48, 1), (11, 52, 2), (11, 60, 3), (11, 67, 2), (11, 75, 1), (13, 50, 4), (13, 56, 2), (13, 60, 2), (13, 64, 3), (13, 69, 4), (13, 75, 2), (13, 82, 1), (13, 86, 1), (13, 90, 2), (13, 93, 2), (13, 96, 1), (13, 99, 2), (9, 17, 1), (9, 21, 1), (9, 25, 1)]
end CKLaneG3.S.C0.B10


