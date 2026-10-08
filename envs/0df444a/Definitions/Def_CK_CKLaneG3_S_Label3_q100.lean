-- Prove2me | Definitions.Def_CK_CKLaneG3_S_Label3_q100
-- name    : CK_CKLaneG3_S_Label3_q100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T00:10:25.545917+00:00
-- url     : https://prove2.me/theorems/028cc336-5758-4ac7-aeab-8a59be281e32
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.Label3 (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.Label3 (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.Label3 (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.Label3 (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/Label3 (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneG3_S_Label3_q01


set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.Label3
open CKLaneD CKLaneG3 CKLaneG3.S
def runs4 : List (ℕ × ℕ × ℕ) := [(6, 12, 1), (6, 18, 19), (9, 32, 18), (10, 10, 12), (2, 18, 10), (3, 48, 2), (4, 0, 15), (6, 8, 4), (6, 37, 9), (0, 0, 8), (0, 36, 14), (1, 0, 38), (2, 45, 5), (3, 0, 19), (2, 28, 13), (3, 20, 28), (0, 8, 28), (1, 38, 12), (2, 0, 18)]

end CKLaneG3.S.Label3


