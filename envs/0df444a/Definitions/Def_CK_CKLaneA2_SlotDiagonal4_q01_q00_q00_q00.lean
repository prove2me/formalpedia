-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q01_q00_q00_q00
-- name    : CK_CKLaneA2_SlotDiagonal4_q01_q00_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T05:45:46.290987+00:00
-- url     : https://prove2.me/theorems/398b7be6-a8ac-4d2a-82f2-e0f89cc38803
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal4 (piece 2 of 4) (piece 1 of 3) (piece 1 of 3) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal4 (piece 2 of 4) (piece 1 of 3) (piece 1 of 3) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal4 (piece 2 of 4) (piece 1 of 3) (piece 1 of 3) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal4 (piece 2 of 4) (piece 1 of 3) (piece 1 of 3) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal4 (piece 2 of 4) (piece 1 of 3) (piece 1 of 3) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q00




namespace CKLaneA2.Diag4
open CKLaneA.Cell CKLaneA2
theorem n356_ok : treeOK (129 / 400 : ℚ) (33 / 100 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n356 = true :=
  treeOK_su (by decide +kernel) n357_ok n412_ok
end CKLaneA2.Diag4


