-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q00_q00
-- name    : CK_CKLaneA2_SlotDiagonal4_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:00:44.594013+00:00
-- url     : https://prove2.me/theorems/47e07a73-29a3-44e0-ad73-53bf643d738b
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal4 (piece 1 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal4 (piece 1 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal4 (piece 1 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal4 (piece 1 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal4 (piece 1 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneA2_Diag4_M04
import Definitions.Def_CK_CKLaneA2_Diag4_M05
import Definitions.Def_CK_CKLaneA2_Diag4_M06
import Definitions.Def_CK_CKLaneA2_Diag4_M07
import Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q00_q00_q01

namespace CKLaneA2.Diag4
open CKLaneA.Cell CKLaneA2
def n110 : Tree := .su (99 / 320 : ℚ) n111 n138
theorem n110_ok : treeOK (123 / 400 : ℚ) (249 / 800 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n110 = true :=
  treeOK_su (by decide +kernel) n111_ok n138_ok
def n165 : Tree := .su (501 / 1600 : ℚ) n166 n195
end CKLaneA2.Diag4


