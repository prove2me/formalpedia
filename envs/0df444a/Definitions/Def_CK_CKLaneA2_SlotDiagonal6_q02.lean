-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q02
-- name    : CK_CKLaneA2_SlotDiagonal6_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T03:46:53.117558+00:00
-- url     : https://prove2.me/theorems/92705d08-dc18-42a3-85e4-c579ece5081f
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal6 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal6 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal6 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal6 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal6 (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_CorrectionComplementCharts
import Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q02_q02

namespace CKLaneA2.Diag6
open CKLaneA.Cell CKLaneA2
theorem slotTree_ok : treeOK (37 / 100 : ℚ) (19 / 50 : ℚ) (0 : ℚ) (3 / 10 : ℚ) n1 = true := n1_ok

end CKLaneA2.Diag6

namespace CKLaneA2.Slots
open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement CKLaneA.Cell

end CKLaneA2.Slots


