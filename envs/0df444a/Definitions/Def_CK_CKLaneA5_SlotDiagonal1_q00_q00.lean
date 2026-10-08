-- Prove2me | Definitions.Def_CK_CKLaneA5_SlotDiagonal1_q00_q00
-- name    : CK_CKLaneA5_SlotDiagonal1_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T22:56:27.897983+00:00
-- url     : https://prove2.me/theorems/f0867bf9-1cb2-42fa-839a-8266aec43132
-- title:
--   Courtade–Kumar proof module `CKLaneA5.SlotDiagonal1 (piece 1 of 4) (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA5.SlotDiagonal1 (piece 1 of 4) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA5.SlotDiagonal1 (piece 1 of 4) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA5.SlotDiagonal1 (piece 1 of 4) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/SlotDiagonal1 (piece 1 of 4) (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneA5_SlotDiagonal1_q00_q00_q02

namespace CKLaneA5.Diag1
open CKLaneA.Cell CKLaneA5
theorem n53_ok : treeOK (1 / 40 : ℚ) (3 / 100 : ℚ) (0 : ℚ) (3 / 80 : ℚ) n53 = true :=
  treeOK_sr (by decide +kernel) n54_ok n71_ok
end CKLaneA5.Diag1


