-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q00_d09
-- name    : CK_CKLaneA2_SlotDiagonal6_q00_d09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T04:14:04.514293+00:00
-- url     : https://prove2.me/theorems/c7b85cdf-43a0-4149-b47b-d60b04290d7c
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal6 (piece)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal6 (piece)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal6 (piece)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal6 (piece) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal6 (piece).lean)

import Definitions.Def_CK_CKLaneA2_Diag6_M09
import Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q00_d08
namespace CKLaneA2.Diag6
open CKLaneA.Cell CKLaneA2

def n207 : Tree := .sr (3 / 20 : ℚ) n208 n289

theorem n207_ok : treeOK (149 / 400 : ℚ) (299 / 800 : ℚ) (0 : ℚ) (3 / 10 : ℚ) n207 = true :=
  treeOK_sr (by decide +kernel) n208_ok n289_ok

end CKLaneA2.Diag6


