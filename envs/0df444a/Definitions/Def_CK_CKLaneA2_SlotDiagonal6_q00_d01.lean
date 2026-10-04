-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q00_d01
-- name    : CK_CKLaneA2_SlotDiagonal6_q00_d01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T04:08:20.276557+00:00
-- url     : https://prove2.me/theorems/cad57929-abe0-4281-b5fd-60d44636c91a
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

import Definitions.Def_CK_CKLaneA2_Diag6_M01
import Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q00_d00
namespace CKLaneA2.Diag6
open CKLaneA.Cell CKLaneA2

def n5 : Tree := .sr (3 / 40 : ℚ) n6 n61

theorem n5_ok : treeOK (37 / 100 : ℚ) (297 / 800 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n5 = true :=
  treeOK_sr (by decide +kernel) n6_ok n61_ok

end CKLaneA2.Diag6


