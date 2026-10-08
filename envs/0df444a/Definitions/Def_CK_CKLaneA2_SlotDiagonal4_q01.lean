-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q01
-- name    : CK_CKLaneA2_SlotDiagonal4_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T16:37:58.143381+00:00
-- url     : https://prove2.me/theorems/a1401c31-625b-49a1-8a4f-e71f3229661e
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal4 (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal4 (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal4 (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal4 (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal4 (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q01_q101

namespace CKLaneA2.Diag4
open CKLaneA.Cell CKLaneA2
theorem n500_ok : treeOK (33 / 100 : ℚ) (69 / 200 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n500 = true :=
  treeOK_su (by decide +kernel) n501_ok n660_ok
def n875 : Tree := .su (139 / 400 : ℚ) n876 n909
theorem n875_ok : treeOK (277 / 800 : ℚ) (279 / 800 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n875 = true :=
  treeOK_su (by decide +kernel) n876_ok n909_ok
end CKLaneA2.Diag4


