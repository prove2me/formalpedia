-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q02_q00_q02
-- name    : CK_CKLaneA2_SlotDiagonal6_q02_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T14:21:52.537203+00:00
-- url     : https://prove2.me/theorems/a0879edf-5ca2-4d0f-9aa2-953ac20d00af
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal6 (piece 3 of 4) (piece 1 of 3) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal6 (piece 3 of 4) (piece 1 of 3) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal6 (piece 3 of 4) (piece 1 of 3) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal6 (piece 3 of 4) (piece 1 of 3) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal6 (piece 3 of 4) (piece 1 of 3) (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q02_q00_q01

namespace CKLaneA2.Diag6
open CKLaneA.Cell CKLaneA2
def n655 : Tree := .sr (3 / 40 : ℚ) n656 n719
theorem n655_ok : treeOK (151 / 400 : ℚ) (303 / 800 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n655 = true :=
  treeOK_sr (by decide +kernel) n656_ok n719_ok
end CKLaneA2.Diag6


