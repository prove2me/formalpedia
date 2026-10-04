-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q00_q01
-- name    : CK_CKLaneA2_SlotDiagonal4_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:57:29.141199+00:00
-- url     : https://prove2.me/theorems/67aa1a38-3711-428d-a6c3-a982261a7504
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal4 (piece 1 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal4 (piece 1 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal4 (piece 1 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal4 (piece 1 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal4 (piece 1 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneA2_Diag4_M06
import Definitions.Def_CK_CKLaneA2_Diag4_M07
import Definitions.Def_CK_CKLaneA2_Diag4_M08
import Definitions.Def_CK_CKLaneA2_Diag4_M09
import Definitions.Def_CK_CKLaneA2_Diag4_M10
import Definitions.Def_CK_CKLaneA2_Diag4_M11
import Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q00_q00

namespace CKLaneA2.Diag4
open CKLaneA.Cell CKLaneA2
theorem n165_ok : treeOK (249 / 800 : ℚ) (63 / 200 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n165 = true :=
  treeOK_su (by decide +kernel) n166_ok n195_ok
def n109 : Tree := .su (249 / 800 : ℚ) n110 n165
theorem n109_ok : treeOK (123 / 400 : ℚ) (63 / 200 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n109 = true :=
  treeOK_su (by decide +kernel) n110_ok n165_ok
def n3 : Tree := .su (123 / 400 : ℚ) n4 n109
theorem n3_ok : treeOK (3 / 10 : ℚ) (63 / 200 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n3 = true :=
  treeOK_su (by decide +kernel) n4_ok n109_ok
def n226 : Tree := .su (507 / 1600 : ℚ) n227 n258
theorem n226_ok : treeOK (63 / 200 : ℚ) (51 / 160 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n226 = true :=
  treeOK_su (by decide +kernel) n227_ok n258_ok
def n289 : Tree := .su (513 / 1600 : ℚ) n290 n323
theorem n289_ok : treeOK (51 / 160 : ℚ) (129 / 400 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n289 = true :=
  treeOK_su (by decide +kernel) n290_ok n323_ok
end CKLaneA2.Diag4


