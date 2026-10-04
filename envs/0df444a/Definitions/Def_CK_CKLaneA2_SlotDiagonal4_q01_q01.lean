-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q01_q01
-- name    : CK_CKLaneA2_SlotDiagonal4_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T11:22:43.934068+00:00
-- url     : https://prove2.me/theorems/2b146687-eab0-47ce-8f8c-ed1ef5c04a87
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal4 (piece 2 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal4 (piece 2 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal4 (piece 2 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal4 (piece 2 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal4 (piece 2 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneA2_Diag4_M19
import Definitions.Def_CK_CKLaneA2_Diag4_M22
import Definitions.Def_CK_CKLaneA2_Diag4_M23
import Definitions.Def_CK_CKLaneA2_Diag4_M24
import Definitions.Def_CK_CKLaneA2_Diag4_M26
import Definitions.Def_CK_CKLaneA2_Diag4_M27
import Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q01_q00

namespace CKLaneA2.Diag4
open CKLaneA.Cell CKLaneA2
def n563 : Tree := .su (669 / 2000 : ℚ) n564 n595
theorem n563_ok : treeOK (333 / 1000 : ℚ) (27 / 80 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n563 = true :=
  treeOK_su (by decide +kernel) n564_ok n595_ok
def n501 : Tree := .su (333 / 1000 : ℚ) n502 n563
theorem n501_ok : treeOK (33 / 100 : ℚ) (27 / 80 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n501 = true :=
  treeOK_su (by decide +kernel) n502_ok n563_ok
def n689 : Tree := .su (17 / 50 : ℚ) n690 n719
theorem n689_ok : treeOK (271 / 800 : ℚ) (273 / 800 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n689 = true :=
  treeOK_su (by decide +kernel) n690_ok n719_ok
def n661 : Tree := .su (271 / 800 : ℚ) n662 n689
theorem n661_ok : treeOK (27 / 80 : ℚ) (273 / 800 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n661 = true :=
  treeOK_su (by decide +kernel) n662_ok n689_ok
def n778 : Tree := .su (11 / 32 : ℚ) n779 n810
end CKLaneA2.Diag4


