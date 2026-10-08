-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q01
-- name    : CK_CKLaneA2_SlotDiagonal6_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T17:32:14.543374+00:00
-- url     : https://prove2.me/theorems/2aa7a2f4-469c-4251-82bf-732dfd72f57a
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal6 (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal6 (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal6 (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal6 (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal6 (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneA2_Diag6_M12
import Definitions.Def_CK_CKLaneA2_Diag6_M13
import Definitions.Def_CK_CKLaneA2_Diag6_M14
import Definitions.Def_CK_CKLaneA2_Diag6_M15
import Definitions.Def_CK_CKLaneA2_Diag6_M16
import Definitions.Def_CK_CKLaneA2_Diag6_M17
import Definitions.Def_CK_CKLaneA2_Diag6_M18
import Definitions.Def_CK_CKLaneA2_Diag6_M19
import Definitions.Def_CK_CKLaneA2_Diag6_M20
import Definitions.Def_CK_CKLaneA2_Diag6_M21
import Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q00

namespace CKLaneA2.Diag6
open CKLaneA.Cell CKLaneA2
theorem n316_ok : treeOK (299 / 800 : ℚ) (3 / 8 : ℚ) (0 : ℚ) (3 / 40 : ℚ) n316 = true :=
  treeOK_sr (by decide +kernel) n317_ok n348_ok
def n315 : Tree := .sr (3 / 40 : ℚ) n316 n375
theorem n315_ok : treeOK (299 / 800 : ℚ) (3 / 8 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n315 = true :=
  treeOK_sr (by decide +kernel) n316_ok n375_ok
def n314 : Tree := .sr (3 / 20 : ℚ) n315 n398
theorem n314_ok : treeOK (299 / 800 : ℚ) (3 / 8 : ℚ) (0 : ℚ) (3 / 10 : ℚ) n314 = true :=
  treeOK_sr (by decide +kernel) n315_ok n398_ok
def n206 : Tree := .su (299 / 800 : ℚ) n207 n314
theorem n206_ok : treeOK (149 / 400 : ℚ) (3 / 8 : ℚ) (0 : ℚ) (3 / 10 : ℚ) n206 = true :=
  treeOK_su (by decide +kernel) n207_ok n314_ok
def n2 : Tree := .su (149 / 400 : ℚ) n3 n206
theorem n2_ok : treeOK (37 / 100 : ℚ) (3 / 8 : ℚ) (0 : ℚ) (3 / 10 : ℚ) n2 = true :=
  treeOK_su (by decide +kernel) n3_ok n206_ok
def n427 : Tree := .sr (3 / 80 : ℚ) n428 n459
theorem n427_ok : treeOK (3 / 8 : ℚ) (301 / 800 : ℚ) (0 : ℚ) (3 / 40 : ℚ) n427 = true :=
  treeOK_sr (by decide +kernel) n428_ok n459_ok
def n426 : Tree := .sr (3 / 40 : ℚ) n427 n488
theorem n426_ok : treeOK (3 / 8 : ℚ) (301 / 800 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n426 = true :=
  treeOK_sr (by decide +kernel) n427_ok n488_ok
def n425 : Tree := .sr (3 / 20 : ℚ) n426 n511
theorem n425_ok : treeOK (3 / 8 : ℚ) (301 / 800 : ℚ) (0 : ℚ) (3 / 10 : ℚ) n425 = true :=
  treeOK_sr (by decide +kernel) n426_ok n511_ok
def n540 : Tree := .sr (3 / 80 : ℚ) n541 n572
theorem n540_ok : treeOK (301 / 800 : ℚ) (151 / 400 : ℚ) (0 : ℚ) (3 / 40 : ℚ) n540 = true :=
  treeOK_sr (by decide +kernel) n541_ok n572_ok
def n539 : Tree := .sr (3 / 40 : ℚ) n540 n601
theorem n539_ok : treeOK (301 / 800 : ℚ) (151 / 400 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n539 = true :=
  treeOK_sr (by decide +kernel) n540_ok n601_ok
def n538 : Tree := .sr (3 / 20 : ℚ) n539 n626
theorem n538_ok : treeOK (301 / 800 : ℚ) (151 / 400 : ℚ) (0 : ℚ) (3 / 10 : ℚ) n538 = true :=
  treeOK_sr (by decide +kernel) n539_ok n626_ok
end CKLaneA2.Diag6


