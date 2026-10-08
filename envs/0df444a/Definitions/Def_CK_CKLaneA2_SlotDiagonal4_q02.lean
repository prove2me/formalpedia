-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q02
-- name    : CK_CKLaneA2_SlotDiagonal4_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T10:16:57.686099+00:00
-- url     : https://prove2.me/theorems/b087728a-a006-483d-a47a-eff369322856
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal4 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal4 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal4 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal4 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal4 (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneA2_Diag4_M28
import Definitions.Def_CK_CKLaneA2_Diag4_M31
import Definitions.Def_CK_CKLaneA2_Diag4_M32
import Definitions.Def_CK_CKLaneA2_Diag4_M33
import Definitions.Def_CK_CKLaneA2_Diag4_M34
import Definitions.Def_CK_CKLaneA2_Diag4_M35
import Definitions.Def_CK_CKLaneA2_Diag4_M36
import Definitions.Def_CK_CKLaneA2_Diag4_M37
import Definitions.Def_CK_CKLaneA2_Diag4_M38
import Definitions.Def_CK_CKLaneA2_Diag4_M39
import Definitions.Def_CK_CKLaneA2_Diag4_M40
import Definitions.Def_CK_CKLaneA2_SlotDiagonal4_q01

namespace CKLaneA2.Diag4
open CKLaneA.Cell CKLaneA2
def n843 : Tree := .su (277 / 800 : ℚ) n844 n875
theorem n843_ok : treeOK (69 / 200 : ℚ) (279 / 800 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n843 = true :=
  treeOK_su (by decide +kernel) n844_ok n875_ok
def n978 : Tree := .su (281 / 800 : ℚ) n979 n1014
theorem n978_ok : treeOK (7 / 20 : ℚ) (141 / 400 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n978 = true :=
  treeOK_su (by decide +kernel) n979_ok n1014_ok
def n942 : Tree := .su (7 / 20 : ℚ) n943 n978
theorem n942_ok : treeOK (279 / 800 : ℚ) (141 / 400 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n942 = true :=
  treeOK_su (by decide +kernel) n943_ok n978_ok
def n842 : Tree := .su (279 / 800 : ℚ) n843 n942
theorem n842_ok : treeOK (69 / 200 : ℚ) (141 / 400 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n842 = true :=
  treeOK_su (by decide +kernel) n843_ok n942_ok
def n1082 : Tree := .su (993 / 2800 : ℚ) n1083 n1116
theorem n1082_ok : treeOK (99 / 280 : ℚ) (249 / 700 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n1082 = true :=
  treeOK_su (by decide +kernel) n1083_ok n1116_ok
def n1050 : Tree := .su (99 / 280 : ℚ) n1051 n1082
theorem n1050_ok : treeOK (141 / 400 : ℚ) (249 / 700 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n1050 = true :=
  treeOK_su (by decide +kernel) n1051_ok n1082_ok
def n1150 : Tree := .su (999 / 2800 : ℚ) n1151 n1184
theorem n1150_ok : treeOK (249 / 700 : ℚ) (501 / 1400 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n1150 = true :=
  treeOK_su (by decide +kernel) n1151_ok n1184_ok
def n1219 : Tree := .su (201 / 560 : ℚ) n1220 n1255
theorem n1219_ok : treeOK (501 / 1400 : ℚ) (9 / 25 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n1219 = true :=
  treeOK_su (by decide +kernel) n1220_ok n1255_ok
def n1149 : Tree := .su (501 / 1400 : ℚ) n1150 n1219
theorem n1149_ok : treeOK (249 / 700 : ℚ) (9 / 25 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n1149 = true :=
  treeOK_su (by decide +kernel) n1150_ok n1219_ok
def n1049 : Tree := .su (249 / 700 : ℚ) n1050 n1149
theorem n1049_ok : treeOK (141 / 400 : ℚ) (9 / 25 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n1049 = true :=
  treeOK_su (by decide +kernel) n1050_ok n1149_ok
def n841 : Tree := .su (141 / 400 : ℚ) n842 n1049
theorem n841_ok : treeOK (69 / 200 : ℚ) (9 / 25 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n841 = true :=
  treeOK_su (by decide +kernel) n842_ok n1049_ok
def n499 : Tree := .su (69 / 200 : ℚ) n500 n841
theorem n499_ok : treeOK (33 / 100 : ℚ) (9 / 25 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n499 = true :=
  treeOK_su (by decide +kernel) n500_ok n841_ok
def n1 : Tree := .su (33 / 100 : ℚ) n2 n499
theorem n1_ok : treeOK (3 / 10 : ℚ) (9 / 25 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n1 = true :=
  treeOK_su (by decide +kernel) n2_ok n499_ok

theorem slotTree_ok : treeOK (3 / 10 : ℚ) (9 / 25 : ℚ) (0 : ℚ) (11 / 50 : ℚ) n1 = true := n1_ok

end CKLaneA2.Diag4


