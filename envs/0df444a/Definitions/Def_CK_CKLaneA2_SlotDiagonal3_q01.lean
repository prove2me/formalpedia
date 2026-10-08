-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal3_q01
-- name    : CK_CKLaneA2_SlotDiagonal3_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T02:02:14.03837+00:00
-- url     : https://prove2.me/theorems/919c2839-dfff-407b-8a95-dfdd6d9d39a1
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal3 (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal3 (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal3 (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal3 (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal3 (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneA2_SlotDiagonal3_q00

namespace CKLaneA2.Diag3
open CKLaneA.Cell CKLaneA2
theorem n148_ok : treeOK (9 / 40 : ℚ) (1 / 4 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n148 = true :=
  treeOK_su (by decide +kernel) n149_ok n248_ok
def n2 : Tree := .su (9 / 40 : ℚ) n3 n148
theorem n2_ok : treeOK (1 / 5 : ℚ) (1 / 4 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n2 = true :=
  treeOK_su (by decide +kernel) n3_ok n148_ok
def n358 : Tree := .sr (3 / 80 : ℚ) n359 n390
theorem n358_ok : treeOK (1 / 4 : ℚ) (21 / 80 : ℚ) (0 : ℚ) (3 / 40 : ℚ) n358 = true :=
  treeOK_sr (by decide +kernel) n359_ok n390_ok
def n421 : Tree := .sr (9 / 80 : ℚ) n422 n453
theorem n421_ok : treeOK (1 / 4 : ℚ) (21 / 80 : ℚ) (3 / 40 : ℚ) (3 / 20 : ℚ) n421 = true :=
  treeOK_sr (by decide +kernel) n422_ok n453_ok
def n357 : Tree := .sr (3 / 40 : ℚ) n358 n421
theorem n357_ok : treeOK (1 / 4 : ℚ) (21 / 80 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n357 = true :=
  treeOK_sr (by decide +kernel) n358_ok n421_ok
def n508 : Tree := .su (27 / 100 : ℚ) n509 n526
theorem n508_ok : treeOK (107 / 400 : ℚ) (11 / 40 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n508 = true :=
  treeOK_su (by decide +kernel) n509_ok n526_ok
def n472 : Tree := .su (107 / 400 : ℚ) n473 n508
theorem n472_ok : treeOK (21 / 80 : ℚ) (11 / 40 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n472 = true :=
  treeOK_su (by decide +kernel) n473_ok n508_ok
def n356 : Tree := .su (21 / 80 : ℚ) n357 n472
theorem n356_ok : treeOK (1 / 4 : ℚ) (11 / 40 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n356 = true :=
  treeOK_su (by decide +kernel) n357_ok n472_ok
def n606 : Tree := .su (113 / 400 : ℚ) n607 n628
theorem n606_ok : treeOK (7 / 25 : ℚ) (23 / 80 : ℚ) (0 : ℚ) (3 / 20 : ℚ) n606 = true :=
  treeOK_su (by decide +kernel) n607_ok n628_ok
end CKLaneA2.Diag3


