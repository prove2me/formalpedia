-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C002
-- name    : CK_CKLaneA1_FEData_C002
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T22:20:53.357065+00:00
-- url     : https://prove2.me/theorems/565062a6-ea24-4363-863e-d4d9ab9852a0
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEData.C002` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEData.C002` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEData.C002` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEData.C002 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEData/C002.lean)

import Definitions.Def_CK_CKLaneA1_FEData_C002_part00

/-! Generated fixedEdge cover chunk 2 (137 cells, 4 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips002_s0 : FEStrip := ⟨⟨9007199254740992, 10, 0⟩, ⟨18014398509481984, 9, 0⟩, ⟨461168601842738790, 5, 0⟩, strips002_s0_c0 ++ strips002_s0_c1⟩

set_option maxRecDepth 1000000 in
theorem strips002_s0_head : (stripOKu 22 (ln2Iv 22) strips002_s0 && nodeOK strips002_s0.w0 && decide (40 * strips002_s0.w0.xa ≤ SCz) && decide ((lastNode strips002_s0.w0 strips002_s0.cells).xa = SCz / 2) && decide (strips002_s0.cells ≠ [])) = true := by decide +kernel

theorem strips002_s0_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨9007199254740992, 10, 0⟩, ⟨18014398509481984, 9, 0⟩, ⟨461168601842738790, 5, 0⟩, strips002_s0_c0 ++ strips002_s0_c1⟩ (⟨461168601842738790, 5, 0⟩) (strips002_s0_c0 ++ strips002_s0_c1) = true := by
  rw [cellsCheck_append, ← strips002_s0_c1_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨9007199254740992, 10, 0⟩ ⟨18014398509481984, 9, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips002_s0_c0 ++ strips002_s0_c1), strips002_s0_c0_ok, strips002_s0_c1_ok, Bool.and_self]

theorem strips002_s0_ok : stripOK 22 (ln2Iv 22) strips002_s0 = true :=
  stripOK_of_parts strips002_s0 strips002_s0_head strips002_s0_cells

def strips002_s1 : FEStrip := ⟨⟨18014398509481984, 9, 0⟩, ⟨36028797018963968, 8, 0⟩, ⟨461168601842738790, 5, 0⟩, strips002_s1_c0 ++ strips002_s1_c1 ++ strips002_s1_c2⟩

set_option maxRecDepth 1000000 in
theorem strips002_s1_head : (stripOKu 22 (ln2Iv 22) strips002_s1 && nodeOK strips002_s1.w0 && decide (40 * strips002_s1.w0.xa ≤ SCz) && decide ((lastNode strips002_s1.w0 strips002_s1.cells).xa = SCz / 2) && decide (strips002_s1.cells ≠ [])) = true := by decide +kernel

theorem strips002_s1_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨18014398509481984, 9, 0⟩, ⟨36028797018963968, 8, 0⟩, ⟨461168601842738790, 5, 0⟩, strips002_s1_c0 ++ strips002_s1_c1 ++ strips002_s1_c2⟩ (⟨461168601842738790, 5, 0⟩) (strips002_s1_c0 ++ strips002_s1_c1 ++ strips002_s1_c2) = true := by
  rw [cellsCheck_append, cellsCheck_append, ← strips002_s1_c1_start, ← strips002_s1_c2_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨18014398509481984, 9, 0⟩ ⟨36028797018963968, 8, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips002_s1_c0 ++ strips002_s1_c1 ++ strips002_s1_c2), strips002_s1_c0_ok, strips002_s1_c1_ok, strips002_s1_c2_ok, Bool.and_self]

theorem strips002_s1_ok : stripOK 22 (ln2Iv 22) strips002_s1 = true :=
  stripOK_of_parts strips002_s1 strips002_s1_head strips002_s1_cells

def strips002_s2 : FEStrip := ⟨⟨36028797018963968, 8, 0⟩, ⟨54043195528445952, 8, 0⟩, ⟨461168601842738790, 5, 0⟩, strips002_s2_c0 ++ strips002_s2_c1 ++ strips002_s2_c2⟩

set_option maxRecDepth 1000000 in
theorem strips002_s2_head : (stripOKu 22 (ln2Iv 22) strips002_s2 && nodeOK strips002_s2.w0 && decide (40 * strips002_s2.w0.xa ≤ SCz) && decide ((lastNode strips002_s2.w0 strips002_s2.cells).xa = SCz / 2) && decide (strips002_s2.cells ≠ [])) = true := by decide +kernel

theorem strips002_s2_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨36028797018963968, 8, 0⟩, ⟨54043195528445952, 8, 0⟩, ⟨461168601842738790, 5, 0⟩, strips002_s2_c0 ++ strips002_s2_c1 ++ strips002_s2_c2⟩ (⟨461168601842738790, 5, 0⟩) (strips002_s2_c0 ++ strips002_s2_c1 ++ strips002_s2_c2) = true := by
  rw [cellsCheck_append, cellsCheck_append, ← strips002_s2_c1_start, ← strips002_s2_c2_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨36028797018963968, 8, 0⟩ ⟨54043195528445952, 8, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips002_s2_c0 ++ strips002_s2_c1 ++ strips002_s2_c2), strips002_s2_c0_ok, strips002_s2_c1_ok, strips002_s2_c2_ok, Bool.and_self]

theorem strips002_s2_ok : stripOK 22 (ln2Iv 22) strips002_s2 = true :=
  stripOK_of_parts strips002_s2 strips002_s2_head strips002_s2_cells

def strips002_s3 : FEStrip := ⟨⟨54043195528445952, 8, 0⟩, ⟨72057594037927936, 7, 0⟩, ⟨461168601842738790, 5, 0⟩, strips002_s3_c0 ++ strips002_s3_c1 ++ strips002_s3_c2⟩

set_option maxRecDepth 1000000 in
theorem strips002_s3_head : (stripOKu 22 (ln2Iv 22) strips002_s3 && nodeOK strips002_s3.w0 && decide (40 * strips002_s3.w0.xa ≤ SCz) && decide ((lastNode strips002_s3.w0 strips002_s3.cells).xa = SCz / 2) && decide (strips002_s3.cells ≠ [])) = true := by decide +kernel

theorem strips002_s3_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨54043195528445952, 8, 0⟩, ⟨72057594037927936, 7, 0⟩, ⟨461168601842738790, 5, 0⟩, strips002_s3_c0 ++ strips002_s3_c1 ++ strips002_s3_c2⟩ (⟨461168601842738790, 5, 0⟩) (strips002_s3_c0 ++ strips002_s3_c1 ++ strips002_s3_c2) = true := by
  rw [cellsCheck_append, cellsCheck_append, ← strips002_s3_c1_start, ← strips002_s3_c2_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨54043195528445952, 8, 0⟩ ⟨72057594037927936, 7, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips002_s3_c0 ++ strips002_s3_c1 ++ strips002_s3_c2), strips002_s3_c0_ok, strips002_s3_c1_ok, strips002_s3_c2_ok, Bool.and_self]

theorem strips002_s3_ok : stripOK 22 (ln2Iv 22) strips002_s3 = true :=
  stripOK_of_parts strips002_s3 strips002_s3_head strips002_s3_cells

def strips002 : List FEStrip := [strips002_s0, strips002_s1, strips002_s2, strips002_s3]

theorem strips002_ok : strips002.all (stripOK 22 (ln2Iv 22)) = true := by
  simp only [strips002, List.all_cons, List.all_nil, strips002_s0_ok, strips002_s1_ok, strips002_s2_ok, strips002_s3_ok, Bool.and_true]

end CKLaneA1.FEData


