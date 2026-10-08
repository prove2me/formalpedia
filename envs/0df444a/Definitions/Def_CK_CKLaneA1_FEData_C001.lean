-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C001
-- name    : CK_CKLaneA1_FEData_C001
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T06:27:43.07837+00:00
-- url     : https://prove2.me/theorems/5d9aaacb-e681-43c1-bdae-3937850821d2
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEData.C001` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEData.C001` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEData.C001` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEData.C001 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEData/C001.lean)

import Definitions.Def_CK_CKLaneA1_FEData_C001_part00

/-! Generated fixedEdge cover chunk 1 (141 cells, 12 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips001_s0 : FEStrip := ⟨⟨2199023255552, 22, 0⟩, ⟨4398046511104, 21, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s0_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s0_head : (stripOKu 22 (ln2Iv 22) strips001_s0 && nodeOK strips001_s0.w0 && decide (40 * strips001_s0.w0.xa ≤ SCz) && decide ((lastNode strips001_s0.w0 strips001_s0.cells).xa = SCz / 2) && decide (strips001_s0.cells ≠ [])) = true := by decide +kernel

theorem strips001_s0_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨2199023255552, 22, 0⟩, ⟨4398046511104, 21, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s0_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s0_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨2199023255552, 22, 0⟩ ⟨4398046511104, 21, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s0_c0), strips001_s0_c0_ok, Bool.and_self]

theorem strips001_s0_ok : stripOK 22 (ln2Iv 22) strips001_s0 = true :=
  stripOK_of_parts strips001_s0 strips001_s0_head strips001_s0_cells

def strips001_s1 : FEStrip := ⟨⟨4398046511104, 21, 0⟩, ⟨8796093022208, 20, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s1_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s1_head : (stripOKu 22 (ln2Iv 22) strips001_s1 && nodeOK strips001_s1.w0 && decide (40 * strips001_s1.w0.xa ≤ SCz) && decide ((lastNode strips001_s1.w0 strips001_s1.cells).xa = SCz / 2) && decide (strips001_s1.cells ≠ [])) = true := by decide +kernel

theorem strips001_s1_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨4398046511104, 21, 0⟩, ⟨8796093022208, 20, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s1_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s1_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨4398046511104, 21, 0⟩ ⟨8796093022208, 20, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s1_c0), strips001_s1_c0_ok, Bool.and_self]

theorem strips001_s1_ok : stripOK 22 (ln2Iv 22) strips001_s1 = true :=
  stripOK_of_parts strips001_s1 strips001_s1_head strips001_s1_cells

def strips001_s2 : FEStrip := ⟨⟨8796093022208, 20, 0⟩, ⟨17592186044416, 19, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s2_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s2_head : (stripOKu 22 (ln2Iv 22) strips001_s2 && nodeOK strips001_s2.w0 && decide (40 * strips001_s2.w0.xa ≤ SCz) && decide ((lastNode strips001_s2.w0 strips001_s2.cells).xa = SCz / 2) && decide (strips001_s2.cells ≠ [])) = true := by decide +kernel

theorem strips001_s2_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨8796093022208, 20, 0⟩, ⟨17592186044416, 19, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s2_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s2_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨8796093022208, 20, 0⟩ ⟨17592186044416, 19, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s2_c0), strips001_s2_c0_ok, Bool.and_self]

theorem strips001_s2_ok : stripOK 22 (ln2Iv 22) strips001_s2 = true :=
  stripOK_of_parts strips001_s2 strips001_s2_head strips001_s2_cells

def strips001_s3 : FEStrip := ⟨⟨17592186044416, 19, 0⟩, ⟨35184372088832, 18, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s3_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s3_head : (stripOKu 22 (ln2Iv 22) strips001_s3 && nodeOK strips001_s3.w0 && decide (40 * strips001_s3.w0.xa ≤ SCz) && decide ((lastNode strips001_s3.w0 strips001_s3.cells).xa = SCz / 2) && decide (strips001_s3.cells ≠ [])) = true := by decide +kernel

theorem strips001_s3_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨17592186044416, 19, 0⟩, ⟨35184372088832, 18, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s3_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s3_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨17592186044416, 19, 0⟩ ⟨35184372088832, 18, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s3_c0), strips001_s3_c0_ok, Bool.and_self]

theorem strips001_s3_ok : stripOK 22 (ln2Iv 22) strips001_s3 = true :=
  stripOK_of_parts strips001_s3 strips001_s3_head strips001_s3_cells

def strips001_s4 : FEStrip := ⟨⟨35184372088832, 18, 0⟩, ⟨70368744177664, 17, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s4_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s4_head : (stripOKu 22 (ln2Iv 22) strips001_s4 && nodeOK strips001_s4.w0 && decide (40 * strips001_s4.w0.xa ≤ SCz) && decide ((lastNode strips001_s4.w0 strips001_s4.cells).xa = SCz / 2) && decide (strips001_s4.cells ≠ [])) = true := by decide +kernel

theorem strips001_s4_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨35184372088832, 18, 0⟩, ⟨70368744177664, 17, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s4_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s4_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨35184372088832, 18, 0⟩ ⟨70368744177664, 17, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s4_c0), strips001_s4_c0_ok, Bool.and_self]

theorem strips001_s4_ok : stripOK 22 (ln2Iv 22) strips001_s4 = true :=
  stripOK_of_parts strips001_s4 strips001_s4_head strips001_s4_cells

def strips001_s5 : FEStrip := ⟨⟨70368744177664, 17, 0⟩, ⟨140737488355328, 16, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s5_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s5_head : (stripOKu 22 (ln2Iv 22) strips001_s5 && nodeOK strips001_s5.w0 && decide (40 * strips001_s5.w0.xa ≤ SCz) && decide ((lastNode strips001_s5.w0 strips001_s5.cells).xa = SCz / 2) && decide (strips001_s5.cells ≠ [])) = true := by decide +kernel

theorem strips001_s5_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨70368744177664, 17, 0⟩, ⟨140737488355328, 16, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s5_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s5_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨70368744177664, 17, 0⟩ ⟨140737488355328, 16, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s5_c0), strips001_s5_c0_ok, Bool.and_self]

theorem strips001_s5_ok : stripOK 22 (ln2Iv 22) strips001_s5 = true :=
  stripOK_of_parts strips001_s5 strips001_s5_head strips001_s5_cells

def strips001_s6 : FEStrip := ⟨⟨140737488355328, 16, 0⟩, ⟨281474976710656, 15, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s6_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s6_head : (stripOKu 22 (ln2Iv 22) strips001_s6 && nodeOK strips001_s6.w0 && decide (40 * strips001_s6.w0.xa ≤ SCz) && decide ((lastNode strips001_s6.w0 strips001_s6.cells).xa = SCz / 2) && decide (strips001_s6.cells ≠ [])) = true := by decide +kernel

theorem strips001_s6_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨140737488355328, 16, 0⟩, ⟨281474976710656, 15, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s6_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s6_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨140737488355328, 16, 0⟩ ⟨281474976710656, 15, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s6_c0), strips001_s6_c0_ok, Bool.and_self]

theorem strips001_s6_ok : stripOK 22 (ln2Iv 22) strips001_s6 = true :=
  stripOK_of_parts strips001_s6 strips001_s6_head strips001_s6_cells

def strips001_s7 : FEStrip := ⟨⟨281474976710656, 15, 0⟩, ⟨562949953421312, 14, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s7_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s7_head : (stripOKu 22 (ln2Iv 22) strips001_s7 && nodeOK strips001_s7.w0 && decide (40 * strips001_s7.w0.xa ≤ SCz) && decide ((lastNode strips001_s7.w0 strips001_s7.cells).xa = SCz / 2) && decide (strips001_s7.cells ≠ [])) = true := by decide +kernel

theorem strips001_s7_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨281474976710656, 15, 0⟩, ⟨562949953421312, 14, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s7_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s7_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨281474976710656, 15, 0⟩ ⟨562949953421312, 14, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s7_c0), strips001_s7_c0_ok, Bool.and_self]

theorem strips001_s7_ok : stripOK 22 (ln2Iv 22) strips001_s7 = true :=
  stripOK_of_parts strips001_s7 strips001_s7_head strips001_s7_cells

def strips001_s8 : FEStrip := ⟨⟨562949953421312, 14, 0⟩, ⟨1125899906842624, 13, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s8_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s8_head : (stripOKu 22 (ln2Iv 22) strips001_s8 && nodeOK strips001_s8.w0 && decide (40 * strips001_s8.w0.xa ≤ SCz) && decide ((lastNode strips001_s8.w0 strips001_s8.cells).xa = SCz / 2) && decide (strips001_s8.cells ≠ [])) = true := by decide +kernel

theorem strips001_s8_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨562949953421312, 14, 0⟩, ⟨1125899906842624, 13, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s8_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s8_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨562949953421312, 14, 0⟩ ⟨1125899906842624, 13, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s8_c0), strips001_s8_c0_ok, Bool.and_self]

theorem strips001_s8_ok : stripOK 22 (ln2Iv 22) strips001_s8 = true :=
  stripOK_of_parts strips001_s8 strips001_s8_head strips001_s8_cells

def strips001_s9 : FEStrip := ⟨⟨1125899906842624, 13, 0⟩, ⟨2251799813685248, 12, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s9_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s9_head : (stripOKu 22 (ln2Iv 22) strips001_s9 && nodeOK strips001_s9.w0 && decide (40 * strips001_s9.w0.xa ≤ SCz) && decide ((lastNode strips001_s9.w0 strips001_s9.cells).xa = SCz / 2) && decide (strips001_s9.cells ≠ [])) = true := by decide +kernel

theorem strips001_s9_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨1125899906842624, 13, 0⟩, ⟨2251799813685248, 12, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s9_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s9_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨1125899906842624, 13, 0⟩ ⟨2251799813685248, 12, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s9_c0), strips001_s9_c0_ok, Bool.and_self]

theorem strips001_s9_ok : stripOK 22 (ln2Iv 22) strips001_s9 = true :=
  stripOK_of_parts strips001_s9 strips001_s9_head strips001_s9_cells

def strips001_s10 : FEStrip := ⟨⟨2251799813685248, 12, 0⟩, ⟨4503599627370496, 11, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s10_c0⟩

set_option maxRecDepth 1000000 in
theorem strips001_s10_head : (stripOKu 22 (ln2Iv 22) strips001_s10 && nodeOK strips001_s10.w0 && decide (40 * strips001_s10.w0.xa ≤ SCz) && decide ((lastNode strips001_s10.w0 strips001_s10.cells).xa = SCz / 2) && decide (strips001_s10.cells ≠ [])) = true := by decide +kernel

theorem strips001_s10_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨2251799813685248, 12, 0⟩, ⟨4503599627370496, 11, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s10_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s10_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨2251799813685248, 12, 0⟩ ⟨4503599627370496, 11, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s10_c0), strips001_s10_c0_ok, Bool.and_self]

theorem strips001_s10_ok : stripOK 22 (ln2Iv 22) strips001_s10 = true :=
  stripOK_of_parts strips001_s10 strips001_s10_head strips001_s10_cells

def strips001_s11 : FEStrip := ⟨⟨4503599627370496, 11, 0⟩, ⟨9007199254740992, 10, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s11_c0 ++ strips001_s11_c1⟩

set_option maxRecDepth 1000000 in
theorem strips001_s11_head : (stripOKu 22 (ln2Iv 22) strips001_s11 && nodeOK strips001_s11.w0 && decide (40 * strips001_s11.w0.xa ≤ SCz) && decide ((lastNode strips001_s11.w0 strips001_s11.cells).xa = SCz / 2) && decide (strips001_s11.cells ≠ [])) = true := by decide +kernel

theorem strips001_s11_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨4503599627370496, 11, 0⟩, ⟨9007199254740992, 10, 0⟩, ⟨461168601842738790, 5, 0⟩, strips001_s11_c0 ++ strips001_s11_c1⟩ (⟨461168601842738790, 5, 0⟩) (strips001_s11_c0 ++ strips001_s11_c1) = true := by
  rw [cellsCheck_append, ← strips001_s11_c1_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨4503599627370496, 11, 0⟩ ⟨9007199254740992, 10, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips001_s11_c0 ++ strips001_s11_c1), strips001_s11_c0_ok, strips001_s11_c1_ok, Bool.and_self]

theorem strips001_s11_ok : stripOK 22 (ln2Iv 22) strips001_s11 = true :=
  stripOK_of_parts strips001_s11 strips001_s11_head strips001_s11_cells

def strips001 : List FEStrip := [strips001_s0, strips001_s1, strips001_s2, strips001_s3, strips001_s4, strips001_s5, strips001_s6, strips001_s7, strips001_s8, strips001_s9, strips001_s10, strips001_s11]

theorem strips001_ok : strips001.all (stripOK 22 (ln2Iv 22)) = true := by
  simp only [strips001, List.all_cons, List.all_nil, strips001_s0_ok, strips001_s1_ok, strips001_s2_ok, strips001_s3_ok, strips001_s4_ok, strips001_s5_ok, strips001_s6_ok, strips001_s7_ok, strips001_s8_ok, strips001_s9_ok, strips001_s10_ok, strips001_s11_ok, Bool.and_true]

end CKLaneA1.FEData


