-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C000
-- name    : CK_CKLaneA1_FEData_C000
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:28:58.658911+00:00
-- url     : https://prove2.me/theorems/44858351-2ec1-4d83-8e7d-43082706dbac
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEData.C000` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEData.C000` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEData.C000` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEData.C000 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEData/C000.lean)

import Definitions.Def_CK_CKLaneA1_FEData_C000_part00

/-! Generated fixedEdge cover chunk 0 (145 cells, 18 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips000_s0 : FEStrip := ⟨⟨0, 0, 0⟩, ⟨16777216, 39, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s0_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s0_head : (stripOKu 22 (ln2Iv 22) strips000_s0 && nodeOK strips000_s0.w0 && decide (40 * strips000_s0.w0.xa ≤ SCz) && decide ((lastNode strips000_s0.w0 strips000_s0.cells).xa = SCz / 2) && decide (strips000_s0.cells ≠ [])) = true := by decide +kernel

theorem strips000_s0_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨0, 0, 0⟩, ⟨16777216, 39, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s0_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s0_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨0, 0, 0⟩ ⟨16777216, 39, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s0_c0), strips000_s0_c0_ok, Bool.and_self]

theorem strips000_s0_ok : stripOK 22 (ln2Iv 22) strips000_s0 = true :=
  stripOK_of_parts strips000_s0 strips000_s0_head strips000_s0_cells

def strips000_s1 : FEStrip := ⟨⟨16777216, 39, 0⟩, ⟨33554432, 38, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s1_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s1_head : (stripOKu 22 (ln2Iv 22) strips000_s1 && nodeOK strips000_s1.w0 && decide (40 * strips000_s1.w0.xa ≤ SCz) && decide ((lastNode strips000_s1.w0 strips000_s1.cells).xa = SCz / 2) && decide (strips000_s1.cells ≠ [])) = true := by decide +kernel

theorem strips000_s1_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨16777216, 39, 0⟩, ⟨33554432, 38, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s1_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s1_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨16777216, 39, 0⟩ ⟨33554432, 38, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s1_c0), strips000_s1_c0_ok, Bool.and_self]

theorem strips000_s1_ok : stripOK 22 (ln2Iv 22) strips000_s1 = true :=
  stripOK_of_parts strips000_s1 strips000_s1_head strips000_s1_cells

def strips000_s2 : FEStrip := ⟨⟨33554432, 38, 0⟩, ⟨67108864, 37, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s2_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s2_head : (stripOKu 22 (ln2Iv 22) strips000_s2 && nodeOK strips000_s2.w0 && decide (40 * strips000_s2.w0.xa ≤ SCz) && decide ((lastNode strips000_s2.w0 strips000_s2.cells).xa = SCz / 2) && decide (strips000_s2.cells ≠ [])) = true := by decide +kernel

theorem strips000_s2_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨33554432, 38, 0⟩, ⟨67108864, 37, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s2_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s2_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨33554432, 38, 0⟩ ⟨67108864, 37, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s2_c0), strips000_s2_c0_ok, Bool.and_self]

theorem strips000_s2_ok : stripOK 22 (ln2Iv 22) strips000_s2 = true :=
  stripOK_of_parts strips000_s2 strips000_s2_head strips000_s2_cells

def strips000_s3 : FEStrip := ⟨⟨67108864, 37, 0⟩, ⟨134217728, 36, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s3_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s3_head : (stripOKu 22 (ln2Iv 22) strips000_s3 && nodeOK strips000_s3.w0 && decide (40 * strips000_s3.w0.xa ≤ SCz) && decide ((lastNode strips000_s3.w0 strips000_s3.cells).xa = SCz / 2) && decide (strips000_s3.cells ≠ [])) = true := by decide +kernel

theorem strips000_s3_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨67108864, 37, 0⟩, ⟨134217728, 36, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s3_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s3_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨67108864, 37, 0⟩ ⟨134217728, 36, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s3_c0), strips000_s3_c0_ok, Bool.and_self]

theorem strips000_s3_ok : stripOK 22 (ln2Iv 22) strips000_s3 = true :=
  stripOK_of_parts strips000_s3 strips000_s3_head strips000_s3_cells

def strips000_s4 : FEStrip := ⟨⟨134217728, 36, 0⟩, ⟨268435456, 35, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s4_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s4_head : (stripOKu 22 (ln2Iv 22) strips000_s4 && nodeOK strips000_s4.w0 && decide (40 * strips000_s4.w0.xa ≤ SCz) && decide ((lastNode strips000_s4.w0 strips000_s4.cells).xa = SCz / 2) && decide (strips000_s4.cells ≠ [])) = true := by decide +kernel

theorem strips000_s4_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨134217728, 36, 0⟩, ⟨268435456, 35, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s4_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s4_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨134217728, 36, 0⟩ ⟨268435456, 35, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s4_c0), strips000_s4_c0_ok, Bool.and_self]

theorem strips000_s4_ok : stripOK 22 (ln2Iv 22) strips000_s4 = true :=
  stripOK_of_parts strips000_s4 strips000_s4_head strips000_s4_cells

def strips000_s5 : FEStrip := ⟨⟨268435456, 35, 0⟩, ⟨536870912, 34, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s5_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s5_head : (stripOKu 22 (ln2Iv 22) strips000_s5 && nodeOK strips000_s5.w0 && decide (40 * strips000_s5.w0.xa ≤ SCz) && decide ((lastNode strips000_s5.w0 strips000_s5.cells).xa = SCz / 2) && decide (strips000_s5.cells ≠ [])) = true := by decide +kernel

theorem strips000_s5_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨268435456, 35, 0⟩, ⟨536870912, 34, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s5_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s5_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨268435456, 35, 0⟩ ⟨536870912, 34, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s5_c0), strips000_s5_c0_ok, Bool.and_self]

theorem strips000_s5_ok : stripOK 22 (ln2Iv 22) strips000_s5 = true :=
  stripOK_of_parts strips000_s5 strips000_s5_head strips000_s5_cells

def strips000_s6 : FEStrip := ⟨⟨536870912, 34, 0⟩, ⟨1073741824, 33, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s6_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s6_head : (stripOKu 22 (ln2Iv 22) strips000_s6 && nodeOK strips000_s6.w0 && decide (40 * strips000_s6.w0.xa ≤ SCz) && decide ((lastNode strips000_s6.w0 strips000_s6.cells).xa = SCz / 2) && decide (strips000_s6.cells ≠ [])) = true := by decide +kernel

theorem strips000_s6_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨536870912, 34, 0⟩, ⟨1073741824, 33, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s6_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s6_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨536870912, 34, 0⟩ ⟨1073741824, 33, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s6_c0), strips000_s6_c0_ok, Bool.and_self]

theorem strips000_s6_ok : stripOK 22 (ln2Iv 22) strips000_s6 = true :=
  stripOK_of_parts strips000_s6 strips000_s6_head strips000_s6_cells

def strips000_s7 : FEStrip := ⟨⟨1073741824, 33, 0⟩, ⟨2147483648, 32, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s7_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s7_head : (stripOKu 22 (ln2Iv 22) strips000_s7 && nodeOK strips000_s7.w0 && decide (40 * strips000_s7.w0.xa ≤ SCz) && decide ((lastNode strips000_s7.w0 strips000_s7.cells).xa = SCz / 2) && decide (strips000_s7.cells ≠ [])) = true := by decide +kernel

theorem strips000_s7_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨1073741824, 33, 0⟩, ⟨2147483648, 32, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s7_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s7_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨1073741824, 33, 0⟩ ⟨2147483648, 32, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s7_c0), strips000_s7_c0_ok, Bool.and_self]

theorem strips000_s7_ok : stripOK 22 (ln2Iv 22) strips000_s7 = true :=
  stripOK_of_parts strips000_s7 strips000_s7_head strips000_s7_cells

def strips000_s8 : FEStrip := ⟨⟨2147483648, 32, 0⟩, ⟨4294967296, 31, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s8_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s8_head : (stripOKu 22 (ln2Iv 22) strips000_s8 && nodeOK strips000_s8.w0 && decide (40 * strips000_s8.w0.xa ≤ SCz) && decide ((lastNode strips000_s8.w0 strips000_s8.cells).xa = SCz / 2) && decide (strips000_s8.cells ≠ [])) = true := by decide +kernel

theorem strips000_s8_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨2147483648, 32, 0⟩, ⟨4294967296, 31, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s8_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s8_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨2147483648, 32, 0⟩ ⟨4294967296, 31, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s8_c0), strips000_s8_c0_ok, Bool.and_self]

theorem strips000_s8_ok : stripOK 22 (ln2Iv 22) strips000_s8 = true :=
  stripOK_of_parts strips000_s8 strips000_s8_head strips000_s8_cells

def strips000_s9 : FEStrip := ⟨⟨4294967296, 31, 0⟩, ⟨8589934592, 30, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s9_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s9_head : (stripOKu 22 (ln2Iv 22) strips000_s9 && nodeOK strips000_s9.w0 && decide (40 * strips000_s9.w0.xa ≤ SCz) && decide ((lastNode strips000_s9.w0 strips000_s9.cells).xa = SCz / 2) && decide (strips000_s9.cells ≠ [])) = true := by decide +kernel

theorem strips000_s9_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨4294967296, 31, 0⟩, ⟨8589934592, 30, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s9_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s9_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨4294967296, 31, 0⟩ ⟨8589934592, 30, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s9_c0), strips000_s9_c0_ok, Bool.and_self]

theorem strips000_s9_ok : stripOK 22 (ln2Iv 22) strips000_s9 = true :=
  stripOK_of_parts strips000_s9 strips000_s9_head strips000_s9_cells

def strips000_s10 : FEStrip := ⟨⟨8589934592, 30, 0⟩, ⟨17179869184, 29, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s10_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s10_head : (stripOKu 22 (ln2Iv 22) strips000_s10 && nodeOK strips000_s10.w0 && decide (40 * strips000_s10.w0.xa ≤ SCz) && decide ((lastNode strips000_s10.w0 strips000_s10.cells).xa = SCz / 2) && decide (strips000_s10.cells ≠ [])) = true := by decide +kernel

theorem strips000_s10_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨8589934592, 30, 0⟩, ⟨17179869184, 29, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s10_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s10_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨8589934592, 30, 0⟩ ⟨17179869184, 29, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s10_c0), strips000_s10_c0_ok, Bool.and_self]

theorem strips000_s10_ok : stripOK 22 (ln2Iv 22) strips000_s10 = true :=
  stripOK_of_parts strips000_s10 strips000_s10_head strips000_s10_cells

def strips000_s11 : FEStrip := ⟨⟨17179869184, 29, 0⟩, ⟨34359738368, 28, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s11_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s11_head : (stripOKu 22 (ln2Iv 22) strips000_s11 && nodeOK strips000_s11.w0 && decide (40 * strips000_s11.w0.xa ≤ SCz) && decide ((lastNode strips000_s11.w0 strips000_s11.cells).xa = SCz / 2) && decide (strips000_s11.cells ≠ [])) = true := by decide +kernel

theorem strips000_s11_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨17179869184, 29, 0⟩, ⟨34359738368, 28, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s11_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s11_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨17179869184, 29, 0⟩ ⟨34359738368, 28, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s11_c0), strips000_s11_c0_ok, Bool.and_self]

theorem strips000_s11_ok : stripOK 22 (ln2Iv 22) strips000_s11 = true :=
  stripOK_of_parts strips000_s11 strips000_s11_head strips000_s11_cells

def strips000_s12 : FEStrip := ⟨⟨34359738368, 28, 0⟩, ⟨68719476736, 27, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s12_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s12_head : (stripOKu 22 (ln2Iv 22) strips000_s12 && nodeOK strips000_s12.w0 && decide (40 * strips000_s12.w0.xa ≤ SCz) && decide ((lastNode strips000_s12.w0 strips000_s12.cells).xa = SCz / 2) && decide (strips000_s12.cells ≠ [])) = true := by decide +kernel

theorem strips000_s12_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨34359738368, 28, 0⟩, ⟨68719476736, 27, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s12_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s12_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨34359738368, 28, 0⟩ ⟨68719476736, 27, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s12_c0), strips000_s12_c0_ok, Bool.and_self]

theorem strips000_s12_ok : stripOK 22 (ln2Iv 22) strips000_s12 = true :=
  stripOK_of_parts strips000_s12 strips000_s12_head strips000_s12_cells

def strips000_s13 : FEStrip := ⟨⟨68719476736, 27, 0⟩, ⟨137438953472, 26, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s13_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s13_head : (stripOKu 22 (ln2Iv 22) strips000_s13 && nodeOK strips000_s13.w0 && decide (40 * strips000_s13.w0.xa ≤ SCz) && decide ((lastNode strips000_s13.w0 strips000_s13.cells).xa = SCz / 2) && decide (strips000_s13.cells ≠ [])) = true := by decide +kernel

theorem strips000_s13_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨68719476736, 27, 0⟩, ⟨137438953472, 26, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s13_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s13_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨68719476736, 27, 0⟩ ⟨137438953472, 26, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s13_c0), strips000_s13_c0_ok, Bool.and_self]

theorem strips000_s13_ok : stripOK 22 (ln2Iv 22) strips000_s13 = true :=
  stripOK_of_parts strips000_s13 strips000_s13_head strips000_s13_cells

def strips000_s14 : FEStrip := ⟨⟨137438953472, 26, 0⟩, ⟨274877906944, 25, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s14_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s14_head : (stripOKu 22 (ln2Iv 22) strips000_s14 && nodeOK strips000_s14.w0 && decide (40 * strips000_s14.w0.xa ≤ SCz) && decide ((lastNode strips000_s14.w0 strips000_s14.cells).xa = SCz / 2) && decide (strips000_s14.cells ≠ [])) = true := by decide +kernel

theorem strips000_s14_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨137438953472, 26, 0⟩, ⟨274877906944, 25, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s14_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s14_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨137438953472, 26, 0⟩ ⟨274877906944, 25, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s14_c0), strips000_s14_c0_ok, Bool.and_self]

theorem strips000_s14_ok : stripOK 22 (ln2Iv 22) strips000_s14 = true :=
  stripOK_of_parts strips000_s14 strips000_s14_head strips000_s14_cells

def strips000_s15 : FEStrip := ⟨⟨274877906944, 25, 0⟩, ⟨549755813888, 24, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s15_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s15_head : (stripOKu 22 (ln2Iv 22) strips000_s15 && nodeOK strips000_s15.w0 && decide (40 * strips000_s15.w0.xa ≤ SCz) && decide ((lastNode strips000_s15.w0 strips000_s15.cells).xa = SCz / 2) && decide (strips000_s15.cells ≠ [])) = true := by decide +kernel

theorem strips000_s15_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨274877906944, 25, 0⟩, ⟨549755813888, 24, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s15_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s15_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨274877906944, 25, 0⟩ ⟨549755813888, 24, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s15_c0), strips000_s15_c0_ok, Bool.and_self]

theorem strips000_s15_ok : stripOK 22 (ln2Iv 22) strips000_s15 = true :=
  stripOK_of_parts strips000_s15 strips000_s15_head strips000_s15_cells

def strips000_s16 : FEStrip := ⟨⟨549755813888, 24, 0⟩, ⟨1099511627776, 23, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s16_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s16_head : (stripOKu 22 (ln2Iv 22) strips000_s16 && nodeOK strips000_s16.w0 && decide (40 * strips000_s16.w0.xa ≤ SCz) && decide ((lastNode strips000_s16.w0 strips000_s16.cells).xa = SCz / 2) && decide (strips000_s16.cells ≠ [])) = true := by decide +kernel

theorem strips000_s16_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨549755813888, 24, 0⟩, ⟨1099511627776, 23, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s16_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s16_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨549755813888, 24, 0⟩ ⟨1099511627776, 23, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s16_c0), strips000_s16_c0_ok, Bool.and_self]

theorem strips000_s16_ok : stripOK 22 (ln2Iv 22) strips000_s16 = true :=
  stripOK_of_parts strips000_s16 strips000_s16_head strips000_s16_cells

def strips000_s17 : FEStrip := ⟨⟨1099511627776, 23, 0⟩, ⟨2199023255552, 22, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s17_c0⟩

set_option maxRecDepth 1000000 in
theorem strips000_s17_head : (stripOKu 22 (ln2Iv 22) strips000_s17 && nodeOK strips000_s17.w0 && decide (40 * strips000_s17.w0.xa ≤ SCz) && decide ((lastNode strips000_s17.w0 strips000_s17.cells).xa = SCz / 2) && decide (strips000_s17.cells ≠ [])) = true := by decide +kernel

theorem strips000_s17_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨1099511627776, 23, 0⟩, ⟨2199023255552, 22, 0⟩, ⟨461168601842738790, 5, 0⟩, strips000_s17_c0⟩ (⟨461168601842738790, 5, 0⟩) (strips000_s17_c0) = true := by
  skip
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨1099511627776, 23, 0⟩ ⟨2199023255552, 22, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips000_s17_c0), strips000_s17_c0_ok, Bool.and_self]

theorem strips000_s17_ok : stripOK 22 (ln2Iv 22) strips000_s17 = true :=
  stripOK_of_parts strips000_s17 strips000_s17_head strips000_s17_cells

def strips000 : List FEStrip := [strips000_s0, strips000_s1, strips000_s2, strips000_s3, strips000_s4, strips000_s5, strips000_s6, strips000_s7, strips000_s8, strips000_s9, strips000_s10, strips000_s11, strips000_s12, strips000_s13, strips000_s14, strips000_s15, strips000_s16, strips000_s17]

theorem strips000_ok : strips000.all (stripOK 22 (ln2Iv 22)) = true := by
  simp only [strips000, List.all_cons, List.all_nil, strips000_s0_ok, strips000_s1_ok, strips000_s2_ok, strips000_s3_ok, strips000_s4_ok, strips000_s5_ok, strips000_s6_ok, strips000_s7_ok, strips000_s8_ok, strips000_s9_ok, strips000_s10_ok, strips000_s11_ok, strips000_s12_ok, strips000_s13_ok, strips000_s14_ok, strips000_s15_ok, strips000_s16_ok, strips000_s17_ok, Bool.and_true]

end CKLaneA1.FEData


