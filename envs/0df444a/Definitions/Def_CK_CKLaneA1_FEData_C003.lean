-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C003
-- name    : CK_CKLaneA1_FEData_C003
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:10:44.549672+00:00
-- url     : https://prove2.me/theorems/9a5ab51c-3b38-4334-8658-e06c92482d7f
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEData.C003` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEData.C003` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEData.C003` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEData.C003 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEData/C003.lean)

import Definitions.Def_CK_CKLaneA1_FEData_C003_part00

/-! Generated fixedEdge cover chunk 3 (99 cells, 2 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips003_s0 : FEStrip := ⟨⟨72057594037927936, 7, 0⟩, ⟨90071992547409920, 7, 0⟩, ⟨461168601842738790, 5, 0⟩, strips003_s0_c0 ++ strips003_s0_c1 ++ strips003_s0_c2⟩

set_option maxRecDepth 1000000 in
theorem strips003_s0_head : (stripOKu 22 (ln2Iv 22) strips003_s0 && nodeOK strips003_s0.w0 && decide (40 * strips003_s0.w0.xa ≤ SCz) && decide ((lastNode strips003_s0.w0 strips003_s0.cells).xa = SCz / 2) && decide (strips003_s0.cells ≠ [])) = true := by decide +kernel

theorem strips003_s0_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨72057594037927936, 7, 0⟩, ⟨90071992547409920, 7, 0⟩, ⟨461168601842738790, 5, 0⟩, strips003_s0_c0 ++ strips003_s0_c1 ++ strips003_s0_c2⟩ (⟨461168601842738790, 5, 0⟩) (strips003_s0_c0 ++ strips003_s0_c1 ++ strips003_s0_c2) = true := by
  rw [cellsCheck_append, cellsCheck_append, ← strips003_s0_c1_start, ← strips003_s0_c2_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨72057594037927936, 7, 0⟩ ⟨90071992547409920, 7, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips003_s0_c0 ++ strips003_s0_c1 ++ strips003_s0_c2), strips003_s0_c0_ok, strips003_s0_c1_ok, strips003_s0_c2_ok, Bool.and_self]

theorem strips003_s0_ok : stripOK 22 (ln2Iv 22) strips003_s0 = true :=
  stripOK_of_parts strips003_s0 strips003_s0_head strips003_s0_cells

def strips003_s1 : FEStrip := ⟨⟨90071992547409920, 7, 0⟩, ⟨108086391056891904, 7, 0⟩, ⟨461168601842738790, 5, 0⟩, strips003_s1_c0 ++ strips003_s1_c1 ++ strips003_s1_c2⟩

set_option maxRecDepth 1000000 in
theorem strips003_s1_head : (stripOKu 22 (ln2Iv 22) strips003_s1 && nodeOK strips003_s1.w0 && decide (40 * strips003_s1.w0.xa ≤ SCz) && decide ((lastNode strips003_s1.w0 strips003_s1.cells).xa = SCz / 2) && decide (strips003_s1.cells ≠ [])) = true := by decide +kernel

theorem strips003_s1_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨90071992547409920, 7, 0⟩, ⟨108086391056891904, 7, 0⟩, ⟨461168601842738790, 5, 0⟩, strips003_s1_c0 ++ strips003_s1_c1 ++ strips003_s1_c2⟩ (⟨461168601842738790, 5, 0⟩) (strips003_s1_c0 ++ strips003_s1_c1 ++ strips003_s1_c2) = true := by
  rw [cellsCheck_append, cellsCheck_append, ← strips003_s1_c1_start, ← strips003_s1_c2_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨90071992547409920, 7, 0⟩ ⟨108086391056891904, 7, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips003_s1_c0 ++ strips003_s1_c1 ++ strips003_s1_c2), strips003_s1_c0_ok, strips003_s1_c1_ok, strips003_s1_c2_ok, Bool.and_self]

theorem strips003_s1_ok : stripOK 22 (ln2Iv 22) strips003_s1 = true :=
  stripOK_of_parts strips003_s1 strips003_s1_head strips003_s1_cells

def strips003 : List FEStrip := [strips003_s0, strips003_s1]

theorem strips003_ok : strips003.all (stripOK 22 (ln2Iv 22)) = true := by
  simp only [strips003, List.all_cons, List.all_nil, strips003_s0_ok, strips003_s1_ok, Bool.and_true]

end CKLaneA1.FEData


