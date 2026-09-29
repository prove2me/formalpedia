-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C011
-- name    : CK_CKLaneA1_FEData_C011
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:13:24.133532+00:00
-- url     : https://prove2.me/theorems/7edf8202-340d-4525-a8ef-e9092d6a25d1
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEData.C011` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEData.C011` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEData.C011` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEData.C011 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEData/C011.lean)

import Definitions.Def_CK_CKLaneA1_FEData_C011_part00

/-! Generated fixedEdge cover chunk 11 (164 cells, 1 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips011_s0 : FEStrip := ⟨⟨259767626506730209, 6, 0⟩, ⟨279043032911875932, 6, 0⟩, ⟨461168601842738790, 5, 0⟩, strips011_s0_c0 ++ strips011_s0_c1 ++ strips011_s0_c2 ++ strips011_s0_c3 ++ strips011_s0_c4 ++ strips011_s0_c5 ++ strips011_s0_c6 ++ strips011_s0_c7 ++ strips011_s0_c8 ++ strips011_s0_c9 ++ strips011_s0_c10 ++ strips011_s0_c11 ++ strips011_s0_c12 ++ strips011_s0_c13 ++ strips011_s0_c14 ++ strips011_s0_c15 ++ strips011_s0_c16⟩

set_option maxRecDepth 1000000 in
theorem strips011_s0_head : (stripOKu 22 (ln2Iv 22) strips011_s0 && nodeOK strips011_s0.w0 && decide (40 * strips011_s0.w0.xa ≤ SCz) && decide ((lastNode strips011_s0.w0 strips011_s0.cells).xa = SCz / 2) && decide (strips011_s0.cells ≠ [])) = true := by decide +kernel

theorem strips011_s0_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨259767626506730209, 6, 0⟩, ⟨279043032911875932, 6, 0⟩, ⟨461168601842738790, 5, 0⟩, strips011_s0_c0 ++ strips011_s0_c1 ++ strips011_s0_c2 ++ strips011_s0_c3 ++ strips011_s0_c4 ++ strips011_s0_c5 ++ strips011_s0_c6 ++ strips011_s0_c7 ++ strips011_s0_c8 ++ strips011_s0_c9 ++ strips011_s0_c10 ++ strips011_s0_c11 ++ strips011_s0_c12 ++ strips011_s0_c13 ++ strips011_s0_c14 ++ strips011_s0_c15 ++ strips011_s0_c16⟩ (⟨461168601842738790, 5, 0⟩) (strips011_s0_c0 ++ strips011_s0_c1 ++ strips011_s0_c2 ++ strips011_s0_c3 ++ strips011_s0_c4 ++ strips011_s0_c5 ++ strips011_s0_c6 ++ strips011_s0_c7 ++ strips011_s0_c8 ++ strips011_s0_c9 ++ strips011_s0_c10 ++ strips011_s0_c11 ++ strips011_s0_c12 ++ strips011_s0_c13 ++ strips011_s0_c14 ++ strips011_s0_c15 ++ strips011_s0_c16) = true := by
  rw [cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, ← strips011_s0_c1_start, ← strips011_s0_c2_start, ← strips011_s0_c3_start, ← strips011_s0_c4_start, ← strips011_s0_c5_start, ← strips011_s0_c6_start, ← strips011_s0_c7_start, ← strips011_s0_c8_start, ← strips011_s0_c9_start, ← strips011_s0_c10_start, ← strips011_s0_c11_start, ← strips011_s0_c12_start, ← strips011_s0_c13_start, ← strips011_s0_c14_start, ← strips011_s0_c15_start, ← strips011_s0_c16_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨259767626506730209, 6, 0⟩ ⟨279043032911875932, 6, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips011_s0_c0 ++ strips011_s0_c1 ++ strips011_s0_c2 ++ strips011_s0_c3 ++ strips011_s0_c4 ++ strips011_s0_c5 ++ strips011_s0_c6 ++ strips011_s0_c7 ++ strips011_s0_c8 ++ strips011_s0_c9 ++ strips011_s0_c10 ++ strips011_s0_c11 ++ strips011_s0_c12 ++ strips011_s0_c13 ++ strips011_s0_c14 ++ strips011_s0_c15 ++ strips011_s0_c16), strips011_s0_c0_ok, strips011_s0_c1_ok, strips011_s0_c2_ok, strips011_s0_c3_ok, strips011_s0_c4_ok, strips011_s0_c5_ok, strips011_s0_c6_ok, strips011_s0_c7_ok, strips011_s0_c8_ok, strips011_s0_c9_ok, strips011_s0_c10_ok, strips011_s0_c11_ok, strips011_s0_c12_ok, strips011_s0_c13_ok, strips011_s0_c14_ok, strips011_s0_c15_ok, strips011_s0_c16_ok, Bool.and_self]

theorem strips011_s0_ok : stripOK 22 (ln2Iv 22) strips011_s0 = true :=
  stripOK_of_parts strips011_s0 strips011_s0_head strips011_s0_cells

def strips011 : List FEStrip := [strips011_s0]

theorem strips011_ok : strips011.all (stripOK 22 (ln2Iv 22)) = true := by
  simp only [strips011, List.all_cons, List.all_nil, strips011_s0_ok, Bool.and_true]

end CKLaneA1.FEData


