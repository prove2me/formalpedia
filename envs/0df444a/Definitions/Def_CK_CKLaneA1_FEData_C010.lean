-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C010
-- name    : CK_CKLaneA1_FEData_C010
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:08:45.590173+00:00
-- url     : https://prove2.me/theorems/2e29f187-e991-4ede-bf48-18ff9e4c6cfd
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEData.C010` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEData.C010` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEData.C010` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEData.C010 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEData/C010.lean)

import Definitions.Def_CK_CKLaneA1_FEData_C010_part00

/-! Generated fixedEdge cover chunk 10 (143 cells, 1 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips010_s0 : FEStrip := ⟨⟨240492220101584486, 6, 0⟩, ⟨259767626506730209, 6, 0⟩, ⟨461168601842738790, 5, 0⟩, strips010_s0_c0 ++ strips010_s0_c1 ++ strips010_s0_c2 ++ strips010_s0_c3 ++ strips010_s0_c4 ++ strips010_s0_c5 ++ strips010_s0_c6 ++ strips010_s0_c7 ++ strips010_s0_c8 ++ strips010_s0_c9 ++ strips010_s0_c10 ++ strips010_s0_c11⟩

set_option maxRecDepth 1000000 in
theorem strips010_s0_head : (stripOKu 22 (ln2Iv 22) strips010_s0 && nodeOK strips010_s0.w0 && decide (40 * strips010_s0.w0.xa ≤ SCz) && decide ((lastNode strips010_s0.w0 strips010_s0.cells).xa = SCz / 2) && decide (strips010_s0.cells ≠ [])) = true := by decide +kernel

theorem strips010_s0_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨240492220101584486, 6, 0⟩, ⟨259767626506730209, 6, 0⟩, ⟨461168601842738790, 5, 0⟩, strips010_s0_c0 ++ strips010_s0_c1 ++ strips010_s0_c2 ++ strips010_s0_c3 ++ strips010_s0_c4 ++ strips010_s0_c5 ++ strips010_s0_c6 ++ strips010_s0_c7 ++ strips010_s0_c8 ++ strips010_s0_c9 ++ strips010_s0_c10 ++ strips010_s0_c11⟩ (⟨461168601842738790, 5, 0⟩) (strips010_s0_c0 ++ strips010_s0_c1 ++ strips010_s0_c2 ++ strips010_s0_c3 ++ strips010_s0_c4 ++ strips010_s0_c5 ++ strips010_s0_c6 ++ strips010_s0_c7 ++ strips010_s0_c8 ++ strips010_s0_c9 ++ strips010_s0_c10 ++ strips010_s0_c11) = true := by
  rw [cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, ← strips010_s0_c1_start, ← strips010_s0_c2_start, ← strips010_s0_c3_start, ← strips010_s0_c4_start, ← strips010_s0_c5_start, ← strips010_s0_c6_start, ← strips010_s0_c7_start, ← strips010_s0_c8_start, ← strips010_s0_c9_start, ← strips010_s0_c10_start, ← strips010_s0_c11_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨240492220101584486, 6, 0⟩ ⟨259767626506730209, 6, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips010_s0_c0 ++ strips010_s0_c1 ++ strips010_s0_c2 ++ strips010_s0_c3 ++ strips010_s0_c4 ++ strips010_s0_c5 ++ strips010_s0_c6 ++ strips010_s0_c7 ++ strips010_s0_c8 ++ strips010_s0_c9 ++ strips010_s0_c10 ++ strips010_s0_c11), strips010_s0_c0_ok, strips010_s0_c1_ok, strips010_s0_c2_ok, strips010_s0_c3_ok, strips010_s0_c4_ok, strips010_s0_c5_ok, strips010_s0_c6_ok, strips010_s0_c7_ok, strips010_s0_c8_ok, strips010_s0_c9_ok, strips010_s0_c10_ok, strips010_s0_c11_ok, Bool.and_self]

theorem strips010_s0_ok : stripOK 22 (ln2Iv 22) strips010_s0 = true :=
  stripOK_of_parts strips010_s0 strips010_s0_head strips010_s0_cells

def strips010 : List FEStrip := [strips010_s0]

theorem strips010_ok : strips010.all (stripOK 22 (ln2Iv 22)) = true := by
  simp only [strips010, List.all_cons, List.all_nil, strips010_s0_ok, Bool.and_true]

end CKLaneA1.FEData


