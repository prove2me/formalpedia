-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C012
-- name    : CK_CKLaneA1_FEData_C012
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:23:28.826498+00:00
-- url     : https://prove2.me/theorems/1b5f2929-2326-481c-b2e9-69fff4b271f8
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEData.C012` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEData.C012` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEData.C012` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEData.C012 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEData/C012.lean)

import Definitions.Def_CK_CKLaneA1_FEData_C012_part02

/-! Generated fixedEdge cover chunk 12 (183 cells, 1 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips012_s0 : FEStrip := ⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39 ++ strips012_s0_c40 ++ strips012_s0_c41 ++ strips012_s0_c42 ++ strips012_s0_c43 ++ strips012_s0_c44 ++ strips012_s0_c45⟩

set_option maxRecDepth 1000000 in
theorem strips012_s0_head : (stripOKu 22 (ln2Iv 22) strips012_s0 && nodeOK strips012_s0.w0 && decide (40 * strips012_s0.w0.xa ≤ SCz) && decide ((lastNode strips012_s0.w0 strips012_s0.cells).xa = SCz / 2) && decide (strips012_s0.cells ≠ [])) = true := by decide +kernel

theorem strips012_s0_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨279043032911875932, 6, 0⟩, ⟨298318439317021655, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39 ++ strips012_s0_c40 ++ strips012_s0_c41 ++ strips012_s0_c42 ++ strips012_s0_c43 ++ strips012_s0_c44 ++ strips012_s0_c45⟩ (⟨461168601842738790, 5, 0⟩) (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39 ++ strips012_s0_c40 ++ strips012_s0_c41 ++ strips012_s0_c42 ++ strips012_s0_c43 ++ strips012_s0_c44 ++ strips012_s0_c45) = true := by
  rw [cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, ← strips012_s0_c1_start, ← strips012_s0_c2_start, ← strips012_s0_c3_start, ← strips012_s0_c4_start, ← strips012_s0_c5_start, ← strips012_s0_c6_start, ← strips012_s0_c7_start, ← strips012_s0_c8_start, ← strips012_s0_c9_start, ← strips012_s0_c10_start, ← strips012_s0_c11_start, ← strips012_s0_c12_start, ← strips012_s0_c13_start, ← strips012_s0_c14_start, ← strips012_s0_c15_start, ← strips012_s0_c16_start, ← strips012_s0_c17_start, ← strips012_s0_c18_start, ← strips012_s0_c19_start, ← strips012_s0_c20_start, ← strips012_s0_c21_start, ← strips012_s0_c22_start, ← strips012_s0_c23_start, ← strips012_s0_c24_start, ← strips012_s0_c25_start, ← strips012_s0_c26_start, ← strips012_s0_c27_start, ← strips012_s0_c28_start, ← strips012_s0_c29_start, ← strips012_s0_c30_start, ← strips012_s0_c31_start, ← strips012_s0_c32_start, ← strips012_s0_c33_start, ← strips012_s0_c34_start, ← strips012_s0_c35_start, ← strips012_s0_c36_start, ← strips012_s0_c37_start, ← strips012_s0_c38_start, ← strips012_s0_c39_start, ← strips012_s0_c40_start, ← strips012_s0_c41_start, ← strips012_s0_c42_start, ← strips012_s0_c43_start, ← strips012_s0_c44_start, ← strips012_s0_c45_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨279043032911875932, 6, 0⟩ ⟨298318439317021655, 5, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips012_s0_c0 ++ strips012_s0_c1 ++ strips012_s0_c2 ++ strips012_s0_c3 ++ strips012_s0_c4 ++ strips012_s0_c5 ++ strips012_s0_c6 ++ strips012_s0_c7 ++ strips012_s0_c8 ++ strips012_s0_c9 ++ strips012_s0_c10 ++ strips012_s0_c11 ++ strips012_s0_c12 ++ strips012_s0_c13 ++ strips012_s0_c14 ++ strips012_s0_c15 ++ strips012_s0_c16 ++ strips012_s0_c17 ++ strips012_s0_c18 ++ strips012_s0_c19 ++ strips012_s0_c20 ++ strips012_s0_c21 ++ strips012_s0_c22 ++ strips012_s0_c23 ++ strips012_s0_c24 ++ strips012_s0_c25 ++ strips012_s0_c26 ++ strips012_s0_c27 ++ strips012_s0_c28 ++ strips012_s0_c29 ++ strips012_s0_c30 ++ strips012_s0_c31 ++ strips012_s0_c32 ++ strips012_s0_c33 ++ strips012_s0_c34 ++ strips012_s0_c35 ++ strips012_s0_c36 ++ strips012_s0_c37 ++ strips012_s0_c38 ++ strips012_s0_c39 ++ strips012_s0_c40 ++ strips012_s0_c41 ++ strips012_s0_c42 ++ strips012_s0_c43 ++ strips012_s0_c44 ++ strips012_s0_c45), strips012_s0_c0_ok, strips012_s0_c1_ok, strips012_s0_c2_ok, strips012_s0_c3_ok, strips012_s0_c4_ok, strips012_s0_c5_ok, strips012_s0_c6_ok, strips012_s0_c7_ok, strips012_s0_c8_ok, strips012_s0_c9_ok, strips012_s0_c10_ok, strips012_s0_c11_ok, strips012_s0_c12_ok, strips012_s0_c13_ok, strips012_s0_c14_ok, strips012_s0_c15_ok, strips012_s0_c16_ok, strips012_s0_c17_ok, strips012_s0_c18_ok, strips012_s0_c19_ok, strips012_s0_c20_ok, strips012_s0_c21_ok, strips012_s0_c22_ok, strips012_s0_c23_ok, strips012_s0_c24_ok, strips012_s0_c25_ok, strips012_s0_c26_ok, strips012_s0_c27_ok, strips012_s0_c28_ok, strips012_s0_c29_ok, strips012_s0_c30_ok, strips012_s0_c31_ok, strips012_s0_c32_ok, strips012_s0_c33_ok, strips012_s0_c34_ok, strips012_s0_c35_ok, strips012_s0_c36_ok, strips012_s0_c37_ok, strips012_s0_c38_ok, strips012_s0_c39_ok, strips012_s0_c40_ok, strips012_s0_c41_ok, strips012_s0_c42_ok, strips012_s0_c43_ok, strips012_s0_c44_ok, strips012_s0_c45_ok, Bool.and_self]

theorem strips012_s0_ok : stripOK 22 (ln2Iv 22) strips012_s0 = true :=
  stripOK_of_parts strips012_s0 strips012_s0_head strips012_s0_cells

def strips012 : List FEStrip := [strips012_s0]

theorem strips012_ok : strips012.all (stripOK 22 (ln2Iv 22)) = true := by
  simp only [strips012, List.all_cons, List.all_nil, strips012_s0_ok, Bool.and_true]

end CKLaneA1.FEData


