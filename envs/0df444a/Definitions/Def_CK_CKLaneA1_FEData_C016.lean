-- Prove2me | Definitions.Def_CK_CKLaneA1_FEData_C016
-- name    : CK_CKLaneA1_FEData_C016
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:00:04.006304+00:00
-- url     : https://prove2.me/theorems/13f990ac-2c5b-4e1e-ab04-b4a686273756
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEData.C016` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEData.C016` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEData.C016` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEData.C016 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEData/C016.lean)

import Definitions.Def_CK_CKLaneA1_FEData_C016_part00

/-! Generated fixedEdge cover chunk 16 (73 cells, 1 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.stripOK`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.FEData

open CKLaneA1


def strips016_s0 : FEStrip := ⟨⟨358846818308881121, 5, 0⟩, ⟨368934881474191033, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, strips016_s0_c0 ++ strips016_s0_c1 ++ strips016_s0_c2 ++ strips016_s0_c3 ++ strips016_s0_c4⟩

set_option maxRecDepth 1000000 in
theorem strips016_s0_head : (stripOKu 22 (ln2Iv 22) strips016_s0 && nodeOK strips016_s0.w0 && decide (40 * strips016_s0.w0.xa ≤ SCz) && decide ((lastNode strips016_s0.w0 strips016_s0.cells).xa = SCz / 2) && decide (strips016_s0.cells ≠ [])) = true := by decide +kernel

theorem strips016_s0_cells : cellsCheck 22 (ln2Iv 22) ⟨⟨358846818308881121, 5, 0⟩, ⟨368934881474191033, 5, 0⟩, ⟨461168601842738790, 5, 0⟩, strips016_s0_c0 ++ strips016_s0_c1 ++ strips016_s0_c2 ++ strips016_s0_c3 ++ strips016_s0_c4⟩ (⟨461168601842738790, 5, 0⟩) (strips016_s0_c0 ++ strips016_s0_c1 ++ strips016_s0_c2 ++ strips016_s0_c3 ++ strips016_s0_c4) = true := by
  rw [cellsCheck_append, cellsCheck_append, cellsCheck_append, cellsCheck_append, ← strips016_s0_c1_start, ← strips016_s0_c2_start, ← strips016_s0_c3_start, ← strips016_s0_c4_start]
  simp only [cellsCheck_geom 22 (ln2Iv 22) ⟨358846818308881121, 5, 0⟩ ⟨368934881474191033, 5, 0⟩ ⟨461168601842738790, 5, 0⟩ (strips016_s0_c0 ++ strips016_s0_c1 ++ strips016_s0_c2 ++ strips016_s0_c3 ++ strips016_s0_c4), strips016_s0_c0_ok, strips016_s0_c1_ok, strips016_s0_c2_ok, strips016_s0_c3_ok, strips016_s0_c4_ok, Bool.and_self]

theorem strips016_s0_ok : stripOK 22 (ln2Iv 22) strips016_s0 = true :=
  stripOK_of_parts strips016_s0 strips016_s0_head strips016_s0_cells

def strips016 : List FEStrip := [strips016_s0]

theorem strips016_ok : strips016.all (stripOK 22 (ln2Iv 22)) = true := by
  simp only [strips016, List.all_cons, List.all_nil, strips016_s0_ok, Bool.and_true]

end CKLaneA1.FEData


