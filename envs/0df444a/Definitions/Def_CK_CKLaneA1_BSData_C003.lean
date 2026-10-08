-- Prove2me | Definitions.Def_CK_CKLaneA1_BSData_C003
-- name    : CK_CKLaneA1_BSData_C003
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:16:17.729045+00:00
-- url     : https://prove2.me/theorems/ff93692b-3ae5-4990-8c5d-df708529c6a6
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSData.C003` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSData.C003` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSData.C003` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSData.C003 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSData/C003.lean)

import Definitions.Def_CK_CKLaneA1_BSData_C003_part00

/-! Generated both-small cover chunk 3 (132 cells, 2 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.bsStripFull`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.BSData

open CKLaneA1


def bstrips003_s0 : BSStrip := ⟨⟨180143985094819840, 6, 0⟩, ⟨216172782113783808, 6, 0⟩, bstrips003_s0_c0 ++ bstrips003_s0_c1 ++ bstrips003_s0_c2 ++ bstrips003_s0_c3 ++ bstrips003_s0_c4 ++ bstrips003_s0_c5 ++ bstrips003_s0_c6 ++ bstrips003_s0_c7⟩

set_option maxRecDepth 1000000 in
theorem bstrips003_s0_head : (bsStripOK 22 (ln2Iv 22) bstrips003_s0 && decide (bstrips003_s0.cells ≠ []) && decide ((rLast r0 bstrips003_s0.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips003_s0_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨180143985094819840, 6, 0⟩, ⟨216172782113783808, 6, 0⟩, bstrips003_s0_c0 ++ bstrips003_s0_c1 ++ bstrips003_s0_c2 ++ bstrips003_s0_c3 ++ bstrips003_s0_c4 ++ bstrips003_s0_c5 ++ bstrips003_s0_c6 ++ bstrips003_s0_c7⟩ r0 (bstrips003_s0_c0 ++ bstrips003_s0_c1 ++ bstrips003_s0_c2 ++ bstrips003_s0_c3 ++ bstrips003_s0_c4 ++ bstrips003_s0_c5 ++ bstrips003_s0_c6 ++ bstrips003_s0_c7) = true := by
  rw [bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, ← bstrips003_s0_c1_start, ← bstrips003_s0_c2_start, ← bstrips003_s0_c3_start, ← bstrips003_s0_c4_start, ← bstrips003_s0_c5_start, ← bstrips003_s0_c6_start, ← bstrips003_s0_c7_start]
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨180143985094819840, 6, 0⟩ ⟨216172782113783808, 6, 0⟩ (bstrips003_s0_c0 ++ bstrips003_s0_c1 ++ bstrips003_s0_c2 ++ bstrips003_s0_c3 ++ bstrips003_s0_c4 ++ bstrips003_s0_c5 ++ bstrips003_s0_c6 ++ bstrips003_s0_c7), bstrips003_s0_c0_ok, bstrips003_s0_c1_ok, bstrips003_s0_c2_ok, bstrips003_s0_c3_ok, bstrips003_s0_c4_ok, bstrips003_s0_c5_ok, bstrips003_s0_c6_ok, bstrips003_s0_c7_ok, Bool.and_self]

theorem bstrips003_s0_ok : bsStripFull 22 (ln2Iv 22) bstrips003_s0 = true :=
  bsStripFull_of_parts bstrips003_s0 bstrips003_s0_head bstrips003_s0_cells

def bstrips003_s1 : BSStrip := ⟨⟨216172782113783808, 6, 0⟩, ⟨252201579132747776, 6, 0⟩, bstrips003_s1_c0 ++ bstrips003_s1_c1 ++ bstrips003_s1_c2 ++ bstrips003_s1_c3 ++ bstrips003_s1_c4 ++ bstrips003_s1_c5 ++ bstrips003_s1_c6 ++ bstrips003_s1_c7 ++ bstrips003_s1_c8⟩

set_option maxRecDepth 1000000 in
theorem bstrips003_s1_head : (bsStripOK 22 (ln2Iv 22) bstrips003_s1 && decide (bstrips003_s1.cells ≠ []) && decide ((rLast r0 bstrips003_s1.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips003_s1_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨216172782113783808, 6, 0⟩, ⟨252201579132747776, 6, 0⟩, bstrips003_s1_c0 ++ bstrips003_s1_c1 ++ bstrips003_s1_c2 ++ bstrips003_s1_c3 ++ bstrips003_s1_c4 ++ bstrips003_s1_c5 ++ bstrips003_s1_c6 ++ bstrips003_s1_c7 ++ bstrips003_s1_c8⟩ r0 (bstrips003_s1_c0 ++ bstrips003_s1_c1 ++ bstrips003_s1_c2 ++ bstrips003_s1_c3 ++ bstrips003_s1_c4 ++ bstrips003_s1_c5 ++ bstrips003_s1_c6 ++ bstrips003_s1_c7 ++ bstrips003_s1_c8) = true := by
  rw [bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, ← bstrips003_s1_c1_start, ← bstrips003_s1_c2_start, ← bstrips003_s1_c3_start, ← bstrips003_s1_c4_start, ← bstrips003_s1_c5_start, ← bstrips003_s1_c6_start, ← bstrips003_s1_c7_start, ← bstrips003_s1_c8_start]
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨216172782113783808, 6, 0⟩ ⟨252201579132747776, 6, 0⟩ (bstrips003_s1_c0 ++ bstrips003_s1_c1 ++ bstrips003_s1_c2 ++ bstrips003_s1_c3 ++ bstrips003_s1_c4 ++ bstrips003_s1_c5 ++ bstrips003_s1_c6 ++ bstrips003_s1_c7 ++ bstrips003_s1_c8), bstrips003_s1_c0_ok, bstrips003_s1_c1_ok, bstrips003_s1_c2_ok, bstrips003_s1_c3_ok, bstrips003_s1_c4_ok, bstrips003_s1_c5_ok, bstrips003_s1_c6_ok, bstrips003_s1_c7_ok, bstrips003_s1_c8_ok, Bool.and_self]

theorem bstrips003_s1_ok : bsStripFull 22 (ln2Iv 22) bstrips003_s1 = true :=
  bsStripFull_of_parts bstrips003_s1 bstrips003_s1_head bstrips003_s1_cells

def bstrips003 : List BSStrip := [bstrips003_s0, bstrips003_s1]

theorem bstrips003_ok : bstrips003.all (bsStripFull 22 (ln2Iv 22)) = true := by
  simp only [bstrips003, List.all_cons, List.all_nil, bstrips003_s0_ok, bstrips003_s1_ok, Bool.and_true]

end CKLaneA1.BSData


