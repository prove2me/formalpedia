-- Prove2me | Definitions.Def_CK_CKLaneA1_BSData_C002
-- name    : CK_CKLaneA1_BSData_C002
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:02:10.67522+00:00
-- url     : https://prove2.me/theorems/6914a36c-7b11-4ab0-a6f8-f853ff65e3db
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSData.C002` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSData.C002` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSData.C002` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSData.C002 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSData/C002.lean)

import Definitions.Def_CK_CKLaneA1_BSData_C002_part00

/-! Generated both-small cover chunk 2 (111 cells, 2 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.bsStripFull`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.BSData

open CKLaneA1


def bstrips002_s0 : BSStrip := ⟨⟨108086391056891904, 7, 0⟩, ⟨144115188075855872, 6, 0⟩, bstrips002_s0_c0 ++ bstrips002_s0_c1 ++ bstrips002_s0_c2 ++ bstrips002_s0_c3⟩

set_option maxRecDepth 1000000 in
theorem bstrips002_s0_head : (bsStripOK 22 (ln2Iv 22) bstrips002_s0 && decide (bstrips002_s0.cells ≠ []) && decide ((rLast r0 bstrips002_s0.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips002_s0_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨108086391056891904, 7, 0⟩, ⟨144115188075855872, 6, 0⟩, bstrips002_s0_c0 ++ bstrips002_s0_c1 ++ bstrips002_s0_c2 ++ bstrips002_s0_c3⟩ r0 (bstrips002_s0_c0 ++ bstrips002_s0_c1 ++ bstrips002_s0_c2 ++ bstrips002_s0_c3) = true := by
  rw [bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, ← bstrips002_s0_c1_start, ← bstrips002_s0_c2_start, ← bstrips002_s0_c3_start]
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨108086391056891904, 7, 0⟩ ⟨144115188075855872, 6, 0⟩ (bstrips002_s0_c0 ++ bstrips002_s0_c1 ++ bstrips002_s0_c2 ++ bstrips002_s0_c3), bstrips002_s0_c0_ok, bstrips002_s0_c1_ok, bstrips002_s0_c2_ok, bstrips002_s0_c3_ok, Bool.and_self]

theorem bstrips002_s0_ok : bsStripFull 22 (ln2Iv 22) bstrips002_s0 = true :=
  bsStripFull_of_parts bstrips002_s0 bstrips002_s0_head bstrips002_s0_cells

def bstrips002_s1 : BSStrip := ⟨⟨144115188075855872, 6, 0⟩, ⟨180143985094819840, 6, 0⟩, bstrips002_s1_c0 ++ bstrips002_s1_c1 ++ bstrips002_s1_c2 ++ bstrips002_s1_c3⟩

set_option maxRecDepth 1000000 in
theorem bstrips002_s1_head : (bsStripOK 22 (ln2Iv 22) bstrips002_s1 && decide (bstrips002_s1.cells ≠ []) && decide ((rLast r0 bstrips002_s1.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips002_s1_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨144115188075855872, 6, 0⟩, ⟨180143985094819840, 6, 0⟩, bstrips002_s1_c0 ++ bstrips002_s1_c1 ++ bstrips002_s1_c2 ++ bstrips002_s1_c3⟩ r0 (bstrips002_s1_c0 ++ bstrips002_s1_c1 ++ bstrips002_s1_c2 ++ bstrips002_s1_c3) = true := by
  rw [bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, ← bstrips002_s1_c1_start, ← bstrips002_s1_c2_start, ← bstrips002_s1_c3_start]
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨144115188075855872, 6, 0⟩ ⟨180143985094819840, 6, 0⟩ (bstrips002_s1_c0 ++ bstrips002_s1_c1 ++ bstrips002_s1_c2 ++ bstrips002_s1_c3), bstrips002_s1_c0_ok, bstrips002_s1_c1_ok, bstrips002_s1_c2_ok, bstrips002_s1_c3_ok, Bool.and_self]

theorem bstrips002_s1_ok : bsStripFull 22 (ln2Iv 22) bstrips002_s1 = true :=
  bsStripFull_of_parts bstrips002_s1 bstrips002_s1_head bstrips002_s1_cells

def bstrips002 : List BSStrip := [bstrips002_s0, bstrips002_s1]

theorem bstrips002_ok : bstrips002.all (bsStripFull 22 (ln2Iv 22)) = true := by
  simp only [bstrips002, List.all_cons, List.all_nil, bstrips002_s0_ok, bstrips002_s1_ok, Bool.and_true]

end CKLaneA1.BSData


