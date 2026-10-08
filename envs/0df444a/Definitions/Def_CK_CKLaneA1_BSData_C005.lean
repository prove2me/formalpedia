-- Prove2me | Definitions.Def_CK_CKLaneA1_BSData_C005
-- name    : CK_CKLaneA1_BSData_C005
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T07:39:50.171503+00:00
-- url     : https://prove2.me/theorems/1059bea4-5ace-48b6-a64e-eb6d1e2d11de
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSData.C005` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSData.C005` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSData.C005` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSData.C005 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSData/C005.lean)

import Definitions.Def_CK_CKLaneA1_BSData_C005_part00

/-! Generated both-small cover chunk 5 (94 cells, 1 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.bsStripFull`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.BSData

open CKLaneA1


def bstrips005_s0 : BSStrip := ⟨⟨288230376151711744, 5, 0⟩, ⟨331464932574468505, 5, 0⟩, bstrips005_s0_c0 ++ bstrips005_s0_c1 ++ bstrips005_s0_c2 ++ bstrips005_s0_c3 ++ bstrips005_s0_c4 ++ bstrips005_s0_c5⟩

set_option maxRecDepth 1000000 in
theorem bstrips005_s0_head : (bsStripOK 22 (ln2Iv 22) bstrips005_s0 && decide (bstrips005_s0.cells ≠ []) && decide ((rLast r0 bstrips005_s0.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips005_s0_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨288230376151711744, 5, 0⟩, ⟨331464932574468505, 5, 0⟩, bstrips005_s0_c0 ++ bstrips005_s0_c1 ++ bstrips005_s0_c2 ++ bstrips005_s0_c3 ++ bstrips005_s0_c4 ++ bstrips005_s0_c5⟩ r0 (bstrips005_s0_c0 ++ bstrips005_s0_c1 ++ bstrips005_s0_c2 ++ bstrips005_s0_c3 ++ bstrips005_s0_c4 ++ bstrips005_s0_c5) = true := by
  rw [bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, bsCellsCheck_append, ← bstrips005_s0_c1_start, ← bstrips005_s0_c2_start, ← bstrips005_s0_c3_start, ← bstrips005_s0_c4_start, ← bstrips005_s0_c5_start]
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨288230376151711744, 5, 0⟩ ⟨331464932574468505, 5, 0⟩ (bstrips005_s0_c0 ++ bstrips005_s0_c1 ++ bstrips005_s0_c2 ++ bstrips005_s0_c3 ++ bstrips005_s0_c4 ++ bstrips005_s0_c5), bstrips005_s0_c0_ok, bstrips005_s0_c1_ok, bstrips005_s0_c2_ok, bstrips005_s0_c3_ok, bstrips005_s0_c4_ok, bstrips005_s0_c5_ok, Bool.and_self]

theorem bstrips005_s0_ok : bsStripFull 22 (ln2Iv 22) bstrips005_s0 = true :=
  bsStripFull_of_parts bstrips005_s0 bstrips005_s0_head bstrips005_s0_cells

def bstrips005 : List BSStrip := [bstrips005_s0]

theorem bstrips005_ok : bstrips005.all (bsStripFull 22 (ln2Iv 22)) = true := by
  simp only [bstrips005, List.all_cons, List.all_nil, bstrips005_s0_ok, Bool.and_true]

end CKLaneA1.BSData


