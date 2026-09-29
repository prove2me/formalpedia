-- Prove2me | Definitions.Def_CK_CKLaneA1_BSData_C000
-- name    : CK_CKLaneA1_BSData_C000
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:53:22.631981+00:00
-- url     : https://prove2.me/theorems/8700de17-970d-41ee-a9f5-5537a2bd5084
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSData.C000` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSData.C000` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSData.C000` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSData.C000 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSData/C000.lean)

import Definitions.Def_CK_CKLaneA1_BSData_C000_part00

/-! Generated both-small cover chunk 0 (105 cells, 7 strips).
Checked by kernel evaluation of the Boolean checker `CKLaneA1.bsStripFull`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1.BSData

open CKLaneA1


def bstrips000_s0 : BSStrip := ⟨⟨0, 0, 0⟩, ⟨1, 63, 0⟩, bstrips000_s0_c0⟩

set_option maxRecDepth 1000000 in
theorem bstrips000_s0_head : (bsStripOK 22 (ln2Iv 22) bstrips000_s0 && decide (bstrips000_s0.cells ≠ []) && decide ((rLast r0 bstrips000_s0.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips000_s0_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨0, 0, 0⟩, ⟨1, 63, 0⟩, bstrips000_s0_c0⟩ r0 (bstrips000_s0_c0) = true := by
  skip
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨0, 0, 0⟩ ⟨1, 63, 0⟩ (bstrips000_s0_c0), bstrips000_s0_c0_ok, Bool.and_self]

theorem bstrips000_s0_ok : bsStripFull 22 (ln2Iv 22) bstrips000_s0 = true :=
  bsStripFull_of_parts bstrips000_s0 bstrips000_s0_head bstrips000_s0_cells

def bstrips000_s1 : BSStrip := ⟨⟨1, 63, 0⟩, ⟨65536, 47, 0⟩, bstrips000_s1_c0⟩

set_option maxRecDepth 1000000 in
theorem bstrips000_s1_head : (bsStripOK 22 (ln2Iv 22) bstrips000_s1 && decide (bstrips000_s1.cells ≠ []) && decide ((rLast r0 bstrips000_s1.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips000_s1_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨1, 63, 0⟩, ⟨65536, 47, 0⟩, bstrips000_s1_c0⟩ r0 (bstrips000_s1_c0) = true := by
  skip
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨1, 63, 0⟩ ⟨65536, 47, 0⟩ (bstrips000_s1_c0), bstrips000_s1_c0_ok, Bool.and_self]

theorem bstrips000_s1_ok : bsStripFull 22 (ln2Iv 22) bstrips000_s1 = true :=
  bsStripFull_of_parts bstrips000_s1 bstrips000_s1_head bstrips000_s1_cells

def bstrips000_s2 : BSStrip := ⟨⟨65536, 47, 0⟩, ⟨4294967296, 31, 0⟩, bstrips000_s2_c0⟩

set_option maxRecDepth 1000000 in
theorem bstrips000_s2_head : (bsStripOK 22 (ln2Iv 22) bstrips000_s2 && decide (bstrips000_s2.cells ≠ []) && decide ((rLast r0 bstrips000_s2.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips000_s2_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨65536, 47, 0⟩, ⟨4294967296, 31, 0⟩, bstrips000_s2_c0⟩ r0 (bstrips000_s2_c0) = true := by
  skip
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨65536, 47, 0⟩ ⟨4294967296, 31, 0⟩ (bstrips000_s2_c0), bstrips000_s2_c0_ok, Bool.and_self]

theorem bstrips000_s2_ok : bsStripFull 22 (ln2Iv 22) bstrips000_s2 = true :=
  bsStripFull_of_parts bstrips000_s2 bstrips000_s2_head bstrips000_s2_cells

def bstrips000_s3 : BSStrip := ⟨⟨4294967296, 31, 0⟩, ⟨1099511627776, 23, 0⟩, bstrips000_s3_c0⟩

set_option maxRecDepth 1000000 in
theorem bstrips000_s3_head : (bsStripOK 22 (ln2Iv 22) bstrips000_s3 && decide (bstrips000_s3.cells ≠ []) && decide ((rLast r0 bstrips000_s3.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips000_s3_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨4294967296, 31, 0⟩, ⟨1099511627776, 23, 0⟩, bstrips000_s3_c0⟩ r0 (bstrips000_s3_c0) = true := by
  skip
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨4294967296, 31, 0⟩ ⟨1099511627776, 23, 0⟩ (bstrips000_s3_c0), bstrips000_s3_c0_ok, Bool.and_self]

theorem bstrips000_s3_ok : bsStripFull 22 (ln2Iv 22) bstrips000_s3 = true :=
  bsStripFull_of_parts bstrips000_s3 bstrips000_s3_head bstrips000_s3_cells

def bstrips000_s4 : BSStrip := ⟨⟨1099511627776, 23, 0⟩, ⟨281474976710656, 15, 0⟩, bstrips000_s4_c0⟩

set_option maxRecDepth 1000000 in
theorem bstrips000_s4_head : (bsStripOK 22 (ln2Iv 22) bstrips000_s4 && decide (bstrips000_s4.cells ≠ []) && decide ((rLast r0 bstrips000_s4.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips000_s4_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨1099511627776, 23, 0⟩, ⟨281474976710656, 15, 0⟩, bstrips000_s4_c0⟩ r0 (bstrips000_s4_c0) = true := by
  skip
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨1099511627776, 23, 0⟩ ⟨281474976710656, 15, 0⟩ (bstrips000_s4_c0), bstrips000_s4_c0_ok, Bool.and_self]

theorem bstrips000_s4_ok : bsStripFull 22 (ln2Iv 22) bstrips000_s4 = true :=
  bsStripFull_of_parts bstrips000_s4 bstrips000_s4_head bstrips000_s4_cells

def bstrips000_s5 : BSStrip := ⟨⟨281474976710656, 15, 0⟩, ⟨4503599627370496, 11, 0⟩, bstrips000_s5_c0 ++ bstrips000_s5_c1⟩

set_option maxRecDepth 1000000 in
theorem bstrips000_s5_head : (bsStripOK 22 (ln2Iv 22) bstrips000_s5 && decide (bstrips000_s5.cells ≠ []) && decide ((rLast r0 bstrips000_s5.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips000_s5_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨281474976710656, 15, 0⟩, ⟨4503599627370496, 11, 0⟩, bstrips000_s5_c0 ++ bstrips000_s5_c1⟩ r0 (bstrips000_s5_c0 ++ bstrips000_s5_c1) = true := by
  rw [bsCellsCheck_append, ← bstrips000_s5_c1_start]
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨281474976710656, 15, 0⟩ ⟨4503599627370496, 11, 0⟩ (bstrips000_s5_c0 ++ bstrips000_s5_c1), bstrips000_s5_c0_ok, bstrips000_s5_c1_ok, Bool.and_self]

theorem bstrips000_s5_ok : bsStripFull 22 (ln2Iv 22) bstrips000_s5 = true :=
  bsStripFull_of_parts bstrips000_s5 bstrips000_s5_head bstrips000_s5_cells

def bstrips000_s6 : BSStrip := ⟨⟨4503599627370496, 11, 0⟩, ⟨18014398509481984, 9, 0⟩, bstrips000_s6_c0 ++ bstrips000_s6_c1⟩

set_option maxRecDepth 1000000 in
theorem bstrips000_s6_head : (bsStripOK 22 (ln2Iv 22) bstrips000_s6 && decide (bstrips000_s6.cells ≠ []) && decide ((rLast r0 bstrips000_s6.cells).ra = SCz)) = true := by decide +kernel

theorem bstrips000_s6_cells : bsCellsCheck 22 (ln2Iv 22) ⟨⟨4503599627370496, 11, 0⟩, ⟨18014398509481984, 9, 0⟩, bstrips000_s6_c0 ++ bstrips000_s6_c1⟩ r0 (bstrips000_s6_c0 ++ bstrips000_s6_c1) = true := by
  rw [bsCellsCheck_append, ← bstrips000_s6_c1_start]
  simp only [bsCellsCheck_geom 22 (ln2Iv 22) ⟨4503599627370496, 11, 0⟩ ⟨18014398509481984, 9, 0⟩ (bstrips000_s6_c0 ++ bstrips000_s6_c1), bstrips000_s6_c0_ok, bstrips000_s6_c1_ok, Bool.and_self]

theorem bstrips000_s6_ok : bsStripFull 22 (ln2Iv 22) bstrips000_s6 = true :=
  bsStripFull_of_parts bstrips000_s6 bstrips000_s6_head bstrips000_s6_cells

def bstrips000 : List BSStrip := [bstrips000_s0, bstrips000_s1, bstrips000_s2, bstrips000_s3, bstrips000_s4, bstrips000_s5, bstrips000_s6]

theorem bstrips000_ok : bstrips000.all (bsStripFull 22 (ln2Iv 22)) = true := by
  simp only [bstrips000, List.all_cons, List.all_nil, bstrips000_s0_ok, bstrips000_s1_ok, bstrips000_s2_ok, bstrips000_s3_ok, bstrips000_s4_ok, bstrips000_s5_ok, bstrips000_s6_ok, Bool.and_true]

end CKLaneA1.BSData


