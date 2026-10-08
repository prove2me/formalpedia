-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub3
-- name    : CK_CKLaneN6_Sub3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:38:37.6919+00:00
-- url     : https://prove2.me/theorems/974c3cc0-d9d3-4de5-aab6-f2e7bed1c630
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3.lean)

import Definitions.Def_CK_CKLaneN6_Sub3_part00

/-! Lane N6 assembly part 3: depth-6 subtrees 134024..135135 of the archived tree, each
matched (kernel decide over the overlapping coarse shards only) with the shard leaf lists. -/

set_option autoImplicit false

namespace CKLaneN6.Asm

open CKLaneN6 CKLaneM05.FE8

set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
/-- Subtree `135025`: 790 archived leaves (DFS range 74027..74816). -/
theorem sub_135025 : (ArchTree.t135025.leavesR [5, 2, 0, 5, 3, 1]).map Prod.fst =
    ((Cs.C0060.paths).drop 425).take 790 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135025 : ∀ q ∈ ArchTree.t135025.leavesR [5, 2, 0, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0060.paths).drop 425).take 790 := by
    rw [← sub_135025]; exact List.mem_map_of_mem hq
  exact Cs.C0060.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135034`: 163 archived leaves (DFS range 74817..74979). -/
theorem sub_135034 : (ArchTree.t135034.leavesR [4, 3, 0, 5, 3, 1]).map Prod.fst =
    ((Cs.C0060.paths ++ Cs.C0061.paths).drop 1215).take 163 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135034 : ∀ q ∈ ArchTree.t135034.leavesR [4, 3, 0, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0060.paths ++ Cs.C0061.paths).drop 1215).take 163 := by
    rw [← sub_135034]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0060.leafOK Cs.C0061.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135035`: 321 archived leaves (DFS range 74980..75300). -/
theorem sub_135035 : (ArchTree.t135035.leavesR [5, 3, 0, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths).drop 12).take 321 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135035 : ∀ q ∈ ArchTree.t135035.leavesR [5, 3, 0, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths).drop 12).take 321 := by
    rw [← sub_135035]; exact List.mem_map_of_mem hq
  exact Cs.C0061.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135124`: 1 archived leaves (DFS range 75301..75301). -/
theorem sub_135124 : (ArchTree.t135124.leavesR [4, 2, 1, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths).drop 333).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135124 : ∀ q ∈ ArchTree.t135124.leavesR [4, 2, 1, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths).drop 333).take 1 := by
    rw [← sub_135124]; exact List.mem_map_of_mem hq
  exact Cs.C0061.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135125`: 1 archived leaves (DFS range 75302..75302). -/
theorem sub_135125 : (ArchTree.t135125.leavesR [5, 2, 1, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths).drop 334).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135125 : ∀ q ∈ ArchTree.t135125.leavesR [5, 2, 1, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths).drop 334).take 1 := by
    rw [← sub_135125]; exact List.mem_map_of_mem hq
  exact Cs.C0061.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135134`: 454 archived leaves (DFS range 75303..75756). -/
theorem sub_135134 : (ArchTree.t135134.leavesR [4, 3, 1, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths).drop 335).take 454 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135134 : ∀ q ∈ ArchTree.t135134.leavesR [4, 3, 1, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths).drop 335).take 454 := by
    rw [← sub_135134]; exact List.mem_map_of_mem hq
  exact Cs.C0061.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `135135`: 790 archived leaves (DFS range 75757..76546). -/
theorem sub_135135 : (ArchTree.t135135.leavesR [5, 3, 1, 5, 3, 1]).map Prod.fst =
    ((Cs.C0061.paths ++ Cs.C0062.paths).drop 789).take 790 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_135135 : ∀ q ∈ ArchTree.t135135.leavesR [5, 3, 1, 5, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0061.paths ++ Cs.C0062.paths).drop 789).take 790 := by
    rw [← sub_135135]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' Cs.C0061.leafOK Cs.C0062.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm


