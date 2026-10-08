-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub2
-- name    : CK_CKLaneN6_Sub2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:09:16.716083+00:00
-- url     : https://prove2.me/theorems/c185b41c-9a61-4da9-bcfc-189988cacf82
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub2.lean)

import Definitions.Def_CK_CKLaneN6_Tree
import Definitions.Def_CK_CKLaneN6_AsmBase
import Definitions.Def_CK_CKLaneN6_Cs_C0016__3

-- ===== source module CKLaneN6.Sub2 =====
section

/-! Lane N6 assembly part 2: depth-6 subtrees 124024..125135 of the archived tree, each
matched (kernel decide over the overlapping coarse shards only) with the shard leaf lists. -/

set_option autoImplicit false

namespace CKLaneN6.Asm

open CKLaneN6 CKLaneM05.FE8

set_option maxHeartbeats 0 in
/-- Subtree `124024`: 1 archived leaves (DFS range 47485..47485). -/
theorem sub_124024 : (ArchTree.t124024.leavesR [4, 2, 0, 4, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 645).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_124024 : ∀ q ∈ ArchTree.t124024.leavesR [4, 2, 0, 4, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 645).take 1 := by
    rw [← sub_124024]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `124025`: 1 archived leaves (DFS range 47486..47486). -/
theorem sub_124025 : (ArchTree.t124025.leavesR [5, 2, 0, 4, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 646).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_124025 : ∀ q ∈ ArchTree.t124025.leavesR [5, 2, 0, 4, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 646).take 1 := by
    rw [← sub_124025]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `124034`: 1 archived leaves (DFS range 47487..47487). -/
theorem sub_124034 : (ArchTree.t124034.leavesR [4, 3, 0, 4, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 647).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_124034 : ∀ q ∈ ArchTree.t124034.leavesR [4, 3, 0, 4, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 647).take 1 := by
    rw [← sub_124034]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `124035`: 1 archived leaves (DFS range 47488..47488). -/
theorem sub_124035 : (ArchTree.t124035.leavesR [5, 3, 0, 4, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 648).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_124035 : ∀ q ∈ ArchTree.t124035.leavesR [5, 3, 0, 4, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 648).take 1 := by
    rw [← sub_124035]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `124124`: 1 archived leaves (DFS range 47489..47489). -/
theorem sub_124124 : (ArchTree.t124124.leavesR [4, 2, 1, 4, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 649).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_124124 : ∀ q ∈ ArchTree.t124124.leavesR [4, 2, 1, 4, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 649).take 1 := by
    rw [← sub_124124]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `124125`: 1 archived leaves (DFS range 47490..47490). -/
theorem sub_124125 : (ArchTree.t124125.leavesR [5, 2, 1, 4, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 650).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_124125 : ∀ q ∈ ArchTree.t124125.leavesR [5, 2, 1, 4, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 650).take 1 := by
    rw [← sub_124125]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `124134`: 1 archived leaves (DFS range 47491..47491). -/
theorem sub_124134 : (ArchTree.t124134.leavesR [4, 3, 1, 4, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 651).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_124134 : ∀ q ∈ ArchTree.t124134.leavesR [4, 3, 1, 4, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 651).take 1 := by
    rw [← sub_124134]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `124135`: 1 archived leaves (DFS range 47492..47492). -/
theorem sub_124135 : (ArchTree.t124135.leavesR [5, 3, 1, 4, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 652).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_124135 : ∀ q ∈ ArchTree.t124135.leavesR [5, 3, 1, 4, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 652).take 1 := by
    rw [← sub_124135]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `125024`: 1 archived leaves (DFS range 47493..47493). -/
theorem sub_125024 : (ArchTree.t125024.leavesR [4, 2, 0, 5, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 653).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_125024 : ∀ q ∈ ArchTree.t125024.leavesR [4, 2, 0, 5, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 653).take 1 := by
    rw [← sub_125024]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `125025`: 1 archived leaves (DFS range 47494..47494). -/
theorem sub_125025 : (ArchTree.t125025.leavesR [5, 2, 0, 5, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 654).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_125025 : ∀ q ∈ ArchTree.t125025.leavesR [5, 2, 0, 5, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 654).take 1 := by
    rw [← sub_125025]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `125034`: 1 archived leaves (DFS range 47495..47495). -/
theorem sub_125034 : (ArchTree.t125034.leavesR [4, 3, 0, 5, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 655).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_125034 : ∀ q ∈ ArchTree.t125034.leavesR [4, 3, 0, 5, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 655).take 1 := by
    rw [← sub_125034]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `125035`: 1 archived leaves (DFS range 47496..47496). -/
theorem sub_125035 : (ArchTree.t125035.leavesR [5, 3, 0, 5, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 656).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_125035 : ∀ q ∈ ArchTree.t125035.leavesR [5, 3, 0, 5, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 656).take 1 := by
    rw [← sub_125035]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `125124`: 1 archived leaves (DFS range 47497..47497). -/
theorem sub_125124 : (ArchTree.t125124.leavesR [4, 2, 1, 5, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 657).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_125124 : ∀ q ∈ ArchTree.t125124.leavesR [4, 2, 1, 5, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 657).take 1 := by
    rw [← sub_125124]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `125125`: 1 archived leaves (DFS range 47498..47498). -/
theorem sub_125125 : (ArchTree.t125125.leavesR [5, 2, 1, 5, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 658).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_125125 : ∀ q ∈ ArchTree.t125125.leavesR [5, 2, 1, 5, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 658).take 1 := by
    rw [← sub_125125]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `125134`: 1 archived leaves (DFS range 47499..47499). -/
theorem sub_125134 : (ArchTree.t125134.leavesR [4, 3, 1, 5, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 659).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_125134 : ∀ q ∈ ArchTree.t125134.leavesR [4, 3, 1, 5, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 659).take 1 := by
    rw [← sub_125134]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `125135`: 1 archived leaves (DFS range 47500..47500). -/
theorem sub_125135 : (ArchTree.t125135.leavesR [5, 3, 1, 5, 2, 1]).map Prod.fst =
    ((Cs.C0016.paths).drop 660).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_125135 : ∀ q ∈ ArchTree.t125135.leavesR [5, 3, 1, 5, 2, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths).drop 660).take 1 := by
    rw [← sub_125135]; exact List.mem_map_of_mem hq
  exact Cs.C0016.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm

end


