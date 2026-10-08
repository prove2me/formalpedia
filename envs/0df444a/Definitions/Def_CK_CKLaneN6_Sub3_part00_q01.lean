-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub3_part00_q01
-- name    : CK_CKLaneN6_Sub3_part00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:28:22.309592+00:00
-- url     : https://prove2.me/theorems/9ca4fd28-5753-499c-bc9b-88fc867aae5c
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3 (part 1 of 2) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3 (part 1 of 2) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3 (part 1 of 2) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (part 1 of 2) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3 (part 1 of 2) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneN6_Sub3_part00_q00

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8
set_option maxHeartbeats 0 in
/-- Subtree `134035`: 212 archived leaves (DFS range 50185..50396). -/
theorem sub_134035 : (ArchTree.t134035.leavesR [5, 3, 0, 4, 3, 1]).map Prod.fst =
    ((Cs.C0021.paths).drop 15).take 212 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134035 : ∀ q ∈ ArchTree.t134035.leavesR [5, 3, 0, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0021.paths).drop 15).take 212 := by
    rw [← sub_134035]; exact List.mem_map_of_mem hq
  exact Cs.C0021.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `134124`: 1 archived leaves (DFS range 50397..50397). -/
theorem sub_134124 : (ArchTree.t134124.leavesR [4, 2, 1, 4, 3, 1]).map Prod.fst =
    ((Cs.C0021.paths).drop 227).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134124 : ∀ q ∈ ArchTree.t134124.leavesR [4, 2, 1, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0021.paths).drop 227).take 1 := by
    rw [← sub_134124]; exact List.mem_map_of_mem hq
  exact Cs.C0021.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

set_option maxHeartbeats 0 in
/-- Subtree `134125`: 1 archived leaves (DFS range 50398..50398). -/
theorem sub_134125 : (ArchTree.t134125.leavesR [5, 2, 1, 4, 3, 1]).map Prod.fst =
    ((Cs.C0021.paths).drop 228).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134125 : ∀ q ∈ ArchTree.t134125.leavesR [5, 2, 1, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0021.paths).drop 228).take 1 := by
    rw [← sub_134125]; exact List.mem_map_of_mem hq
  exact Cs.C0021.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm


