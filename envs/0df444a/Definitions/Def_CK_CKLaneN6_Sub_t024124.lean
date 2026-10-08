-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub_t024124
-- name    : CK_CKLaneN6_Sub_t024124
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T02:39:10.510885+00:00
-- url     : https://prove2.me/theorems/5a5ef8c8-c794-4432-84db-bf31c7697962
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub (subtree 024124)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub (subtree 024124)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub (subtree 024124)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub (subtree 024124) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub (subtree 024124).lean)

import Definitions.Def_CK_CKLaneN6_Tree
import Definitions.Def_CK_CKLaneN6_AsmBase
import Definitions.Def_CK_CKLaneN6_Cs_C0003

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8
set_option maxHeartbeats 0 in
/-- Subtree `024124`: 1 archived leaves (DFS range 14455..14455). -/
theorem sub_024124 : (ArchTree.t024124.leavesR [4, 2, 1, 4, 2, 0]).map Prod.fst =
    ((Cs.C0003.paths).drop 1537).take 1 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_024124 : ∀ q ∈ ArchTree.t024124.leavesR [4, 2, 1, 4, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0003.paths).drop 1537).take 1 := by
    rw [← sub_024124]; exact List.mem_map_of_mem hq
  exact Cs.C0003.leafOK q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm


