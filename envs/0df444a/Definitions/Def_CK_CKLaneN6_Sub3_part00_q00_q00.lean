-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub3_part00_q00_q00
-- name    : CK_CKLaneN6_Sub3_part00_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T10:03:05.131888+00:00
-- url     : https://prove2.me/theorems/1cdd7ae0-12bd-4ce2-8197-8fc60484cc79
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3 (part 1 of 2) (piece 1 of 3) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3 (part 1 of 2) (piece 1 of 3) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3 (part 1 of 2) (piece 1 of 3) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (part 1 of 2) (piece 1 of 3) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3 (part 1 of 2) (piece 1 of 3) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneN6_Sub3_part00_q00_q00_q00

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8
theorem subOK_134024 : ∀ q ∈ ArchTree.t134024.leavesR [4, 2, 0, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0016.paths ++ Cs.C0017.paths ++ Cs.C0018.paths).drop 661).take 1144 := by
    rw [← sub_134024]; exact List.mem_map_of_mem hq
  exact (forall_mem_append' (forall_mem_append' Cs.C0016.leafOK Cs.C0017.leafOK) Cs.C0018.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm


