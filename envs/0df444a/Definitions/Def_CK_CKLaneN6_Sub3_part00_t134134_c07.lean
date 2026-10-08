-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub3_part00_t134134_c07
-- name    : CK_CKLaneN6_Sub3_part00_t134134_c07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T11:42:35.647728+00:00
-- url     : https://prove2.me/theorems/3bc0226c-137e-4f9f-a4fa-b05ec28ec8e5
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3 (subtree 134134 chunk 07)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3 (subtree 134134 chunk 07)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3 (subtree 134134 chunk 07)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (subtree 134134 chunk 07) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3 (subtree 134134 chunk 07).lean)

import Definitions.Def_CK_CKLaneN6_Tree
import Definitions.Def_CK_CKLaneN6_AsmBase
import Definitions.Def_CK_CKLaneN6_SubSplitBase
import Definitions.Def_CK_CKLaneN6_Cs_C0036__2

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8

set_option maxHeartbeats 0 in
theorem sub_134134_c07 : (ArchTree.t134134.splR.splR.splL.splR.splR.splR.splR.splL.splL.leavesR [2, 4, 1, 3, 1, 3, 0, 3, 1, 4, 3, 1, 4, 3, 1]).map Prod.fst =
    ((Cs.C0036.paths).drop 6).take 210 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134134_c07 : ∀ q ∈ ArchTree.t134134.splR.splR.splL.splR.splR.splR.splR.splL.splL.leavesR [2, 4, 1, 3, 1, 3, 0, 3, 1, 4, 3, 1, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0036.paths).drop 6).take 210 := by
    rw [← sub_134134_c07]; exact List.mem_map_of_mem hq
  exact (Cs.C0036.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm


