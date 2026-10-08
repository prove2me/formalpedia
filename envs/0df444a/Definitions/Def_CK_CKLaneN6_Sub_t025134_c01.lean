-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub_t025134_c01
-- name    : CK_CKLaneN6_Sub_t025134_c01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T02:16:16.531402+00:00
-- url     : https://prove2.me/theorems/72d62e8a-87ff-4d6e-84c4-e0d8ef46e6c3
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub (subtree 025134 chunk 01)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub (subtree 025134 chunk 01)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub (subtree 025134 chunk 01)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub (subtree 025134 chunk 01) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub (subtree 025134 chunk 01).lean)

import Definitions.Def_CK_CKLaneN6_Tree
import Definitions.Def_CK_CKLaneN6_AsmBase
import Definitions.Def_CK_CKLaneN6_SubSplitBase
import Definitions.Def_CK_CKLaneN6_Cs_C0013__2

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8

set_option maxHeartbeats 0 in
theorem sub_025134_c01 : (ArchTree.t025134.splL.splL.splL.splL.splL.splL.splR.leavesR [5, 2, 0, 4, 4, 4, 4, 4, 3, 1, 5, 2, 0]).map Prod.fst =
    ((Cs.C0013.paths).drop 1954).take 895 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_025134_c01 : ∀ q ∈ ArchTree.t025134.splL.splL.splL.splL.splL.splL.splR.leavesR [5, 2, 0, 4, 4, 4, 4, 4, 3, 1, 5, 2, 0], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0013.paths).drop 1954).take 895 := by
    rw [← sub_025134_c01]; exact List.mem_map_of_mem hq
  exact (Cs.C0013.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm


