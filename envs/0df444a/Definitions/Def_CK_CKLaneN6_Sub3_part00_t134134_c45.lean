-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub3_part00_t134134_c45
-- name    : CK_CKLaneN6_Sub3_part00_t134134_c45
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:25:02.133096+00:00
-- url     : https://prove2.me/theorems/1fffbe07-4b03-4aa0-afa0-1c0db6f64dd3
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3 (subtree 134134 chunk 45)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3 (subtree 134134 chunk 45)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3 (subtree 134134 chunk 45)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (subtree 134134 chunk 45) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3 (subtree 134134 chunk 45).lean)

import Definitions.Def_CK_CKLaneN6_Tree
import Definitions.Def_CK_CKLaneN6_AsmBase
import Definitions.Def_CK_CKLaneN6_SubSplitBase
import Definitions.Def_CK_CKLaneN6_Cs_C0057__3

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8

set_option maxHeartbeats 0 in
theorem sub_134134_c45 : (ArchTree.t134134.splR.splR.splR.splR.leavesR [5, 1, 3, 1, 4, 3, 1, 4, 3, 1]).map Prod.fst =
    ((Cs.C0058.paths).drop 50).take 41 :=
  pathsBeq_eq (by decide +kernel)

theorem subOK_134134_c45 : ∀ q ∈ ArchTree.t134134.splR.splR.splR.splR.leavesR [5, 1, 3, 1, 4, 3, 1, 4, 3, 1], LeafOK (feBox q.1) := by
  intro q hq
  have h1 : q.1 ∈ ((Cs.C0058.paths).drop 50).take 41 := by
    rw [← sub_134134_c45]; exact List.mem_map_of_mem hq
  exact (Cs.C0058.leafOK) q.1 (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end CKLaneN6.Asm


