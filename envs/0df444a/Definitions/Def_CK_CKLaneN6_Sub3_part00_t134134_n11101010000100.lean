-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub3_part00_t134134_n11101010000100
-- name    : CK_CKLaneN6_Sub3_part00_t134134_n11101010000100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T15:41:36.019478+00:00
-- url     : https://prove2.me/theorems/0cce1388-ad10-4d8b-9076-9a0875147d20
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3 (subtree 134134 combine node 11101010000100)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3 (subtree 134134 combine node 11101010000100)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3 (subtree 134134 combine node 11101010000100)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (subtree 134134 combine node 11101010000100) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3 (subtree 134134 combine node 11101010000100).lean)

import Definitions.Def_CK_CKLaneN6_Sub3_part00_t134134_c31
import Definitions.Def_CK_CKLaneN6_Sub3_part00_t134134_n111010100001001

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8

theorem subOK_134134_n11101010000100 : ∀ q ∈ ArchTree.t134134.splR.splR.splR.splL.splR.splL.splR.splL.splL.splL.splL.splR.splL.splL.leavesR [0, 4, 3, 4, 4, 4, 4, 1, 4, 3, 4, 1, 3, 1, 4, 3, 1, 4, 3, 1], LeafOK (feBox q.1) :=
  PTree.forall_leavesR_spl ArchTree.t134134.splR.splR.splR.splL.splR.splL.splR.splL.splL.splL.splL.splR.splL.splL [0, 4, 3, 4, 4, 4, 4, 1, 4, 3, 4, 1, 3, 1, 4, 3, 1, 4, 3, 1] [2, 0, 4, 3, 4, 4, 4, 4, 1, 4, 3, 4, 1, 3, 1, 4, 3, 1, 4, 3, 1] [3, 0, 4, 3, 4, 4, 4, 4, 1, 4, 3, 4, 1, 3, 1, 4, 3, 1, 4, 3, 1] rfl rfl rfl subOK_134134_c31 subOK_134134_n111010100001001

end CKLaneN6.Asm


