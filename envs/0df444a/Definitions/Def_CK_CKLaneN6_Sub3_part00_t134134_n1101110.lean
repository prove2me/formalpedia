-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub3_part00_t134134_n1101110
-- name    : CK_CKLaneN6_Sub3_part00_t134134_n1101110
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T14:05:40.3686+00:00
-- url     : https://prove2.me/theorems/31886f12-5f69-4365-abd6-8cc7a67a90f1
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3 (subtree 134134 combine node 1101110)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3 (subtree 134134 combine node 1101110)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3 (subtree 134134 combine node 1101110)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (subtree 134134 combine node 1101110) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3 (subtree 134134 combine node 1101110).lean)

import Definitions.Def_CK_CKLaneN6_Sub3_part00_t134134_c05
import Definitions.Def_CK_CKLaneN6_Sub3_part00_t134134_c06

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8

theorem subOK_134134_n1101110 : ∀ q ∈ ArchTree.t134134.splR.splR.splL.splR.splR.splR.splL.leavesR [0, 3, 1, 3, 0, 3, 1, 4, 3, 1, 4, 3, 1], LeafOK (feBox q.1) :=
  PTree.forall_leavesR_spl ArchTree.t134134.splR.splR.splL.splR.splR.splR.splL [0, 3, 1, 3, 0, 3, 1, 4, 3, 1, 4, 3, 1] [2, 0, 3, 1, 3, 0, 3, 1, 4, 3, 1, 4, 3, 1] [3, 0, 3, 1, 3, 0, 3, 1, 4, 3, 1, 4, 3, 1] rfl rfl rfl subOK_134134_c05 subOK_134134_c06

end CKLaneN6.Asm


