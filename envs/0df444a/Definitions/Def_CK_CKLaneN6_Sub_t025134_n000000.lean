-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub_t025134_n000000
-- name    : CK_CKLaneN6_Sub_t025134_n000000
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T02:32:37.04016+00:00
-- url     : https://prove2.me/theorems/98719c7d-4aa6-4933-893d-3230382a2a25
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3 (subtree 025134 combine node 000000)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3 (subtree 025134 combine node 000000)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3 (subtree 025134 combine node 000000)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (subtree 025134 combine node 000000) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3 (subtree 025134 combine node 000000).lean)

import Definitions.Def_CK_CKLaneN6_Sub_t025134_c00
import Definitions.Def_CK_CKLaneN6_Sub_t025134_c01

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8

theorem subOK_025134_n000000 : ∀ q ∈ ArchTree.t025134.splL.splL.splL.splL.splL.splL.leavesR [2, 0, 4, 4, 4, 4, 4, 3, 1, 5, 2, 0], LeafOK (feBox q.1) :=
  PTree.forall_leavesR_spl ArchTree.t025134.splL.splL.splL.splL.splL.splL [2, 0, 4, 4, 4, 4, 4, 3, 1, 5, 2, 0] [4, 2, 0, 4, 4, 4, 4, 4, 3, 1, 5, 2, 0] [5, 2, 0, 4, 4, 4, 4, 4, 3, 1, 5, 2, 0] rfl rfl rfl subOK_025134_c00 subOK_025134_c01

end CKLaneN6.Asm


