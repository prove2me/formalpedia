-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub_t024135_n001
-- name    : CK_CKLaneN6_Sub_t024135_n001
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T03:13:46.822185+00:00
-- url     : https://prove2.me/theorems/e1e196e3-d268-40e2-b051-823f0ea82139
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3 (subtree 024135 combine node 001)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3 (subtree 024135 combine node 001)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3 (subtree 024135 combine node 001)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (subtree 024135 combine node 001) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3 (subtree 024135 combine node 001).lean)

import Definitions.Def_CK_CKLaneN6_Sub_t024135_c01
import Definitions.Def_CK_CKLaneN6_Sub_t024135_c02

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8

theorem subOK_024135_n001 : ∀ q ∈ ArchTree.t024135.splL.splL.splR.leavesR [5, 4, 4, 5, 3, 1, 4, 2, 0], LeafOK (feBox q.1) :=
  PTree.forall_leavesR_spl ArchTree.t024135.splL.splL.splR [5, 4, 4, 5, 3, 1, 4, 2, 0] [4, 5, 4, 4, 5, 3, 1, 4, 2, 0] [5, 5, 4, 4, 5, 3, 1, 4, 2, 0] rfl rfl rfl subOK_024135_c01 subOK_024135_c02

end CKLaneN6.Asm


