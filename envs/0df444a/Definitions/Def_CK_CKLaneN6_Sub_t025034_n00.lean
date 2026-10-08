-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub_t025034_n00
-- name    : CK_CKLaneN6_Sub_t025034_n00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T03:06:12.024335+00:00
-- url     : https://prove2.me/theorems/4d708737-8672-46f3-85db-a1052acea010
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub3 (subtree 025034 combine node 00)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub3 (subtree 025034 combine node 00)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub3 (subtree 025034 combine node 00)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub3 (subtree 025034 combine node 00) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub3 (subtree 025034 combine node 00).lean)

import Definitions.Def_CK_CKLaneN6_Sub_t025034_n000
import Definitions.Def_CK_CKLaneN6_Sub_t025034_c02

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8

theorem subOK_025034_n00 : ∀ q ∈ ArchTree.t025034.splL.splL.leavesR [4, 4, 4, 3, 0, 5, 2, 0], LeafOK (feBox q.1) :=
  PTree.forall_leavesR_spl ArchTree.t025034.splL.splL [4, 4, 4, 3, 0, 5, 2, 0] [4, 4, 4, 4, 3, 0, 5, 2, 0] [5, 4, 4, 4, 3, 0, 5, 2, 0] rfl rfl rfl subOK_025034_n000 subOK_025034_c02

end CKLaneN6.Asm


