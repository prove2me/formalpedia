-- Prove2me | Definitions.Def_CK_CKLaneN6_Sub_t025034
-- name    : CK_CKLaneN6_Sub_t025034
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T03:55:54.287731+00:00
-- url     : https://prove2.me/theorems/3beaf859-61f4-4ef6-a75e-2fa6a4f8a032
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Sub (subtree 025034)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Sub (subtree 025034)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Sub (subtree 025034)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Sub (subtree 025034) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Sub (subtree 025034).lean)

import Definitions.Def_CK_CKLaneN6_Sub_t025034_n0
import Definitions.Def_CK_CKLaneN6_Sub_t025034_c04

set_option autoImplicit false
namespace CKLaneN6.Asm
open CKLaneN6 CKLaneM05.FE8

theorem subOK_025034 : ∀ q ∈ ArchTree.t025034.leavesR [4, 3, 0, 5, 2, 0], LeafOK (feBox q.1) :=
  PTree.forall_leavesR_spl ArchTree.t025034 [4, 3, 0, 5, 2, 0] [4, 4, 3, 0, 5, 2, 0] [5, 4, 3, 0, 5, 2, 0] rfl rfl rfl subOK_025034_n0 subOK_025034_c04

end CKLaneN6.Asm


