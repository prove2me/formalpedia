-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BA_Top_t034
-- name    : CK_CKLaneC_RSC2_BA_Top_t034
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T06:22:58.283514+00:00
-- url     : https://prove2.me/theorems/ea42a945-c259-4b8f-8c22-221bbee7f43e
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BA_Top (subtrees t_034)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BA_Top (subtrees t_034)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BA_Top (subtrees t_034)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BA_Top (subtrees t_034) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BA_Top (subtrees t_034).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BA_Top_t030
import Definitions.Def_CK_CKLaneC_RSC2_BA_Top_t033

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BA_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BA_Top
open CKLaneC.RSCell

theorem t_034 : RegionPosI 3458764513820540928 4611686018427387904 0 4611686018427387904 2305843009213693952 6341068275337658368 :=
  (RegionPosI.split_b 4035225266123964416 CKLaneC.RSC2.BA_Top.t_030 CKLaneC.RSC2.BA_Top.t_033)

end CKLaneC.RSC2.BA_Top


