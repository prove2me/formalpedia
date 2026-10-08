-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BA_Top_t068
-- name    : CK_CKLaneC_RSC2_BA_Top_t068
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T16:27:41.199355+00:00
-- url     : https://prove2.me/theorems/25753714-59b2-457c-bad7-64ceabdfcf4c
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BA_Top (subtrees t_068)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BA_Top (subtrees t_068)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BA_Top (subtrees t_068)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BA_Top (subtrees t_068) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BA_Top (subtrees t_068).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BA_0108
import Definitions.Def_CK_CKLaneC_RSC2_BA_0109
import Definitions.Def_CK_CKLaneC_RSC2_BA_0110
import Definitions.Def_CK_CKLaneC_RSC2_BA_0111

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BA_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BA_Top
open CKLaneC.RSCell

theorem t_068 : RegionPosI 2882303761517117440 3458764513820540928 11529215046068469760 13835058055282163712 2305843009213693952 4323455642275676160 :=
  (RegionPosI.split_b 3170534137668829184 (RegionPosI.split_t 12682136550675316736 CKLaneC.RSC2.BA_0108.region CKLaneC.RSC2.BA_0109.region) (RegionPosI.split_t 12682136550675316736 CKLaneC.RSC2.BA_0110.region CKLaneC.RSC2.BA_0111.region))

end CKLaneC.RSC2.BA_Top


