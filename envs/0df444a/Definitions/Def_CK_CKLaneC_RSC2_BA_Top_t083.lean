-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BA_Top_t083
-- name    : CK_CKLaneC_RSC2_BA_Top_t083
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T16:40:02.512489+00:00
-- url     : https://prove2.me/theorems/d53919c6-d45f-4d48-acee-63ed22c760d7
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BA_Top (subtrees t_083)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BA_Top (subtrees t_083)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BA_Top (subtrees t_083)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BA_Top (subtrees t_083) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BA_Top (subtrees t_083).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BA_0131
import Definitions.Def_CK_CKLaneC_RSC2_BA_0132
import Definitions.Def_CK_CKLaneC_RSC2_BA_0133
import Definitions.Def_CK_CKLaneC_RSC2_BA_0134

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BA_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BA_Top
open CKLaneC.RSCell

theorem t_083 : RegionPosI 2882303761517117440 3458764513820540928 13835058055282163712 16140901064495857664 2305843009213693952 4323455642275676160 :=
  (RegionPosI.split_b 3170534137668829184 (RegionPosI.split_t 14987979559889010688 CKLaneC.RSC2.BA_0131.region CKLaneC.RSC2.BA_0132.region) (RegionPosI.split_t 14987979559889010688 CKLaneC.RSC2.BA_0133.region CKLaneC.RSC2.BA_0134.region))

end CKLaneC.RSC2.BA_Top


