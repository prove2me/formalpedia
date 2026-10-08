-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t061
-- name    : CK_CKLaneC_RSC2_BD_Top_q00_t061
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T21:51:47.373896+00:00
-- url     : https://prove2.me/theorems/8da9b553-3d95-4026-a188-81b446103a9f
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BD_Top (subtrees t_061)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BD_Top (subtrees t_061)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BD_Top (subtrees t_061)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BD_Top (subtrees t_061) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BD_Top (subtrees t_061).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BD_0091
import Definitions.Def_CK_CKLaneC_RSC2_BD_0092
import Definitions.Def_CK_CKLaneC_RSC2_BD_0093

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BD_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BD_Top
open CKLaneC.RSCell

theorem t_061 : RegionPosI 8070450532247928832 8646911284551352320 13835058055282163712 16140901064495857664 2305843009213693952 6341068275337658368 :=
  (RegionPosI.split_s 4323455642275676160 (RegionPosI.split_b 8358680908399640576 CKLaneC.RSC2.BD_0091.region CKLaneC.RSC2.BD_0092.region) CKLaneC.RSC2.BD_0093.region)

end CKLaneC.RSC2.BD_Top


