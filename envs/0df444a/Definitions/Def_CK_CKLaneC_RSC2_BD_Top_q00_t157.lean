-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t157
-- name    : CK_CKLaneC_RSC2_BD_Top_q00_t157
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T03:45:53.58962+00:00
-- url     : https://prove2.me/theorems/8c3d3961-97f1-47d3-82da-d4406f5eee89
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BD_Top (subtrees t_157)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BD_Top (subtrees t_157)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BD_Top (subtrees t_157)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BD_Top (subtrees t_157) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BD_Top (subtrees t_157).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BD_0240
import Definitions.Def_CK_CKLaneC_RSC2_BD_0241
import Definitions.Def_CK_CKLaneC_RSC2_BD_0242
import Definitions.Def_CK_CKLaneC_RSC2_BD_0243

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BD_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BD_Top
open CKLaneC.RSCell

theorem t_157 : RegionPosI 8646911284551352320 8935141660703064064 14987979559889010688 16140901064495857664 16429131440647569408 18446744073709551616 :=
  (RegionPosI.split_s 17437937757178560512 (RegionPosI.split_s 16933534598913064960 CKLaneC.RSC2.BD_0240.region (RegionPosI.split_t 15564440312192434176 CKLaneC.RSC2.BD_0241.region CKLaneC.RSC2.BD_0242.region)) CKLaneC.RSC2.BD_0243.region)

end CKLaneC.RSC2.BD_Top


