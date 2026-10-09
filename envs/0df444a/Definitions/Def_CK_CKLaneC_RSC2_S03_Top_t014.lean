-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S03_Top_t014
-- name    : CK_CKLaneC_RSC2_S03_Top_t014
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T17:05:22.141712+00:00
-- url     : https://prove2.me/theorems/0b153918-2805-4674-9b5b-b7024bedfd28
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S03_Top (subtrees t_014)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S03_Top (subtrees t_014)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S03_Top (subtrees t_014)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S03_Top (subtrees t_014) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S03_Top (subtrees t_014).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S03_0045
import Definitions.Def_CK_CKLaneC_RSC2_S03_0046
import Definitions.Def_CK_CKLaneC_RSC2_S03_0047
import Definitions.Def_CK_CKLaneC_RSC2_S03_0048
import Definitions.Def_CK_CKLaneC_RSC2_S03_0049
import Definitions.Def_CK_CKLaneC_RSC2_S03_0050

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S03_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S03_Top
open CKLaneC.RSCell

theorem t_014 : RegionPosI 4503599627370496 9007199254740992 4611686018427387904 9223372036854775808 3458764513820540928 4611686018427387904 :=
  (RegionPosI.split_b 6755399441055744 (RegionPosI.split_b 5629499534213120 (RegionPosI.split_s 4035225266123964416 CKLaneC.RSC2.S03_0045.region CKLaneC.RSC2.S03_0046.region) (RegionPosI.split_s 4035225266123964416 CKLaneC.RSC2.S03_0047.region CKLaneC.RSC2.S03_0048.region)) (RegionPosI.split_b 7881299347898368 CKLaneC.RSC2.S03_0049.region CKLaneC.RSC2.S03_0050.region))

end CKLaneC.RSC2.S03_Top


