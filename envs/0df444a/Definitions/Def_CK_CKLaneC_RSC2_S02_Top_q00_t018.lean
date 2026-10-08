-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S02_Top_q00_t018
-- name    : CK_CKLaneC_RSC2_S02_Top_q00_t018
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T02:59:10.067599+00:00
-- url     : https://prove2.me/theorems/2b618868-9a39-4842-a18c-cf39059de5d9
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S02_Top (subtrees t_018)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S02_Top (subtrees t_018)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S02_Top (subtrees t_018)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S02_Top (subtrees t_018) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S02_Top (subtrees t_018).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S02_0061
import Definitions.Def_CK_CKLaneC_RSC2_S02_0062
import Definitions.Def_CK_CKLaneC_RSC2_S02_0063
import Definitions.Def_CK_CKLaneC_RSC2_S02_0064
import Definitions.Def_CK_CKLaneC_RSC2_S02_0065

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S02_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S02_Top
open CKLaneC.RSCell

theorem t_018 : RegionPosI 2251799813685248 3377699720527872 9223372036854775808 13835058055282163712 3458764513820540928 4611686018427387904 :=
  (RegionPosI.split_b 2814749767106560 (RegionPosI.split_s 4035225266123964416 (RegionPosI.split_b 2533274790395904 CKLaneC.RSC2.S02_0061.region CKLaneC.RSC2.S02_0062.region) CKLaneC.RSC2.S02_0063.region) (RegionPosI.split_s 4035225266123964416 CKLaneC.RSC2.S02_0064.region CKLaneC.RSC2.S02_0065.region))

end CKLaneC.RSC2.S02_Top


