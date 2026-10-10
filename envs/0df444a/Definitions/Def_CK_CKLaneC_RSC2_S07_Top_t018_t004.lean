-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S07_Top_t018_t004
-- name    : CK_CKLaneC_RSC2_S07_Top_t018_t004
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T15:25:15.427898+00:00
-- url     : https://prove2.me/theorems/2b55c9d0-ec32-4220-9c92-d6c5baabe7ab
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S07_Top (subtrees t_018_004)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S07_Top (subtrees t_018_004)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S07_Top (subtrees t_018_004)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S07_Top (subtrees t_018_004) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S07_Top (subtrees t_018_004).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S07_0065
import Definitions.Def_CK_CKLaneC_RSC2_S07_0066

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S07_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S07_Top
open CKLaneC.RSCell

theorem t_018_004 : RegionPosI 108086391056891904 144115188075855872 4611686018427387904 9223372036854775808 9223372036854775808 13835058055282163712 :=
  (RegionPosI.split_s 11529215046068469760 CKLaneC.RSC2.S07_0065.region CKLaneC.RSC2.S07_0066.region)

end CKLaneC.RSC2.S07_Top


