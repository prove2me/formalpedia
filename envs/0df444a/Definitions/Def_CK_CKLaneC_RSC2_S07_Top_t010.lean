-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S07_Top_t010
-- name    : CK_CKLaneC_RSC2_S07_Top_t010
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T10:51:08.34589+00:00
-- url     : https://prove2.me/theorems/5a7419f8-097f-4c46-aaf2-44e8225cbd56
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S07_Top (subtrees t_010)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S07_Top (subtrees t_010)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S07_Top (subtrees t_010)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S07_Top (subtrees t_010) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S07_Top (subtrees t_010).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S07_0041
import Definitions.Def_CK_CKLaneC_RSC2_S07_0042
import Definitions.Def_CK_CKLaneC_RSC2_S07_0043
import Definitions.Def_CK_CKLaneC_RSC2_S07_0044
import Definitions.Def_CK_CKLaneC_RSC2_S07_0045

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S07_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S07_Top
open CKLaneC.RSCell

theorem t_010 : RegionPosI 72057594037927936 144115188075855872 13835058055282163712 18446744073709551616 4611686018427387904 6917529027641081856 :=
  (RegionPosI.split_b 108086391056891904 (RegionPosI.split_b 90071992547409920 (RegionPosI.split_s 5764607523034234880 CKLaneC.RSC2.S07_0041.region CKLaneC.RSC2.S07_0042.region) CKLaneC.RSC2.S07_0043.region) (RegionPosI.split_s 5764607523034234880 CKLaneC.RSC2.S07_0044.region CKLaneC.RSC2.S07_0045.region))

end CKLaneC.RSC2.S07_Top


