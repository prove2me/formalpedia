-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t109
-- name    : CK_CKLaneC_RSC2_BD_Top_q00_t109
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T03:26:00.636853+00:00
-- url     : https://prove2.me/theorems/6ffcf4bb-5ec8-47a6-9d62-f16d3e960626
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BD_Top (subtrees t_109)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BD_Top (subtrees t_109)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BD_Top (subtrees t_109)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BD_Top (subtrees t_109) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BD_Top (subtrees t_109).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BD_0172
import Definitions.Def_CK_CKLaneC_RSC2_BD_0173
import Definitions.Def_CK_CKLaneC_RSC2_BD_0174

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BD_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BD_Top
open CKLaneC.RSCell

theorem t_109 : RegionPosI 8646911284551352320 9223372036854775808 11529215046068469760 12105675798371893248 15924728282382073856 16429131440647569408 :=
  (RegionPosI.split_s 16176929861514821632 CKLaneC.RSC2.BD_0172.region (RegionPosI.split_b 8935141660703064064 CKLaneC.RSC2.BD_0173.region CKLaneC.RSC2.BD_0174.region))

end CKLaneC.RSC2.BD_Top


