-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t153
-- name    : CK_CKLaneC_RSC2_BD_Top_q00_t153
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T03:56:48.011257+00:00
-- url     : https://prove2.me/theorems/f6df374a-01d1-4c84-bc4e-7631fa8b8814
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BD_Top (subtrees t_153)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BD_Top (subtrees t_153)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BD_Top (subtrees t_153)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BD_Top (subtrees t_153) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BD_Top (subtrees t_153).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BD_0234
import Definitions.Def_CK_CKLaneC_RSC2_BD_0235
import Definitions.Def_CK_CKLaneC_RSC2_BD_0236

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BD_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BD_Top
open CKLaneC.RSCell

theorem t_153 : RegionPosI 8646911284551352320 9223372036854775808 14987979559889010688 16140901064495857664 15420325124116578304 16429131440647569408 :=
  (RegionPosI.split_b 8935141660703064064 CKLaneC.RSC2.BD_0234.region (RegionPosI.split_s 15924728282382073856 CKLaneC.RSC2.BD_0235.region CKLaneC.RSC2.BD_0236.region))

end CKLaneC.RSC2.BD_Top


