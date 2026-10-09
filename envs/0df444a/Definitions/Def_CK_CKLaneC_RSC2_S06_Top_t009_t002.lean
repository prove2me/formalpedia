-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S06_Top_t009_t002
-- name    : CK_CKLaneC_RSC2_S06_Top_t009_t002
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T01:23:10.636693+00:00
-- url     : https://prove2.me/theorems/c0871844-3e9f-4160-96d4-ad7274c9fc64
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S06_Top (subtrees t_009_002)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S06_Top (subtrees t_009_002)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S06_Top (subtrees t_009_002)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S06_Top (subtrees t_009_002) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S06_Top (subtrees t_009_002).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S06_0033
import Definitions.Def_CK_CKLaneC_RSC2_S06_0034

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S06_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S06_Top
open CKLaneC.RSCell

theorem t_009_002 : RegionPosI 54043195528445952 72057594037927936 13835058055282163712 18446744073709551616 3458764513820540928 4611686018427387904 :=
  (RegionPosI.split_b 63050394783186944 CKLaneC.RSC2.S06_0033.region CKLaneC.RSC2.S06_0034.region)

end CKLaneC.RSC2.S06_Top


