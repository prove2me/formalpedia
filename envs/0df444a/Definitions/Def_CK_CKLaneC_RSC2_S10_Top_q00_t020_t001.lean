-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S10_Top_q00_t020_t001
-- name    : CK_CKLaneC_RSC2_S10_Top_q00_t020_t001
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T10:11:25.605198+00:00
-- url     : https://prove2.me/theorems/7cfe90db-f8bd-4999-959c-18853881f457
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S10_Top (subtrees t_020_001)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S10_Top (subtrees t_020_001)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S10_Top (subtrees t_020_001)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S10_Top (subtrees t_020_001) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S10_Top (subtrees t_020_001).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S10_0038
import Definitions.Def_CK_CKLaneC_RSC2_S10_0039

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S10_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S10_Top
open CKLaneC.RSCell

theorem t_020_001 : RegionPosI 576460752303423488 1152921504606846976 13835058055282163712 18446744073709551616 6917529027641081856 9223372036854775808 :=
  (RegionPosI.split_b 864691128455135232 CKLaneC.RSC2.S10_0038.region CKLaneC.RSC2.S10_0039.region)

end CKLaneC.RSC2.S10_Top


