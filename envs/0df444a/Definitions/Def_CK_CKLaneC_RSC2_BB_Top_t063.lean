-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BB_Top_t063
-- name    : CK_CKLaneC_RSC2_BB_Top_t063
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T11:23:09.263271+00:00
-- url     : https://prove2.me/theorems/47e3071a-1f2a-4a24-a33c-febd11fc1564
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BB_Top (subtrees t_063)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BB_Top (subtrees t_063)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BB_Top (subtrees t_063)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BB_Top (subtrees t_063) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BB_Top (subtrees t_063).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BB_Top_t061
import Definitions.Def_CK_CKLaneC_RSC2_BB_Top_t062

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BB_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BB_Top
open CKLaneC.RSCell

theorem t_063 : RegionPosI 5188146770730811392 5764607523034234880 13835058055282163712 18446744073709551616 2305843009213693952 6341068275337658368 :=
  (RegionPosI.split_t 16140901064495857664 CKLaneC.RSC2.BB_Top.t_061 CKLaneC.RSC2.BB_Top.t_062)

end CKLaneC.RSC2.BB_Top


