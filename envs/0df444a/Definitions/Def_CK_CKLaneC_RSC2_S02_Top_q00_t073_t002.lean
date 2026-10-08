-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S02_Top_q00_t073_t002
-- name    : CK_CKLaneC_RSC2_S02_Top_q00_t073_t002
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T21:32:20.479983+00:00
-- url     : https://prove2.me/theorems/28663ebf-06ae-49a3-9d53-460a395e1589
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S02_Top (subtrees t_073_002)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S02_Top (subtrees t_073_002)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S02_Top (subtrees t_073_002)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S02_Top (subtrees t_073_002) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S02_Top (subtrees t_073_002).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S02_0221
import Definitions.Def_CK_CKLaneC_RSC2_S02_0222

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S02_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S02_Top
open CKLaneC.RSCell

theorem t_073_002 : RegionPosI 2814749767106560 3377699720527872 0 4611686018427387904 13835058055282163712 18446744073709551616 :=
  (RegionPosI.split_s 16140901064495857664 CKLaneC.RSC2.S02_0221.region CKLaneC.RSC2.S02_0222.region)

end CKLaneC.RSC2.S02_Top


