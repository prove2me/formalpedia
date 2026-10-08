-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S02_Top_q00_t064_t000
-- name    : CK_CKLaneC_RSC2_S02_Top_q00_t064_t000
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:37:57.301498+00:00
-- url     : https://prove2.me/theorems/b4a2402e-999c-4525-bbeb-6319e0ed331e
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S02_Top (subtrees t_064_000)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S02_Top (subtrees t_064_000)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S02_Top (subtrees t_064_000)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S02_Top (subtrees t_064_000) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S02_Top (subtrees t_064_000).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S02_0198
import Definitions.Def_CK_CKLaneC_RSC2_S02_0199

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S02_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S02_Top
open CKLaneC.RSCell

theorem t_064_000 : RegionPosI 3377699720527872 3940649673949184 9223372036854775808 13835058055282163712 9223372036854775808 11529215046068469760 :=
  (RegionPosI.split_s 10376293541461622784 CKLaneC.RSC2.S02_0198.region CKLaneC.RSC2.S02_0199.region)

end CKLaneC.RSC2.S02_Top


