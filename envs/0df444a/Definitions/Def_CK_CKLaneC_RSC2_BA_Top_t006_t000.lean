-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BA_Top_t006_t000
-- name    : CK_CKLaneC_RSC2_BA_Top_t006_t000
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T00:11:56.537204+00:00
-- url     : https://prove2.me/theorems/340e55e7-fcaf-4e46-9dd0-6e2d577f2232
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BA_Top (subtrees t_006_000)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BA_Top (subtrees t_006_000)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BA_Top (subtrees t_006_000)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BA_Top (subtrees t_006_000) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BA_Top (subtrees t_006_000).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BA_0013
import Definitions.Def_CK_CKLaneC_RSC2_BA_0014

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BA_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BA_Top
open CKLaneC.RSCell

theorem t_006_000 : RegionPosI 2882303761517117440 3458764513820540928 2305843009213693952 4611686018427387904 2305843009213693952 4323455642275676160 :=
  (RegionPosI.split_b 3170534137668829184 CKLaneC.RSC2.BA_0013.region CKLaneC.RSC2.BA_0014.region)

end CKLaneC.RSC2.BA_Top


