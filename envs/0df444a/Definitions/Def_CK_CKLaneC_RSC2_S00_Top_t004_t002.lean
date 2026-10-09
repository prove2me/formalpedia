-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S00_Top_t004_t002
-- name    : CK_CKLaneC_RSC2_S00_Top_t004_t002
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T04:19:52.912851+00:00
-- url     : https://prove2.me/theorems/d65a5cc5-2c8b-46c4-9da5-27c626d3931a
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S00_Top (subtrees t_004_002)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S00_Top (subtrees t_004_002)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S00_Top (subtrees t_004_002)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S00_Top (subtrees t_004_002) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S00_Top (subtrees t_004_002).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S00_Top_t004_t000
import Definitions.Def_CK_CKLaneC_RSC2_S00_Top_t004_t001

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S00_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S00_Top
open CKLaneC.RSCell

theorem t_004_002 : RegionPosI 844424930131968 1125899906842624 13835058055282163712 18446744073709551616 2305843009213693952 2882303761517117440 :=
  (RegionPosI.split_b 985162418487296 CKLaneC.RSC2.S00_Top.t_004_000 CKLaneC.RSC2.S00_Top.t_004_001)

end CKLaneC.RSC2.S00_Top


