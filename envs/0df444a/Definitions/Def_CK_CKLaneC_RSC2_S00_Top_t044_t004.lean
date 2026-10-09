-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S00_Top_t044_t004
-- name    : CK_CKLaneC_RSC2_S00_Top_t044_t004
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T18:17:40.399984+00:00
-- url     : https://prove2.me/theorems/ec0bb905-dc37-4bfb-82fb-fd10758505b0
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S00_Top (subtrees t_044_004)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S00_Top (subtrees t_044_004)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S00_Top (subtrees t_044_004)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S00_Top (subtrees t_044_004) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S00_Top (subtrees t_044_004).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S00_Top_t044_t003
import Definitions.Def_CK_CKLaneC_RSC2_S00_0154

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S00_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S00_Top
open CKLaneC.RSCell

theorem t_044_004 : RegionPosI 985162418487296 1125899906842624 9223372036854775808 13835058055282163712 13835058055282163712 18446744073709551616 :=
  (RegionPosI.split_s 16140901064495857664 CKLaneC.RSC2.S00_Top.t_044_003 CKLaneC.RSC2.S00_0154.region)

end CKLaneC.RSC2.S00_Top


