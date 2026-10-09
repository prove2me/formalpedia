-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S01_Top_t067_t005
-- name    : CK_CKLaneC_RSC2_S01_Top_t067_t005
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T22:34:24.037407+00:00
-- url     : https://prove2.me/theorems/5d626afe-9d41-4dff-9368-95c19f4b2e5f
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S01_Top (subtrees t_067_005)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S01_Top (subtrees t_067_005)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S01_Top (subtrees t_067_005)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S01_Top (subtrees t_067_005) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S01_Top (subtrees t_067_005).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S01_Top_t067_t003
import Definitions.Def_CK_CKLaneC_RSC2_S01_Top_t067_t004

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S01_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S01_Top
open CKLaneC.RSCell

theorem t_067_005 : RegionPosI 1407374883553280 1688849860263936 13835058055282163712 18446744073709551616 6917529027641081856 9223372036854775808 :=
  (RegionPosI.split_s 8070450532247928832 CKLaneC.RSC2.S01_Top.t_067_003 CKLaneC.RSC2.S01_Top.t_067_004)

end CKLaneC.RSC2.S01_Top


