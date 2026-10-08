-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t143
-- name    : CK_CKLaneC_RSC2_BD_Top_q00_t143
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T13:03:15.194903+00:00
-- url     : https://prove2.me/theorems/36407ef8-650d-4a47-bb93-d0f048a66317
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BD_Top (subtrees t_143)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BD_Top (subtrees t_143)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BD_Top (subtrees t_143)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BD_Top (subtrees t_143) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BD_Top (subtrees t_143).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t139
import Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t142

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BD_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BD_Top
open CKLaneC.RSCell

theorem t_143 : RegionPosI 8070450532247928832 8646911284551352320 13835058055282163712 16140901064495857664 16429131440647569408 18446744073709551616 :=
  (RegionPosI.split_s 17437937757178560512 CKLaneC.RSC2.BD_Top.t_139 CKLaneC.RSC2.BD_Top.t_142)

end CKLaneC.RSC2.BD_Top


