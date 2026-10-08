-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t015
-- name    : CK_CKLaneC_RSC2_BD_Top_q00_t015
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T10:29:22.507088+00:00
-- url     : https://prove2.me/theorems/d9a9a710-3616-43df-8e8a-d6c298a97a72
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BD_Top (subtrees t_015)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BD_Top (subtrees t_015)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BD_Top (subtrees t_015)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BD_Top (subtrees t_015) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BD_Top (subtrees t_015).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t013
import Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t014

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BD_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BD_Top
open CKLaneC.RSCell

theorem t_015 : RegionPosI 8070450532247928832 8646911284551352320 0 4611686018427387904 14411518807585587200 18446744073709551616 :=
  (RegionPosI.split_t 2305843009213693952 CKLaneC.RSC2.BD_Top.t_013 CKLaneC.RSC2.BD_Top.t_014)

end CKLaneC.RSC2.BD_Top


