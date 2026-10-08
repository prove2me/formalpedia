-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t105
-- name    : CK_CKLaneC_RSC2_BD_Top_q00_t105
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T11:33:45.730761+00:00
-- url     : https://prove2.me/theorems/65751ca5-3e9c-4fb4-af21-6cfe2e7c3004
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.BD_Top (subtrees t_105)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.BD_Top (subtrees t_105)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.BD_Top (subtrees t_105)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.BD_Top (subtrees t_105) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/BD_Top (subtrees t_105).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t102
import Definitions.Def_CK_CKLaneC_RSC2_BD_Top_q00_t104

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.BD_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.BD_Top
open CKLaneC.RSCell

theorem t_105 : RegionPosI 8935141660703064064 9223372036854775808 9223372036854775808 11529215046068469760 16429131440647569408 18446744073709551616 :=
  (RegionPosI.split_t 10376293541461622784 (RegionPosI.split_s 17437937757178560512 CKLaneC.RSC2.BD_Top.t_102 (RegionPosI.excl 8935141660703064064 9223372036854775808 9223372036854775808 10376293541461622784 17437937757178560512 18446744073709551616 (by decide +kernel))) (RegionPosI.split_s 17437937757178560512 CKLaneC.RSC2.BD_Top.t_104 (RegionPosI.excl 8935141660703064064 9223372036854775808 10376293541461622784 11529215046068469760 17437937757178560512 18446744073709551616 (by decide +kernel))))

end CKLaneC.RSC2.BD_Top


