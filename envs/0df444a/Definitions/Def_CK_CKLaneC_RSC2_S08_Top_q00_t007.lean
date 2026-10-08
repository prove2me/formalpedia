-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S08_Top_q00_t007
-- name    : CK_CKLaneC_RSC2_S08_Top_q00_t007
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T07:56:34.273965+00:00
-- url     : https://prove2.me/theorems/6ff8960c-3f6f-4d71-a579-03a1cc8c0439
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S08_Top (subtrees t_007)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S08_Top (subtrees t_007)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S08_Top (subtrees t_007)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S08_Top (subtrees t_007) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S08_Top (subtrees t_007).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S08_0029
import Definitions.Def_CK_CKLaneC_RSC2_S08_0030
import Definitions.Def_CK_CKLaneC_RSC2_S08_0031
import Definitions.Def_CK_CKLaneC_RSC2_S08_0032
import Definitions.Def_CK_CKLaneC_RSC2_S08_0033
import Definitions.Def_CK_CKLaneC_RSC2_S08_0034
import Definitions.Def_CK_CKLaneC_RSC2_S08_0035

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S08_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S08_Top
open CKLaneC.RSCell

theorem t_007 : RegionPosI 144115188075855872 288230376151711744 9223372036854775808 18446744073709551616 4611686018427387904 6917529027641081856 :=
  (RegionPosI.split_t 13835058055282163712 (RegionPosI.split_b 216172782113783808 (RegionPosI.split_b 180143985094819840 CKLaneC.RSC2.S08_0029.region CKLaneC.RSC2.S08_0030.region) CKLaneC.RSC2.S08_0031.region) (RegionPosI.split_b 216172782113783808 (RegionPosI.split_b 180143985094819840 CKLaneC.RSC2.S08_0032.region CKLaneC.RSC2.S08_0033.region) (RegionPosI.split_s 5764607523034234880 CKLaneC.RSC2.S08_0034.region CKLaneC.RSC2.S08_0035.region)))

end CKLaneC.RSC2.S08_Top


