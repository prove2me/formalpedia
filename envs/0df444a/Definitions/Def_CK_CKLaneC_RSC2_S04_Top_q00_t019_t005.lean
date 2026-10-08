-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S04_Top_q00_t019_t005
-- name    : CK_CKLaneC_RSC2_S04_Top_q00_t019_t005
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T02:36:17.451976+00:00
-- url     : https://prove2.me/theorems/a0ee7ccf-a50e-4250-a6ed-7754c29cc9fe
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S04_Top (subtrees t_019_005)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S04_Top (subtrees t_019_005)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S04_Top (subtrees t_019_005)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S04_Top (subtrees t_019_005) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S04_Top (subtrees t_019_005).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S04_Top_q00_t019_t004
import Definitions.Def_CK_CKLaneC_RSC2_S04_0073

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S04_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S04_Top
open CKLaneC.RSCell

theorem t_019_005 : RegionPosI 13510798882111488 18014398509481984 9223372036854775808 13835058055282163712 4611686018427387904 6917529027641081856 :=
  (RegionPosI.split_s 5764607523034234880 CKLaneC.RSC2.S04_Top.t_019_004 CKLaneC.RSC2.S04_0073.region)

end CKLaneC.RSC2.S04_Top


