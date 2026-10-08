-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S04_Top_q00_t045_t001
-- name    : CK_CKLaneC_RSC2_S04_Top_q00_t045_t001
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T23:24:30.426414+00:00
-- url     : https://prove2.me/theorems/e8db7ace-f311-4483-ac94-680751ce77d3
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S04_Top (subtrees t_045_001)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S04_Top (subtrees t_045_001)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S04_Top (subtrees t_045_001)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S04_Top (subtrees t_045_001) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S04_Top (subtrees t_045_001).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S04_Top_q00_t045_t000
import Definitions.Def_CK_CKLaneC_RSC2_S04_0142

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S04_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S04_Top
open CKLaneC.RSCell

theorem t_045_001 : RegionPosI 9007199254740992 13510798882111488 0 4611686018427387904 13835058055282163712 18446744073709551616 :=
  (RegionPosI.split_b 11258999068426240 CKLaneC.RSC2.S04_Top.t_045_000 CKLaneC.RSC2.S04_0142.region)

end CKLaneC.RSC2.S04_Top


