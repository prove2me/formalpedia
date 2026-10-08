-- Prove2me | Definitions.Def_CK_CKLaneC_RSC2_S02_Top_q00_t025
-- name    : CK_CKLaneC_RSC2_S02_Top_q00_t025
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T13:21:07.787148+00:00
-- url     : https://prove2.me/theorems/f41e086c-0358-4e88-8904-76707ee7769f
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSC2.S02_Top (subtrees t_025)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSC2.S02_Top (subtrees t_025)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSC2.S02_Top (subtrees t_025)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSC2.S02_Top (subtrees t_025) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSC2/S02_Top (subtrees t_025).lean)

import Definitions.Def_CK_CKLaneC_RSCell_RegionI
import Definitions.Def_CK_CKLaneC_RSC2_S02_Top_q00_t017
import Definitions.Def_CK_CKLaneC_RSC2_S02_Top_q00_t024

/-! RA-stat cover: subtree of the root assembly of CKLaneC.RSC2.S02_Top (split by rsc2tree.py; term verbatim). -/

namespace CKLaneC.RSC2.S02_Top
open CKLaneC.RSCell

theorem t_025 : RegionPosI 2251799813685248 4503599627370496 0 18446744073709551616 3458764513820540928 4611686018427387904 :=
  (RegionPosI.split_t 9223372036854775808 CKLaneC.RSC2.S02_Top.t_017 CKLaneC.RSC2.S02_Top.t_024)

end CKLaneC.RSC2.S02_Top


