-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_Row4_q00_q00_q00_q00_q00_l03
-- name    : CK_CKLaneM07_CE_Row4_q00_q00_q00_q00_q00_l03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-12T07:06:15.836508+00:00
-- url     : https://prove2.me/theorems/475fc4ca-190a-4f92-9d2d-df299b38f603
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.Row4 (subtrees cells)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.Row4 (subtrees cells)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.Row4 (subtrees cells)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.Row4 (subtrees cells) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/Row4 (subtrees cells).lean)

import Definitions.Def_CK_CKLaneM07_CE_Cells_C0096__2
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0098
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0099
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0100
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0101
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0102
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0103
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0104
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0105
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0106
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0107
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0108
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0109
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0110__2
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0112
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0113
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0114
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0115
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0116
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0117__2
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0119
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0120
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0121
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0122
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0123
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0124__2
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0126
import Definitions.Def_CK_CKLaneM07_CE_Cells_C0127

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Sub-list 3 of `CKLaneM07.CE.Row4.cells` (split by split_listdef.py; elements verbatim, in order). -/

namespace CKLaneM07.CE.Row4

def cells_l03 : List CellV :=
  [CKLaneM07.CE.Cells.C0096.cl,
   CKLaneM07.CE.Cells.C0097.cl,
   CKLaneM07.CE.Cells.C0098.cl,
   CKLaneM07.CE.Cells.C0099.cl,
   CKLaneM07.CE.Cells.C0100.cl,
   CKLaneM07.CE.Cells.C0101.cl,
   CKLaneM07.CE.Cells.C0102.cl,
   CKLaneM07.CE.Cells.C0103.cl,
   CKLaneM07.CE.Cells.C0104.cl,
   CKLaneM07.CE.Cells.C0105.cl,
   CKLaneM07.CE.Cells.C0106.cl,
   CKLaneM07.CE.Cells.C0107.cl,
   CKLaneM07.CE.Cells.C0108.cl,
   CKLaneM07.CE.Cells.C0109.cl,
   CKLaneM07.CE.Cells.C0110.cl,
   CKLaneM07.CE.Cells.C0111.cl,
   CKLaneM07.CE.Cells.C0112.cl,
   CKLaneM07.CE.Cells.C0113.cl,
   CKLaneM07.CE.Cells.C0114.cl,
   CKLaneM07.CE.Cells.C0115.cl,
   CKLaneM07.CE.Cells.C0116.cl,
   CKLaneM07.CE.Cells.C0117.cl,
   CKLaneM07.CE.Cells.C0118.cl,
   CKLaneM07.CE.Cells.C0119.cl,
   CKLaneM07.CE.Cells.C0120.cl,
   CKLaneM07.CE.Cells.C0121.cl,
   CKLaneM07.CE.Cells.C0122.cl,
   CKLaneM07.CE.Cells.C0123.cl,
   CKLaneM07.CE.Cells.C0124.cl,
   CKLaneM07.CE.Cells.C0125.cl,
   CKLaneM07.CE.Cells.C0126.cl,
   CKLaneM07.CE.Cells.C0127.cl]

end CKLaneM07.CE.Row4


