-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Table_q00
-- name    : CK_CKLaneC_SAxis_Data_Table_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:36:37.849678+00:00
-- url     : https://prove2.me/theorems/83de1550-a86d-4c03-8042-9c970270a193
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Table (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Table (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Table (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Table (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Table (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab00
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab01
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab02
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab03
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab04
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab05
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab06
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab07
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab08
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab09
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab10
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab11
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab12
import Definitions.Def_CK_CKLaneC_SAxis_Data_Tab13



set_option autoImplicit false

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain

namespace CKLaneC.SAxis.Data

/-- The checked slope table of the sAxis certificate. -/
def T : List (List Piece) := [tab00, tab01, tab02, tab03, tab04, tab05, tab06, tab07, tab08, tab09, tab10, tab11, tab12, tab13]

end CKLaneC.SAxis.Data


