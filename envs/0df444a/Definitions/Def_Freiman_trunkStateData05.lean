-- Prove2me | Definitions.Def_Freiman_trunkStateData05
-- name    : Freiman_trunkStateData05
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:21:26.786793+00:00
-- url     : https://prove2.me/theorems/711e1385-213e-4cb3-b163-4643717fe2dc
-- title:
--   trunkStateData05
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData05Part01
import Definitions.Def_Freiman_trunkStateData05Part02
import Definitions.Def_Freiman_trunkStateData05Part03
import Definitions.Def_Freiman_trunkStateData05Part04
import Definitions.Def_Freiman_trunkStateData05Part05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData05 : TrunkState :=
  ⟨⟨([2],[2]),(false,false)⟩,⟨(1/3),(1/2),(1/3),(1/2)⟩,
  trunkStateData05Part01 ++ trunkStateData05Part02 ++ trunkStateData05Part03 ++ trunkStateData05Part04 ++ trunkStateData05Part05⟩
end Freiman


