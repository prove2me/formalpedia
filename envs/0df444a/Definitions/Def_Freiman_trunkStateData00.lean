-- Prove2me | Definitions.Def_Freiman_trunkStateData00
-- name    : Freiman_trunkStateData00
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:16:14.801494+00:00
-- url     : https://prove2.me/theorems/231ffa26-021a-4f62-85a6-f3b8264f55af
-- title:
--   trunkStateData00
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData00Part01
import Definitions.Def_Freiman_trunkStateData00Part02
import Definitions.Def_Freiman_trunkStateData00Part03
import Definitions.Def_Freiman_trunkStateData00Part04
import Definitions.Def_Freiman_trunkStateData00Part05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData00 : TrunkState :=
  ⟨⟨([1],[1]),(false,false)⟩,⟨(1/2),(4/5),(1/2),(4/5)⟩,
  trunkStateData00Part01 ++ trunkStateData00Part02 ++ trunkStateData00Part03 ++ trunkStateData00Part04 ++ trunkStateData00Part05⟩
end Freiman


