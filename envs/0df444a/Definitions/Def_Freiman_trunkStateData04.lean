-- Prove2me | Definitions.Def_Freiman_trunkStateData04
-- name    : Freiman_trunkStateData04
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:18:32.220777+00:00
-- url     : https://prove2.me/theorems/67a36f4f-7aeb-4a89-8056-f818a1410ea0
-- title:
--   trunkStateData04
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData04Part01
import Definitions.Def_Freiman_trunkStateData04Part02
import Definitions.Def_Freiman_trunkStateData04Part03
import Definitions.Def_Freiman_trunkStateData04Part04
import Definitions.Def_Freiman_trunkStateData04Part05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData04 : TrunkState :=
  ⟨⟨([2],[1]),(false,false)⟩,⟨(1/3),(1/2),(1/2),(4/5)⟩,
  trunkStateData04Part01 ++ trunkStateData04Part02 ++ trunkStateData04Part03 ++ trunkStateData04Part04 ++ trunkStateData04Part05⟩
end Freiman


