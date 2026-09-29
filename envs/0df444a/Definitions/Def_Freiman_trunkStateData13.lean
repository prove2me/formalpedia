-- Prove2me | Definitions.Def_Freiman_trunkStateData13
-- name    : Freiman_trunkStateData13
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:20:50.671292+00:00
-- url     : https://prove2.me/theorems/327af382-0823-42e2-a524-b00e98edf1ac
-- title:
--   trunkStateData13
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData13Part01
import Definitions.Def_Freiman_trunkStateData13Part02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData13 : TrunkState :=
  ⟨⟨([3,1],[2]),(false,false)⟩,⟨(3/4),(4/5),(1/3),(1/2)⟩,
  trunkStateData13Part01 ++ trunkStateData13Part02⟩
end Freiman


