-- Prove2me | Definitions.Def_Freiman_trunkStateData07
-- name    : Freiman_trunkStateData07
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:18:28.993809+00:00
-- url     : https://prove2.me/theorems/46908882-f822-4299-8482-96a763677fbb
-- title:
--   trunkStateData07
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData07Part01
import Definitions.Def_Freiman_trunkStateData07Part02
import Definitions.Def_Freiman_trunkStateData07Part03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData07 : TrunkState :=
  ⟨⟨([2],[3,1]),(false,false)⟩,⟨(1/3),(1/2),(3/4),(4/5)⟩,
  trunkStateData07Part01 ++ trunkStateData07Part02 ++ trunkStateData07Part03⟩
end Freiman


