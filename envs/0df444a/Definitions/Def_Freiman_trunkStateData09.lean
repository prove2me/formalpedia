-- Prove2me | Definitions.Def_Freiman_trunkStateData09
-- name    : Freiman_trunkStateData09
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:19:02.902923+00:00
-- url     : https://prove2.me/theorems/5bd0c5dc-c7d7-427e-9fe4-c6f55f03a0f1
-- title:
--   trunkStateData09
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData09Part01
import Definitions.Def_Freiman_trunkStateData09Part02
import Definitions.Def_Freiman_trunkStateData09Part03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData09 : TrunkState :=
  ⟨⟨([3],[2]),(false,false)⟩,⟨(1/4),(1/3),(1/3),(1/2)⟩,
  trunkStateData09Part01 ++ trunkStateData09Part02 ++ trunkStateData09Part03⟩
end Freiman


