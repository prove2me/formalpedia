-- Prove2me | Definitions.Def_Freiman_trunkStateData15
-- name    : Freiman_trunkStateData15
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:21:35.831105+00:00
-- url     : https://prove2.me/theorems/6323f6e1-a1e1-4eaf-a812-7b7ddc43a37d
-- title:
--   trunkStateData15
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData15Part01
import Definitions.Def_Freiman_trunkStateData15Part02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData15 : TrunkState :=
  ⟨⟨([3,1],[3,1]),(false,false)⟩,⟨(3/4),(4/5),(3/4),(4/5)⟩,
  trunkStateData15Part01 ++ trunkStateData15Part02⟩
end Freiman


