-- Prove2me | Definitions.Def_Freiman_trunkStateData11
-- name    : Freiman_trunkStateData11
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:21:17.67261+00:00
-- url     : https://prove2.me/theorems/b058ed76-9bec-4999-8b6e-2792a297d262
-- title:
--   trunkStateData11
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData11Part01
import Definitions.Def_Freiman_trunkStateData11Part02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData11 : TrunkState :=
  ⟨⟨([3],[3,1]),(false,false)⟩,⟨(1/4),(1/3),(3/4),(4/5)⟩,
  trunkStateData11Part01 ++ trunkStateData11Part02⟩
end Freiman


