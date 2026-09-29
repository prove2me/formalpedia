-- Prove2me | Definitions.Def_Freiman_trunkStateData08
-- name    : Freiman_trunkStateData08
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:18:19.508617+00:00
-- url     : https://prove2.me/theorems/18eafb5f-61a9-4e3f-b249-2dc045472a4e
-- title:
--   trunkStateData08
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData08Part01
import Definitions.Def_Freiman_trunkStateData08Part02
import Definitions.Def_Freiman_trunkStateData08Part03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData08 : TrunkState :=
  ⟨⟨([3],[1]),(false,false)⟩,⟨(1/4),(1/3),(1/2),(4/5)⟩,
  trunkStateData08Part01 ++ trunkStateData08Part02 ++ trunkStateData08Part03⟩
end Freiman


