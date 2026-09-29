-- Prove2me | Definitions.Def_Freiman_trunkStateData12
-- name    : Freiman_trunkStateData12
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:20:36.067571+00:00
-- url     : https://prove2.me/theorems/acb1ea46-71dc-425d-bc07-9b38dc9e8123
-- title:
--   trunkStateData12
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData12Part01
import Definitions.Def_Freiman_trunkStateData12Part02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData12 : TrunkState :=
  ⟨⟨([3,1],[1]),(false,false)⟩,⟨(3/4),(4/5),(1/2),(4/5)⟩,
  trunkStateData12Part01 ++ trunkStateData12Part02⟩
end Freiman


