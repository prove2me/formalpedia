-- Prove2me | Definitions.Def_Freiman_trunkStateData03
-- name    : Freiman_trunkStateData03
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:15:47.167105+00:00
-- url     : https://prove2.me/theorems/17a81bb2-1fde-4c5e-86eb-e366952064ee
-- title:
--   trunkStateData03
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData03Part01
import Definitions.Def_Freiman_trunkStateData03Part02
import Definitions.Def_Freiman_trunkStateData03Part03

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData03 : TrunkState :=
  ⟨⟨([1],[3,1]),(false,false)⟩,⟨(1/2),(4/5),(3/4),(4/5)⟩,
  trunkStateData03Part01 ++ trunkStateData03Part02 ++ trunkStateData03Part03⟩
end Freiman


