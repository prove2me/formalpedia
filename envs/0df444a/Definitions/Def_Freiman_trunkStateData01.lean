-- Prove2me | Definitions.Def_Freiman_trunkStateData01
-- name    : Freiman_trunkStateData01
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:16:17.602075+00:00
-- url     : https://prove2.me/theorems/5d6d0827-3e26-4ebf-8418-06d28efb4650
-- title:
--   trunkStateData01
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData01Part01
import Definitions.Def_Freiman_trunkStateData01Part02
import Definitions.Def_Freiman_trunkStateData01Part03
import Definitions.Def_Freiman_trunkStateData01Part04
import Definitions.Def_Freiman_trunkStateData01Part05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData01 : TrunkState :=
  ⟨⟨([1],[2]),(false,false)⟩,⟨(1/2),(4/5),(1/3),(1/2)⟩,
  trunkStateData01Part01 ++ trunkStateData01Part02 ++ trunkStateData01Part03 ++ trunkStateData01Part04 ++ trunkStateData01Part05⟩
end Freiman


