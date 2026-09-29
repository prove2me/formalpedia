-- Prove2me | Definitions.Def_Freiman_trunkStateData06
-- name    : Freiman_trunkStateData06
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:18:37.380503+00:00
-- url     : https://prove2.me/theorems/4eafd529-e76a-4cc6-ab11-229d0a5d315e
-- title:
--   trunkStateData06
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData06Part01
import Definitions.Def_Freiman_trunkStateData06Part02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData06 : TrunkState :=
  ⟨⟨([2],[3]),(false,false)⟩,⟨(1/3),(1/2),(1/4),(1/3)⟩,
  trunkStateData06Part01 ++ trunkStateData06Part02⟩
end Freiman


