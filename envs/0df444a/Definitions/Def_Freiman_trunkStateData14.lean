-- Prove2me | Definitions.Def_Freiman_trunkStateData14
-- name    : Freiman_trunkStateData14
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:21:35.444554+00:00
-- url     : https://prove2.me/theorems/85fcc162-18b8-40e5-b22c-c888499681d4
-- title:
--   trunkStateData14
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData14Part01

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData14 : TrunkState :=
  ⟨⟨([3,1],[3]),(false,false)⟩,⟨(3/4),(4/5),(1/4),(1/3)⟩,
  trunkStateData14Part01⟩
end Freiman


