-- Prove2me | Definitions.Def_Freiman_trunkStateData10
-- name    : Freiman_trunkStateData10
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:20:42.882705+00:00
-- url     : https://prove2.me/theorems/ec5f5a31-daf0-415c-aeb0-46c3f24dac50
-- title:
--   trunkStateData10
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData10Part01
import Definitions.Def_Freiman_trunkStateData10Part02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData10 : TrunkState :=
  ⟨⟨([3],[3]),(false,false)⟩,⟨(1/4),(1/3),(1/4),(1/3)⟩,
  trunkStateData10Part01 ++ trunkStateData10Part02⟩
end Freiman


