-- Prove2me | Definitions.Def_Freiman_trunkStateData02
-- name    : Freiman_trunkStateData02
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:16:05.996788+00:00
-- url     : https://prove2.me/theorems/ed4b1586-1658-4733-893e-dc6e8c1e36a2
-- title:
--   trunkStateData02
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkStateData02Part01
import Definitions.Def_Freiman_trunkStateData02Part02

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData02 : TrunkState :=
  ⟨⟨([1],[3]),(false,false)⟩,⟨(1/2),(4/5),(1/4),(1/3)⟩,
  trunkStateData02Part01 ++ trunkStateData02Part02⟩
end Freiman


