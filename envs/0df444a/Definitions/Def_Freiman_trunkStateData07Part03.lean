-- Prove2me | Definitions.Def_Freiman_trunkStateData07Part03
-- name    : Freiman_trunkStateData07Part03
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:16:52.342757+00:00
-- url     : https://prove2.me/theorems/1535f9e8-6082-4569-baa5-0fc7d9febe03
-- title:
--   trunkStateData07Part03
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkModel

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData07Part03 : List TrunkGroup := [
    ⟨4,[75],40,[(0,(.pair 5432)),(1,(.pair 5433)),(2,(.pair 5432)),(3,(.pair 5434))]⟩,
    ⟨4,[75],41,[(8,(.pair 5047)),(10,(.pair 5332)),(11,(.pair 5332)),(16,(.pair 5047)),(17,(.pair 5014)),(18,(.pair 5014))]⟩,
    ⟨4,[77],0,[(-1,(.pair 5435))]⟩,
    ⟨4,[79],0,[(-1,(.pair 5436))]⟩,
    ⟨4,[93,95],0,[(-1,(.pair 5437))]⟩,
    ⟨4,[97],0,[(-1,(.pair 4964))]⟩,
    ⟨4,[99],0,[(-1,(.pair 4965))]⟩
  ]
end Freiman


