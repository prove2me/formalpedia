-- Prove2me | Definitions.Def_Freiman_trunkBoundData
-- name    : Freiman_trunkBoundData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:11:52.447306+00:00
-- url     : https://prove2.me/theorems/53204c29-dc94-4e6c-9721-f9df8e5e8331
-- title:
--   trunkBoundData
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkBoundData01
import Definitions.Def_Freiman_trunkBoundData02
import Definitions.Def_Freiman_trunkBoundData03
import Definitions.Def_Freiman_trunkBoundData04

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkDataBounds : Array CertBound := trunkBoundData01 ++ trunkBoundData02 ++ trunkBoundData03 ++ trunkBoundData04
end Freiman


