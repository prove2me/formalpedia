-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData30Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData30Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:09:59.70877+00:00
-- url     : https://prove2.me/theorems/68e1b5dc-68c1-453c-955a-ad5c1fe32980
-- title:
--   Small Pair Pure Closure Data30Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared30.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData30Destinations.lean, lines 15-16, SHA-256 c9c9eb3c0cf0ab5e93aca9131284c63efa57c40c1bce0288ac935085563024a1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData30DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30DestinationsChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07

end D1Bound5.PairLightClosurePrepared30
end


