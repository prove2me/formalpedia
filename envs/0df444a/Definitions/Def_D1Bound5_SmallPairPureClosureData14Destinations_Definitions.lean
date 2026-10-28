-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData14Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData14Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:32:40.899378+00:00
-- url     : https://prove2.me/theorems/1c076de3-12c0-4969-8e28-53262837d43e
-- title:
--   Small Pair Pure Closure Data14Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared14.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData14Destinations.lean, lines 15-16, SHA-256 9ef7803fd568137682399387e4d4380eb69e8659bbf2a801b75b6ce03d6ca1e7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData14DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14DestinationsChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07

end D1Bound5.PairLightClosurePrepared14
end


