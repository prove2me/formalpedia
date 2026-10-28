-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData4Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData4Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:26:44.513114+00:00
-- url     : https://prove2.me/theorems/5656533d-72ce-4dec-b75b-2284be0e4e6e
-- title:
--   Small Pair Pure Closure Data4Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared4.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData4Destinations.lean, lines 17-18, SHA-256 0a21eca8476eff40112db39d292f8f0856df4dddc6393cd57b0a09152d5e276d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4DestinationsChunk09_Definitions

section
namespace D1Bound5.PairLightClosurePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07 ++ destinationsChunk08 ++ destinationsChunk09

end D1Bound5.PairLightClosurePrepared4
end


