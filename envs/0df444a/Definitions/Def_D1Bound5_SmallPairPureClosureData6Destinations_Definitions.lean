-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData6Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData6Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:29:41.35625+00:00
-- url     : https://prove2.me/theorems/ceb2a2b6-243a-4cf2-a25f-e9671b38abd7
-- title:
--   Small Pair Pure Closure Data6Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared6.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData6Destinations.lean, lines 18-19, SHA-256 dd3d676ad6a705a5357f40bf9e402356a6f25dd505c1a1934cfd141ac277fdbc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk09_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6DestinationsChunk10_Definitions

section
namespace D1Bound5.PairLightClosurePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07 ++ destinationsChunk08 ++ destinationsChunk09 ++ destinationsChunk10

end D1Bound5.PairLightClosurePrepared6
end


