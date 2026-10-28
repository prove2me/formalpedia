-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData8Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData8Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:33:42.339434+00:00
-- url     : https://prove2.me/theorems/b169ad29-02d5-4875-94da-799683ca262a
-- title:
--   Small Pair Pure Closure Data8Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared8.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData8Destinations.lean, lines 19-20, SHA-256 3c215d36b6cbac4c4f2c380e8d443d2acbbf81806b5f68d04e4b7fa49744ce05. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk09_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk10_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk11_Definitions

section
namespace D1Bound5.PairLightClosurePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07 ++ destinationsChunk08 ++ destinationsChunk09 ++ destinationsChunk10 ++ destinationsChunk11

end D1Bound5.PairLightClosurePrepared8
end


