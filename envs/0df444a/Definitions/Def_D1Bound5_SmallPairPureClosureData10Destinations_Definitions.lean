-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData10Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData10Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:24:47.342003+00:00
-- url     : https://prove2.me/theorems/6767ccb4-c98e-47c0-a824-f3c1d2d623da
-- title:
--   Small Pair Pure Closure Data10Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared10.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData10Destinations.lean, lines 17-18, SHA-256 a41025578100c6fe844a6c83db29b54d9bc40a206f11ddf9cc6b80838f0ce3e5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10DestinationsChunk09_Definitions

section
namespace D1Bound5.PairLightClosurePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07 ++ destinationsChunk08 ++ destinationsChunk09

end D1Bound5.PairLightClosurePrepared10
end


