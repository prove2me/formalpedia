-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData15Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData15Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:19:36.744665+00:00
-- url     : https://prove2.me/theorems/c2ffd544-0073-4211-8151-538719b706ed
-- title:
--   Small Pair Pure Closure Data15Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared15.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData15Destinations.lean, lines 15-16, SHA-256 1c03493937c5e58ac304a8d86ba5a3083b461b2df71c7aa4e0520bee71a00fbd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData15DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15DestinationsChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07

end D1Bound5.PairLightClosurePrepared15
end


