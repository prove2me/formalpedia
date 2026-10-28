-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData23Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData23Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:26:39.671277+00:00
-- url     : https://prove2.me/theorems/649712b1-4830-479e-be0a-dff3f6947a7d
-- title:
--   Small Pair Pure Closure Data23Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared23.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData23Destinations.lean, lines 15-16, SHA-256 42a2fd6d98d680f1e032d89d088f44fc6c5e6168123022d5316d909c5acca62c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData23DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23DestinationsChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07

end D1Bound5.PairLightClosurePrepared23
end


