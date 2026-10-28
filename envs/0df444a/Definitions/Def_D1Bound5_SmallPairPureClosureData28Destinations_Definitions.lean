-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData28Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData28Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:24:51.339917+00:00
-- url     : https://prove2.me/theorems/1f19f701-5ecc-4530-b677-aa9cf54a33e2
-- title:
--   Small Pair Pure Closure Data28Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared28.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData28Destinations.lean, lines 16-17, SHA-256 daa944838390810f794c55a111c115f790b50fa477a72fa6cd6a9ef1120c2c53. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData28DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28DestinationsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28DestinationsChunk08_Definitions

section
namespace D1Bound5.PairLightClosurePrepared28
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07 ++ destinationsChunk08

end D1Bound5.PairLightClosurePrepared28
end


