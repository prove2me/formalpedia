-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData36Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData36Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:24:48.917104+00:00
-- url     : https://prove2.me/theorems/1832317f-86b9-4dad-a001-c1985177f229
-- title:
--   Small Pair Pure Closure Data36Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared36.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData36Destinations.lean, lines 16-17, SHA-256 733b3c3923ce56d221f91e6727fe0dc55705a4271ab9f1a6ef878049ca25281d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData36DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36DestinationsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36DestinationsChunk08_Definitions

section
namespace D1Bound5.PairLightClosurePrepared36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07 ++ destinationsChunk08

end D1Bound5.PairLightClosurePrepared36
end


