-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData21Destinations_Definitions
-- name    : D1Bound5_SmallPairPureClosureData21Destinations_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:26:46.439265+00:00
-- url     : https://prove2.me/theorems/257c1e7b-e6de-4bd9-afd5-784141662481
-- title:
--   Small Pair Pure Closure Data21Destinations
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared21.destinations`.
-- source:
--   D1Bound5/SmallPairPureClosureData21Destinations.lean, lines 16-17, SHA-256 93f0e87b8b69298ea4f84d029bbbb33f59fe74776e02d2acf2a15174df6bdc93. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_SmallPairPureClosureData21DestinationsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21DestinationsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21DestinationsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21DestinationsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21DestinationsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21DestinationsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21DestinationsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21DestinationsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21DestinationsChunk08_Definitions

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinations : List (Option Nat × Option Nat) :=
  destinationsChunk00 ++ destinationsChunk01 ++ destinationsChunk02 ++ destinationsChunk03 ++ destinationsChunk04 ++ destinationsChunk05 ++ destinationsChunk06 ++ destinationsChunk07 ++ destinationsChunk08

end D1Bound5.PairLightClosurePrepared21
end


