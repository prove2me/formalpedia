-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData6LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:34:17.513987+00:00
-- url     : https://prove2.me/theorems/11d9f4a8-f351-45f2-993b-eee4dee2aac8
-- title:
--   Small Pair Light Data6Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared6.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData6LeftCached.lean, lines 14-15, SHA-256 5cff0686d218e633397417308a5721ec1b9642b7d4e75e354a947ada9c33ad74. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCachedChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCachedChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCachedChunk06_Definitions

section
namespace D1Bound5.PairLightPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCached : List PairLightCachedVertex :=
  leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04 ++ leftCachedChunk05 ++ leftCachedChunk06

end D1Bound5.PairLightPrepared6
end


