-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData15LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:08:00.265757+00:00
-- url     : https://prove2.me/theorems/cb65a307-91a7-4f78-b13b-f456cba7afca
-- title:
--   Small Pair Light Data15Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared15.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData15LeftCached.lean, lines 11-12, SHA-256 d7596ae741c3616d9b709848a715b841712d6abd326a83aad680f3fd1cf44321. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached : List PairLightCachedVertex := leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04

end D1Bound5.PairLightPrepared15
end


