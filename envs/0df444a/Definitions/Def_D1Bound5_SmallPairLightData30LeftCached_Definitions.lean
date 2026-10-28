-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData30LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:33:53.25683+00:00
-- url     : https://prove2.me/theorems/d12f0d4f-d967-4651-9685-9eeacf8f440e
-- title:
--   Small Pair Light Data30Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared30.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData30LeftCached.lean, lines 11-12, SHA-256 6f8083ceb1f45e1256d3bd4db62625db67a7dfded5279a5f0ad51179b76fb6e0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached : List PairLightCachedVertex := leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04

end D1Bound5.PairLightPrepared30
end


