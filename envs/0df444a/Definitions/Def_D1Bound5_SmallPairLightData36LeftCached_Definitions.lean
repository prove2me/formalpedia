-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData36LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:21:35.692655+00:00
-- url     : https://prove2.me/theorems/7b612be9-bfe6-4fba-b314-1612f5864dc8
-- title:
--   Small Pair Light Data36Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared36.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData36LeftCached.lean, lines 11-12, SHA-256 ece64f42ca555894b56b049bfe9cf49b11a66d7642e94f52719d1ab20a61bd8c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached : List PairLightCachedVertex := leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04

end D1Bound5.PairLightPrepared36
end


