-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData15RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:16:54.480871+00:00
-- url     : https://prove2.me/theorems/ffbe1a34-4cf5-4c74-bc57-1dec7c91996b
-- title:
--   Small Pair Light Data15Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared15.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData15RightCached.lean, lines 10-11, SHA-256 beb7eafa7177fa5d9627c72cb271aca1bc5126e770129c83a514273d0175cb98. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCachedChunk03_Definitions

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCached : List PairLightCachedVertex := rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03

end D1Bound5.PairLightPrepared15
end


