-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData28RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:05:36.791155+00:00
-- url     : https://prove2.me/theorems/ca5cc488-a307-4307-bb57-f8fb7a78d044
-- title:
--   Small Pair Light Data28Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared28.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData28RightCached.lean, lines 11-12, SHA-256 6315375cb1951787591dc04e10de64c74c5ca80d5dffb603d96ea4147bfa09f8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCached : List PairLightCachedVertex := rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03 ++ rightCachedChunk04

end D1Bound5.PairLightPrepared28
end


