-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData28LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:34:23.321717+00:00
-- url     : https://prove2.me/theorems/62b9e38b-b0a2-4bb7-9a09-780a1348be7b
-- title:
--   Small Pair Light Data28Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared28.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData28LeftCached.lean, lines 11-12, SHA-256 9e02f403fe418ecaebed7c3c304960ac09d16aafe9c6a5ead0a0b2d859367462. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached : List PairLightCachedVertex := leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04

end D1Bound5.PairLightPrepared28
end


