-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData14LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:32:59.7027+00:00
-- url     : https://prove2.me/theorems/01f02356-2ec2-4ef7-900a-ea066722a339
-- title:
--   Small Pair Light Data14Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared14.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData14LeftCached.lean, lines 11-12, SHA-256 4e37eb38c673225a5dd5e28808b7b69a233b4215ee92669212bb8b1c68f9f614. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached : List PairLightCachedVertex := leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04

end D1Bound5.PairLightPrepared14
end


