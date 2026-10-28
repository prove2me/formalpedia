-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData14RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:51:51.55051+00:00
-- url     : https://prove2.me/theorems/12f0c636-8376-4529-87ee-7927c25b5455
-- title:
--   Small Pair Light Data14Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared14.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData14RightCached.lean, lines 11-12, SHA-256 c38624f4278067156e4838a7bcfcd1cf70cc5912493e5234e9a8ed2061dd1652. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCached : List PairLightCachedVertex := rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03 ++ rightCachedChunk04

end D1Bound5.PairLightPrepared14
end


