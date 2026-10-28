-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData23LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:50:51.991552+00:00
-- url     : https://prove2.me/theorems/b8c21a84-5bf6-4819-a9e6-36c383c105af
-- title:
--   Small Pair Light Data23Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared23.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData23LeftCached.lean, lines 11-12, SHA-256 9946d25585e2fe5c8838eb27469278b2f789443eabaf37e5d88ee6d42f45b109. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached : List PairLightCachedVertex := leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04

end D1Bound5.PairLightPrepared23
end


