-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData21LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:53:41.030265+00:00
-- url     : https://prove2.me/theorems/0f83627b-51d1-4f14-b125-ce157486c06a
-- title:
--   Small Pair Light Data21Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared21.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData21LeftCached.lean, lines 11-12, SHA-256 0750ab980f579a91da8b8e35f1d4a6d33cf377130dc776ca12d212afd09e7e51. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def leftCached : List PairLightCachedVertex := leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04

end D1Bound5.PairLightPrepared21
end


