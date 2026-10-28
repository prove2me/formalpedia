-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData4LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:05:14.157568+00:00
-- url     : https://prove2.me/theorems/cfd833b6-b17a-40d9-beed-e922ec27ccc0
-- title:
--   Small Pair Light Data4Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared4.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData4LeftCached.lean, lines 14-15, SHA-256 ede8eeaf132ac401b0f4098c11409e76fc8f3343bd7345b16108ecb99dad0cb9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCachedChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCachedChunk05_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


noncomputable def leftCached : List PairLightCachedVertex :=
  leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04 ++ leftCachedChunk05

end D1Bound5.PairLightPrepared4
end


