-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData8RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:11:39.437361+00:00
-- url     : https://prove2.me/theorems/0d69f0a0-109e-418c-9966-d657eb037fcb
-- title:
--   Small Pair Light Data8Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared8.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData8RightCached.lean, lines 15-16, SHA-256 c02d2456ff81c571fca14d53c66874b3b37b2236be16282da2465ba55c8541e3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCachedChunk07_Definitions

section
namespace D1Bound5.PairLightPrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCached : List PairLightCachedVertex :=
  rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03 ++ rightCachedChunk04 ++ rightCachedChunk05 ++ rightCachedChunk06 ++ rightCachedChunk07

end D1Bound5.PairLightPrepared8
end


