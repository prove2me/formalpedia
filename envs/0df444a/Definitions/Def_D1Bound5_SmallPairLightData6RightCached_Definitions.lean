-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData6RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:30:06.727415+00:00
-- url     : https://prove2.me/theorems/46ae8f21-ac93-41e5-b1c7-e44a3167d0a3
-- title:
--   Small Pair Light Data6Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared6.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData6RightCached.lean, lines 14-15, SHA-256 ffe7e171bba5ee38438a42bec38e89e45ffd868bd53a1e7a939e9ba7b2258ca6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCachedChunk06_Definitions

section
namespace D1Bound5.PairLightPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCached : List PairLightCachedVertex :=
  rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03 ++ rightCachedChunk04 ++ rightCachedChunk05 ++ rightCachedChunk06

end D1Bound5.PairLightPrepared6
end


