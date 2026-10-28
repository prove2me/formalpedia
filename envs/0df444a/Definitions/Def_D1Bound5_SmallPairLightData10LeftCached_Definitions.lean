-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData10LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:27:13.188688+00:00
-- url     : https://prove2.me/theorems/a52b824c-31c3-4fb9-b476-c4fdb91cc2ab
-- title:
--   Small Pair Light Data10Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared10.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData10LeftCached.lean, lines 13-14, SHA-256 28f53d152c584c75e737911811f662f226a1889d6f8266f59eb93ed9ad883a63. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCachedChunk05_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCached : List PairLightCachedVertex :=
  leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04 ++ leftCachedChunk05

end D1Bound5.PairLightPrepared10
end


