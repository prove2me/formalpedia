-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData21RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:19:20.238925+00:00
-- url     : https://prove2.me/theorems/3dc3e406-ce8c-402e-86bd-78ae1a62c303
-- title:
--   Small Pair Light Data21Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared21.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData21RightCached.lean, lines 11-12, SHA-256 f2630dd69cd88149714612156eb788f6a0a93601d162bf271bd354a5ca8d3a24. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCached : List PairLightCachedVertex := rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03 ++ rightCachedChunk04

end D1Bound5.PairLightPrepared21
end


