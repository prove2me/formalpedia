-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData30RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:11:52.050508+00:00
-- url     : https://prove2.me/theorems/a280f641-0125-41d0-a871-24281026846c
-- title:
--   Small Pair Light Data30Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared30.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData30RightCached.lean, lines 10-11, SHA-256 f25c445ae430ab77285dbc851f9b681c6427fa11c3dad77bb5f68e6ff8ac0fa6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCachedChunk03_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCached : List PairLightCachedVertex := rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03

end D1Bound5.PairLightPrepared30
end


