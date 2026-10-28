-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData36RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:16:07.1069+00:00
-- url     : https://prove2.me/theorems/c016fd44-6aba-4fd1-b048-58ccd357dc72
-- title:
--   Small Pair Light Data36Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared36.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData36RightCached.lean, lines 11-12, SHA-256 05bb93e7c6b81c1e43a4e3ddcd2fcecdce6644f7d3ba3479bb96b1204d9665b4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCachedChunk04_Definitions

section
namespace D1Bound5.PairLightPrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCached : List PairLightCachedVertex := rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03 ++ rightCachedChunk04

end D1Bound5.PairLightPrepared36
end


