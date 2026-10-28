-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData23RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:33:24.94473+00:00
-- url     : https://prove2.me/theorems/25b157c0-f13b-4650-96dc-ee6809759a56
-- title:
--   Small Pair Light Data23Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared23.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData23RightCached.lean, lines 10-11, SHA-256 0ec621bb37bfd732115e43b7528ad7c9aea48a9012e86ac4107243c0b54c859f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCachedChunk03_Definitions

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable
def rightCached : List PairLightCachedVertex := rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03

end D1Bound5.PairLightPrepared23
end


