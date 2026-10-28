-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData10RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:35:21.148458+00:00
-- url     : https://prove2.me/theorems/8adb3768-6cb2-4fd6-b771-d83c5987cb1e
-- title:
--   Small Pair Light Data10Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared10.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData10RightCached.lean, lines 13-14, SHA-256 e9adb6cbf415451a86b5dd3f97bc84ba85ca3a9eb3b688eb6851757f0094fed7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCachedChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCachedChunk05_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightCached : List PairLightCachedVertex :=
  rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03 ++ rightCachedChunk04 ++ rightCachedChunk05

end D1Bound5.PairLightPrepared10
end


