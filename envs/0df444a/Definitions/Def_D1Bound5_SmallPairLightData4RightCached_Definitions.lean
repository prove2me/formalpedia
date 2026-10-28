-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData4RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:58.749816+00:00
-- url     : https://prove2.me/theorems/c9cf6fdf-7f25-4a25-aa1a-801302d47da5
-- title:
--   Small Pair Light Data4Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared4.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData4RightCached.lean, lines 14-15, SHA-256 72c269ef58565b98da6283137018eb9861fbf3a471c56f0c75bdb8b09bd6f7c7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCachedChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCachedChunk05_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


noncomputable def rightCached : List PairLightCachedVertex :=
  rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03 ++ rightCachedChunk04 ++ rightCachedChunk05

end D1Bound5.PairLightPrepared4
end


