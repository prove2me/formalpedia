-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData8LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:31:58.80681+00:00
-- url     : https://prove2.me/theorems/48762fd4-b36b-4037-ace5-6a320c06b291
-- title:
--   Small Pair Light Data8Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared8.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData8LeftCached.lean, lines 15-16, SHA-256 053b31ea6897c92b11af4cec6f6a4060c46df9038304566a019fb65e5c29b319. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCachedChunk07_Definitions

section
namespace D1Bound5.PairLightPrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftCached : List PairLightCachedVertex :=
  leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03 ++ leftCachedChunk04 ++ leftCachedChunk05 ++ leftCachedChunk06 ++ leftCachedChunk07

end D1Bound5.PairLightPrepared8
end


