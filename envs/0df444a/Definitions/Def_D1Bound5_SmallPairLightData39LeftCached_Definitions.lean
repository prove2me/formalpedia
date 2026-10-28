-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
-- name    : D1Bound5_SmallPairLightData39LeftCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:15:54.876462+00:00
-- url     : https://prove2.me/theorems/73d5519c-0334-4bf3-af9a-62c1565f6c5e
-- title:
--   Small Pair Light Data39Left Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared39.leftCached`.
-- source:
--   D1Bound5/SmallPairLightData39LeftCached.lean, lines 9-11, SHA-256 0a04320ef34ac725500543de407a3c8f37f4cbf897c28d588188d01b39d49515. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCachedChunk03_Definitions

section
namespace D1Bound5.PairLightPrepared39
set_option autoImplicit false

noncomputable
def leftCached : List PairLightCachedVertex :=
  leftCachedChunk00 ++ leftCachedChunk01 ++ leftCachedChunk02 ++ leftCachedChunk03

end D1Bound5.PairLightPrepared39
end


