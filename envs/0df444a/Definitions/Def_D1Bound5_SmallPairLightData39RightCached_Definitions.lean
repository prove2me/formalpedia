-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
-- name    : D1Bound5_SmallPairLightData39RightCached_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:16.838927+00:00
-- url     : https://prove2.me/theorems/0cc3c744-d5b7-4134-9809-e2acc865eca2
-- title:
--   Small Pair Light Data39Right Cached
-- statement:
--   Cached exact coordinate data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared39.rightCached`.
-- source:
--   D1Bound5/SmallPairLightData39RightCached.lean, lines 9-11, SHA-256 bff5b45a75f64de69204c7fe31ed5a891531637506aa556fb54eb564496abc14. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCachedChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCachedChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCachedChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCachedChunk03_Definitions

section
namespace D1Bound5.PairLightPrepared39
set_option autoImplicit false

noncomputable
def rightCached : List PairLightCachedVertex :=
  rightCachedChunk00 ++ rightCachedChunk01 ++ rightCachedChunk02 ++ rightCachedChunk03

end D1Bound5.PairLightPrepared39
end


