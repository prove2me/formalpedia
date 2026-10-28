-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData8RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:57:46.691444+00:00
-- url     : https://prove2.me/theorems/254594b0-c445-4ce3-aaee-fcd963492e38
-- title:
--   Small Pair Pure Closure Data8Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared8.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData8RootPairs.lean, lines 19-20, SHA-256 ddf098cbaf79a96b426b4081235b938f3e45ecabcba6daa38d66f412d1d70a52. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk09_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk10_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairsChunk11_Definitions

section
namespace D1Bound5.PairLightClosurePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07 ++ rootPairsChunk08 ++ rootPairsChunk09 ++ rootPairsChunk10 ++ rootPairsChunk11

end D1Bound5.PairLightClosurePrepared8
end


