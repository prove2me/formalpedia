-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData4RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:19.582654+00:00
-- url     : https://prove2.me/theorems/b13ed524-869a-41d4-adc8-bb9239a8f736
-- title:
--   Small Pair Pure Closure Data4Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared4.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData4RootPairs.lean, lines 17-18, SHA-256 12b40c64a968b9c50c8d91413621918a3d552fc8abe80d96a393b98d9b041ddf. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairsChunk09_Definitions

section
namespace D1Bound5.PairLightClosurePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07 ++ rootPairsChunk08 ++ rootPairsChunk09

end D1Bound5.PairLightClosurePrepared4
end


