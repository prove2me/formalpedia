-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData30RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:55:11.016442+00:00
-- url     : https://prove2.me/theorems/3e8a0b31-fb54-4c02-913e-80ab39c5987f
-- title:
--   Small Pair Pure Closure Data30Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared30.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData30RootPairs.lean, lines 15-16, SHA-256 8319a04f102744b4405540a460f2fb20ff94d924b27f69ed93b21ae6625d9fd5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairsChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07

end D1Bound5.PairLightClosurePrepared30
end


