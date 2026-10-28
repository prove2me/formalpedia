-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData36RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:26.994893+00:00
-- url     : https://prove2.me/theorems/b0469e53-f4ea-46c4-88c2-aac7c4f6f1c9
-- title:
--   Small Pair Pure Closure Data36Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared36.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData36RootPairs.lean, lines 16-17, SHA-256 2c59b0d872aa12041cfe424e3dadefb8b09c8d5c8841bcf0b2a9ccbeeb91a73f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairsChunk08_Definitions

section
namespace D1Bound5.PairLightClosurePrepared36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07 ++ rootPairsChunk08

end D1Bound5.PairLightClosurePrepared36
end


