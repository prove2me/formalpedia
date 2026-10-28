-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData14RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:52:58.864331+00:00
-- url     : https://prove2.me/theorems/0fb1b37f-18bd-434e-9e31-c647dafa3685
-- title:
--   Small Pair Pure Closure Data14Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared14.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData14RootPairs.lean, lines 15-16, SHA-256 200ff622bcd8dc40ee951f9ab5c802f7014df7bea9678a6cc35dd08cbf7f9f4d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairsChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07

end D1Bound5.PairLightClosurePrepared14
end


