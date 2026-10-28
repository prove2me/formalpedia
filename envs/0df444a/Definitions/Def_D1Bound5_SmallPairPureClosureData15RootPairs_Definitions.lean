-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData15RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:57:21.823606+00:00
-- url     : https://prove2.me/theorems/630c383a-bede-4128-9136-3495df55aa14
-- title:
--   Small Pair Pure Closure Data15Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared15.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData15RootPairs.lean, lines 15-16, SHA-256 cce6d13ffe02edd142de545fa4c4084ceff42ad9c758ae673ed85bbaf4ae8176. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairsChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07

end D1Bound5.PairLightClosurePrepared15
end


