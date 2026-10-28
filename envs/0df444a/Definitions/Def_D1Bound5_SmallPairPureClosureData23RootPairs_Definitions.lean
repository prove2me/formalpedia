-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData23RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:24.58649+00:00
-- url     : https://prove2.me/theorems/ac2de82b-e427-4403-9022-6dfd126f37c3
-- title:
--   Small Pair Pure Closure Data23Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared23.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData23RootPairs.lean, lines 15-16, SHA-256 de953e4ad96f1e9830624bbaf02266dc222a5973f1a2e44048b56db309d331c9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairsChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07

end D1Bound5.PairLightClosurePrepared23
end


