-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData6RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:57:25.820956+00:00
-- url     : https://prove2.me/theorems/44cb76cb-6b11-4cc4-b86a-3f8c08882871
-- title:
--   Small Pair Pure Closure Data6Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared6.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData6RootPairs.lean, lines 18-19, SHA-256 0a91e27d59c616740b622ecdf3c6f703f449ee371db6b17f7e3a925f9f2202ce. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk09_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairsChunk10_Definitions

section
namespace D1Bound5.PairLightClosurePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07 ++ rootPairsChunk08 ++ rootPairsChunk09 ++ rootPairsChunk10

end D1Bound5.PairLightClosurePrepared6
end


