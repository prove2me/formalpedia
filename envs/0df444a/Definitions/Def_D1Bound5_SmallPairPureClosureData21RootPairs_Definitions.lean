-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData21RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:56:34.363576+00:00
-- url     : https://prove2.me/theorems/65e58e38-41bd-4327-b8cb-5a7ef9d0c6b7
-- title:
--   Small Pair Pure Closure Data21Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared21.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData21RootPairs.lean, lines 16-17, SHA-256 8702f28edb8eab59e71227e283348e89d231e3164f0037e46047782036d27a91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairsChunk08_Definitions

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07 ++ rootPairsChunk08

end D1Bound5.PairLightClosurePrepared21
end


