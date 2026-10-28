-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData10RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:38.737584+00:00
-- url     : https://prove2.me/theorems/7fdba929-bec9-4077-a8b3-12eb207fad10
-- title:
--   Small Pair Pure Closure Data10Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared10.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData10RootPairs.lean, lines 17-18, SHA-256 d5310fc115570c7d10fd3c96fc63e2f4399f81defcc41942ba3559eb85b9f434. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairsChunk09_Definitions

section
namespace D1Bound5.PairLightClosurePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07 ++ rootPairsChunk08 ++ rootPairsChunk09

end D1Bound5.PairLightClosurePrepared10
end


