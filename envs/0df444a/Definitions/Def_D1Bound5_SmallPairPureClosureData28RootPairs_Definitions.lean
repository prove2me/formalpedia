-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairs_Definitions
-- name    : D1Bound5_SmallPairPureClosureData28RootPairs_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:57:08.964203+00:00
-- url     : https://prove2.me/theorems/1d176881-f655-4803-9d98-6f10ad9dbe88
-- title:
--   Small Pair Pure Closure Data28Root Pairs
-- statement:
--   Exact root-pair lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared28.rootPairs`.
-- source:
--   D1Bound5/SmallPairPureClosureData28RootPairs.lean, lines 16-17, SHA-256 5b8044ac2275ca7206079415b6ab79d925403bc44889bbdd152919c34b389352. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairsChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairsChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairsChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairsChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairsChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairsChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairsChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairsChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairsChunk08_Definitions

section
namespace D1Bound5.PairLightClosurePrepared28
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rootPairs : List (PairLightCoordinate × PairLightCoordinate) :=
  rootPairsChunk00 ++ rootPairsChunk01 ++ rootPairsChunk02 ++ rootPairsChunk03 ++ rootPairsChunk04 ++ rootPairsChunk05 ++ rootPairsChunk06 ++ rootPairsChunk07 ++ rootPairsChunk08

end D1Bound5.PairLightClosurePrepared28
end


