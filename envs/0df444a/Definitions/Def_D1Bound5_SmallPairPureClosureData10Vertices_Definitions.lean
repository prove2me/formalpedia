-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData10Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData10Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:10.791757+00:00
-- url     : https://prove2.me/theorems/9a6f1bc9-7021-47c4-8c15-7aeb66da790a
-- title:
--   Small Pair Pure Closure Data10Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared10.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData10Vertices.lean, lines 17-18, SHA-256 6f518fd1fe04d1d175fafa0feab7d3168ea24475f188335e0889d32e03485b29. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10VerticesChunk09_Definitions

section
namespace D1Bound5.PairLightClosurePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07 ++ verticesChunk08 ++ verticesChunk09

end D1Bound5.PairLightClosurePrepared10
end


