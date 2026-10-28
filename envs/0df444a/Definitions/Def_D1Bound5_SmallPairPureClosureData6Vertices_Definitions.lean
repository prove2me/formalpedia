-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData6Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData6Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:57:09.017346+00:00
-- url     : https://prove2.me/theorems/c669243e-399d-4df2-bf4b-715450131580
-- title:
--   Small Pair Pure Closure Data6Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared6.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData6Vertices.lean, lines 18-19, SHA-256 f7f8e0b1a65d1bf37fb1ed36d929fdacc793c8cc2851961771201374efcf17ae. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk09_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6VerticesChunk10_Definitions

section
namespace D1Bound5.PairLightClosurePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07 ++ verticesChunk08 ++ verticesChunk09 ++ verticesChunk10

end D1Bound5.PairLightClosurePrepared6
end


