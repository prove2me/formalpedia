-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData4Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData4Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:22.814206+00:00
-- url     : https://prove2.me/theorems/3f41e527-8580-4b59-aa06-ce6d3981ef48
-- title:
--   Small Pair Pure Closure Data4Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared4.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData4Vertices.lean, lines 17-18, SHA-256 d67c44ce038da75860e18e4e518c09b3ae71a0e4d8d7930c17f54efb5f9b55db. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4VerticesChunk09_Definitions

section
namespace D1Bound5.PairLightClosurePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07 ++ verticesChunk08 ++ verticesChunk09

end D1Bound5.PairLightClosurePrepared4
end


