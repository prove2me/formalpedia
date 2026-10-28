-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData14Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData14Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:57:02.487215+00:00
-- url     : https://prove2.me/theorems/d23424d9-d3f7-471f-8223-42860c0bc7fd
-- title:
--   Small Pair Pure Closure Data14Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared14.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData14Vertices.lean, lines 15-16, SHA-256 1cb15aa6daa61607718d6d37da59a8229c62aab6920284e57b03ccc3844a2ef4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14VerticesChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07

end D1Bound5.PairLightClosurePrepared14
end


