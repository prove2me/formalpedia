-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData15Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData15Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:21.482381+00:00
-- url     : https://prove2.me/theorems/404ab1ee-5ca9-43b5-ba34-e2a89ee4717e
-- title:
--   Small Pair Pure Closure Data15Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared15.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData15Vertices.lean, lines 15-16, SHA-256 dc750be74c4cea67c5c280f9082c89b194cc23e3288d9bf7a7b0bfcfe4a8afb4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15VerticesChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07

end D1Bound5.PairLightClosurePrepared15
end


