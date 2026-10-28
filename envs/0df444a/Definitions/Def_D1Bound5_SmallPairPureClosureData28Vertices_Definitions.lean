-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData28Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData28Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:57:22.668989+00:00
-- url     : https://prove2.me/theorems/b212c392-a2d6-4f3b-98eb-9e98bcab146f
-- title:
--   Small Pair Pure Closure Data28Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared28.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData28Vertices.lean, lines 16-17, SHA-256 929a755ebb1364f8108460bfd26e6c34e88cf457d02012e966e23bc7b94f20a6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28VerticesChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28VerticesChunk08_Definitions

section
namespace D1Bound5.PairLightClosurePrepared28
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07 ++ verticesChunk08

end D1Bound5.PairLightClosurePrepared28
end


