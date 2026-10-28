-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData8Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData8Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:23.301167+00:00
-- url     : https://prove2.me/theorems/9f19ae91-1d9d-4491-83d6-935e6624e74a
-- title:
--   Small Pair Pure Closure Data8Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared8.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData8Vertices.lean, lines 19-20, SHA-256 7abea8df408adcbd21d96c92beef13929f5dc7d16db8c1861256502451b64988. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk08_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk09_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk10_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8VerticesChunk11_Definitions

section
namespace D1Bound5.PairLightClosurePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07 ++ verticesChunk08 ++ verticesChunk09 ++ verticesChunk10 ++ verticesChunk11

end D1Bound5.PairLightClosurePrepared8
end


