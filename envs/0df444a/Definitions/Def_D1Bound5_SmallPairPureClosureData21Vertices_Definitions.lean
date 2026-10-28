-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData21Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData21Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:58.976646+00:00
-- url     : https://prove2.me/theorems/a4df585d-dda1-43c1-a402-d5dd353bff80
-- title:
--   Small Pair Pure Closure Data21Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared21.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData21Vertices.lean, lines 16-17, SHA-256 fe9815d846f53ab24f672526d5edad08dc0be2b762dcae7993f776427eaac70f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21VerticesChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21VerticesChunk08_Definitions

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07 ++ verticesChunk08

end D1Bound5.PairLightClosurePrepared21
end


