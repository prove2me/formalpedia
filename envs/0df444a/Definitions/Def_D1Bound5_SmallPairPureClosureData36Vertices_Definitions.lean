-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData36Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData36Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:23.576237+00:00
-- url     : https://prove2.me/theorems/f7ce4605-63c9-4c45-ae8d-c5c64303fe6d
-- title:
--   Small Pair Pure Closure Data36Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared36.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData36Vertices.lean, lines 16-17, SHA-256 9607c3351ac9e0b633dbde5ebf1904915d348060cc157bcff26b8cff37cd2a38. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36VerticesChunk07_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36VerticesChunk08_Definitions

section
namespace D1Bound5.PairLightClosurePrepared36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07 ++ verticesChunk08

end D1Bound5.PairLightClosurePrepared36
end


