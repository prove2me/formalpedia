-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData30Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData30Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:53.215302+00:00
-- url     : https://prove2.me/theorems/cdbe5fe4-f3a0-4df6-8e22-4b55038bd643
-- title:
--   Small Pair Pure Closure Data30Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared30.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData30Vertices.lean, lines 15-16, SHA-256 6a20f837f14a5b029aaa8efb9743154f663cd1ac5d6972ef3ba532b7c7989dc3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30VerticesChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07

end D1Bound5.PairLightClosurePrepared30
end


