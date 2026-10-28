-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData23Vertices_Definitions
-- name    : D1Bound5_SmallPairPureClosureData23Vertices_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:57:00.100008+00:00
-- url     : https://prove2.me/theorems/111f9ee8-e6cd-4631-ae15-edd2a9b0e51b
-- title:
--   Small Pair Pure Closure Data23Vertices
-- statement:
--   Exact vertex-coordinate lists used in the coordinate form of the small-pair mutation-closure certificates. The named objects in this bundle include `PairLightClosurePrepared23.vertices`.
-- source:
--   D1Bound5/SmallPairPureClosureData23Vertices.lean, lines 15-16, SHA-256 ced1f786fbdbadbff0ebdaddbe0ad03af82b818403a142cf37c4f1c1159d82db. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23VerticesChunk00_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23VerticesChunk01_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23VerticesChunk02_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23VerticesChunk03_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23VerticesChunk04_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23VerticesChunk05_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23VerticesChunk06_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23VerticesChunk07_Definitions

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def vertices : List PairLightCoordinate :=
  verticesChunk00 ++ verticesChunk01 ++ verticesChunk02 ++ verticesChunk03 ++ verticesChunk04 ++ verticesChunk05 ++ verticesChunk06 ++ verticesChunk07

end D1Bound5.PairLightClosurePrepared23
end


