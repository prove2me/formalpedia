-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData6_Definitions
-- name    : D1Bound5_SmallPairPureClosureData6_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:13.51858+00:00
-- url     : https://prove2.me/theorems/6ec09bc4-71d8-4ba2-abd7-b99e537f29d7
-- title:
--   Small Pair Pure Closure Data6
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared6.a`, `PairLightClosurePrepared6.b`, `PairLightClosurePrepared6.anchorRoot`, `PairLightClosurePrepared6.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData6.lean, lines 10-10, SHA-256 ba74385191be6fe2f88e28184217ee21c70969d0753549eec5323d53f6c383fa; D1Bound5/SmallPairPureClosureData6.lean, lines 11-11, SHA-256 ba74385191be6fe2f88e28184217ee21c70969d0753549eec5323d53f6c383fa; D1Bound5/SmallPairPureClosureData6.lean, lines 12-12, SHA-256 ba74385191be6fe2f88e28184217ee21c70969d0753549eec5323d53f6c383fa; D1Bound5/SmallPairPureClosureData6.lean, lines 14-16, SHA-256 ba74385191be6fe2f88e28184217ee21c70969d0753549eec5323d53f6c383fa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-2,-1)
noncomputable def b : PairLightCoordinate := (2,-1)
noncomputable def anchorRoot : PairLightCoordinate := (0, 2)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared6
end


