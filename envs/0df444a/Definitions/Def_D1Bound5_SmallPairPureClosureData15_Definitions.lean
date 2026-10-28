-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData15_Definitions
-- name    : D1Bound5_SmallPairPureClosureData15_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:17.260075+00:00
-- url     : https://prove2.me/theorems/8f186a75-e008-453a-a9d1-a6e41ba17906
-- title:
--   Small Pair Pure Closure Data15
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared15.a`, `PairLightClosurePrepared15.b`, `PairLightClosurePrepared15.anchorRoot`, `PairLightClosurePrepared15.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData15.lean, lines 10-10, SHA-256 cdb63684ff53832fafcda3da888d3c45ba2bbf33924a87fda77d6e6b8af0b902; D1Bound5/SmallPairPureClosureData15.lean, lines 11-11, SHA-256 cdb63684ff53832fafcda3da888d3c45ba2bbf33924a87fda77d6e6b8af0b902; D1Bound5/SmallPairPureClosureData15.lean, lines 12-12, SHA-256 cdb63684ff53832fafcda3da888d3c45ba2bbf33924a87fda77d6e6b8af0b902; D1Bound5/SmallPairPureClosureData15.lean, lines 14-16, SHA-256 cdb63684ff53832fafcda3da888d3c45ba2bbf33924a87fda77d6e6b8af0b902. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-1,-1)
noncomputable def b : PairLightCoordinate := (-1,1)
noncomputable def anchorRoot : PairLightCoordinate := (2, 0)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared15
end


