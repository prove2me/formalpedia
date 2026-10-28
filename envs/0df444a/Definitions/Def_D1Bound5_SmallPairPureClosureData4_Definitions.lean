-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData4_Definitions
-- name    : D1Bound5_SmallPairPureClosureData4_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:06.332285+00:00
-- url     : https://prove2.me/theorems/da0ac9da-a0e0-4385-bd87-9082eef10ed0
-- title:
--   Small Pair Pure Closure Data4
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared4.a`, `PairLightClosurePrepared4.b`, `PairLightClosurePrepared4.anchorRoot`, `PairLightClosurePrepared4.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData4.lean, lines 10-10, SHA-256 9f6ba353b2b4504033102ea427ff30d3caac2b6309e5eb9c480b56a306a106fa; D1Bound5/SmallPairPureClosureData4.lean, lines 11-11, SHA-256 9f6ba353b2b4504033102ea427ff30d3caac2b6309e5eb9c480b56a306a106fa; D1Bound5/SmallPairPureClosureData4.lean, lines 12-12, SHA-256 9f6ba353b2b4504033102ea427ff30d3caac2b6309e5eb9c480b56a306a106fa; D1Bound5/SmallPairPureClosureData4.lean, lines 14-16, SHA-256 9f6ba353b2b4504033102ea427ff30d3caac2b6309e5eb9c480b56a306a106fa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-2,-1)
noncomputable def b : PairLightCoordinate := (0,-1)
noncomputable def anchorRoot : PairLightCoordinate := (1, 1)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared4
end


