-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData14_Definitions
-- name    : D1Bound5_SmallPairPureClosureData14_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:57:50.213751+00:00
-- url     : https://prove2.me/theorems/74a002c3-61fa-4b6a-9fbd-2f8a4be1cfd9
-- title:
--   Small Pair Pure Closure Data14
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared14.a`, `PairLightClosurePrepared14.b`, `PairLightClosurePrepared14.anchorRoot`, `PairLightClosurePrepared14.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData14.lean, lines 10-10, SHA-256 2757716d083b68e01ce3b904d230bd001a03a16470a800e13b4cdfa59b086a5a; D1Bound5/SmallPairPureClosureData14.lean, lines 11-11, SHA-256 2757716d083b68e01ce3b904d230bd001a03a16470a800e13b4cdfa59b086a5a; D1Bound5/SmallPairPureClosureData14.lean, lines 12-12, SHA-256 2757716d083b68e01ce3b904d230bd001a03a16470a800e13b4cdfa59b086a5a; D1Bound5/SmallPairPureClosureData14.lean, lines 14-16, SHA-256 2757716d083b68e01ce3b904d230bd001a03a16470a800e13b4cdfa59b086a5a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-2,0)
noncomputable def b : PairLightCoordinate := (1,-1)
noncomputable def anchorRoot : PairLightCoordinate := (1, 1)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared14
end


