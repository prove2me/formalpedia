-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData23_Definitions
-- name    : D1Bound5_SmallPairPureClosureData23_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:06.992949+00:00
-- url     : https://prove2.me/theorems/20085eef-f194-4386-934f-a0e58d32d4ac
-- title:
--   Small Pair Pure Closure Data23
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared23.a`, `PairLightClosurePrepared23.b`, `PairLightClosurePrepared23.anchorRoot`, `PairLightClosurePrepared23.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData23.lean, lines 10-10, SHA-256 d1850cc259f044990e773071529f613dfc132b8c44b75dd2917a393d612329c4; D1Bound5/SmallPairPureClosureData23.lean, lines 11-11, SHA-256 d1850cc259f044990e773071529f613dfc132b8c44b75dd2917a393d612329c4; D1Bound5/SmallPairPureClosureData23.lean, lines 12-12, SHA-256 d1850cc259f044990e773071529f613dfc132b8c44b75dd2917a393d612329c4; D1Bound5/SmallPairPureClosureData23.lean, lines 14-16, SHA-256 d1850cc259f044990e773071529f613dfc132b8c44b75dd2917a393d612329c4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-1,-1)
noncomputable def b : PairLightCoordinate := (-2,1)
noncomputable def anchorRoot : PairLightCoordinate := (2, 0)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared23
end


