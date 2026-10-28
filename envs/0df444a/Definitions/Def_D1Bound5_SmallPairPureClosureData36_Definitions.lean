-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData36_Definitions
-- name    : D1Bound5_SmallPairPureClosureData36_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:08.484042+00:00
-- url     : https://prove2.me/theorems/c2b43a08-8f4d-4cfb-96ec-6449d685cfd5
-- title:
--   Small Pair Pure Closure Data36
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared36.a`, `PairLightClosurePrepared36.b`, `PairLightClosurePrepared36.anchorRoot`, `PairLightClosurePrepared36.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData36.lean, lines 10-10, SHA-256 aa6a6c5f49de7c442b97e19d7220dcd31e5f79557ecbb67875cea755d875549c; D1Bound5/SmallPairPureClosureData36.lean, lines 11-11, SHA-256 aa6a6c5f49de7c442b97e19d7220dcd31e5f79557ecbb67875cea755d875549c; D1Bound5/SmallPairPureClosureData36.lean, lines 12-12, SHA-256 aa6a6c5f49de7c442b97e19d7220dcd31e5f79557ecbb67875cea755d875549c; D1Bound5/SmallPairPureClosureData36.lean, lines 14-16, SHA-256 aa6a6c5f49de7c442b97e19d7220dcd31e5f79557ecbb67875cea755d875549c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-2,-1)
noncomputable def b : PairLightCoordinate := (1,0)
noncomputable def anchorRoot : PairLightCoordinate := (1, -1)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared36
end


