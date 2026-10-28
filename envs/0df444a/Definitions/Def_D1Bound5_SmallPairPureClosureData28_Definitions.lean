-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData28_Definitions
-- name    : D1Bound5_SmallPairPureClosureData28_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:02.193332+00:00
-- url     : https://prove2.me/theorems/d7afd111-b3a2-4878-99bc-db1edaef0ecb
-- title:
--   Small Pair Pure Closure Data28
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared28.a`, `PairLightClosurePrepared28.b`, `PairLightClosurePrepared28.anchorRoot`, `PairLightClosurePrepared28.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData28.lean, lines 10-10, SHA-256 df4bd8a04f75abf8c52f747d1f2364aeca58d091e35cca6b02041a9625584ee4; D1Bound5/SmallPairPureClosureData28.lean, lines 11-11, SHA-256 df4bd8a04f75abf8c52f747d1f2364aeca58d091e35cca6b02041a9625584ee4; D1Bound5/SmallPairPureClosureData28.lean, lines 12-12, SHA-256 df4bd8a04f75abf8c52f747d1f2364aeca58d091e35cca6b02041a9625584ee4; D1Bound5/SmallPairPureClosureData28.lean, lines 14-16, SHA-256 df4bd8a04f75abf8c52f747d1f2364aeca58d091e35cca6b02041a9625584ee4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared28
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-1,0)
noncomputable def b : PairLightCoordinate := (1,-3)
noncomputable def anchorRoot : PairLightCoordinate := (1, 1)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared28
end


