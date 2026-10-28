-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData21_Definitions
-- name    : D1Bound5_SmallPairPureClosureData21_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:31.76465+00:00
-- url     : https://prove2.me/theorems/3effcef6-c2bb-4f2a-ac35-d2181d5910ac
-- title:
--   Small Pair Pure Closure Data21
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared21.a`, `PairLightClosurePrepared21.b`, `PairLightClosurePrepared21.anchorRoot`, `PairLightClosurePrepared21.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData21.lean, lines 10-10, SHA-256 6c6abb92f65b2f6b7ebc9f22448377e2313ae6641ae9d180f080305a00ec9b84; D1Bound5/SmallPairPureClosureData21.lean, lines 11-11, SHA-256 6c6abb92f65b2f6b7ebc9f22448377e2313ae6641ae9d180f080305a00ec9b84; D1Bound5/SmallPairPureClosureData21.lean, lines 12-12, SHA-256 6c6abb92f65b2f6b7ebc9f22448377e2313ae6641ae9d180f080305a00ec9b84; D1Bound5/SmallPairPureClosureData21.lean, lines 14-16, SHA-256 6c6abb92f65b2f6b7ebc9f22448377e2313ae6641ae9d180f080305a00ec9b84. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-1,-2)
noncomputable def b : PairLightCoordinate := (0,1)
noncomputable def anchorRoot : PairLightCoordinate := (2, -1)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared21
end


