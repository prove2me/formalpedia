-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData30_Definitions
-- name    : D1Bound5_SmallPairPureClosureData30_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:20.830189+00:00
-- url     : https://prove2.me/theorems/33485ea5-87e5-42d8-b091-0abddd4cb4c1
-- title:
--   Small Pair Pure Closure Data30
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared30.a`, `PairLightClosurePrepared30.b`, `PairLightClosurePrepared30.anchorRoot`, `PairLightClosurePrepared30.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData30.lean, lines 10-10, SHA-256 3eb6bef765424dd801e1fc2f042bda188b8a04e2dc9c11029d74942ead452f4a; D1Bound5/SmallPairPureClosureData30.lean, lines 11-11, SHA-256 3eb6bef765424dd801e1fc2f042bda188b8a04e2dc9c11029d74942ead452f4a; D1Bound5/SmallPairPureClosureData30.lean, lines 12-12, SHA-256 3eb6bef765424dd801e1fc2f042bda188b8a04e2dc9c11029d74942ead452f4a; D1Bound5/SmallPairPureClosureData30.lean, lines 14-16, SHA-256 3eb6bef765424dd801e1fc2f042bda188b8a04e2dc9c11029d74942ead452f4a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (1,-2)
noncomputable def b : PairLightCoordinate := (-1,2)
noncomputable def anchorRoot : PairLightCoordinate := (2, 0)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared30
end


