-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData10_Definitions
-- name    : D1Bound5_SmallPairPureClosureData10_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:59:16.864517+00:00
-- url     : https://prove2.me/theorems/5e78b290-7780-4615-b911-1c4cba1ef990
-- title:
--   Small Pair Pure Closure Data10
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared10.a`, `PairLightClosurePrepared10.b`, `PairLightClosurePrepared10.anchorRoot`, `PairLightClosurePrepared10.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData10.lean, lines 10-10, SHA-256 e87e0313b6e0dc6d3637ca44e78aa29deebce618d351cc3a97df6acf81ba5a88; D1Bound5/SmallPairPureClosureData10.lean, lines 11-11, SHA-256 e87e0313b6e0dc6d3637ca44e78aa29deebce618d351cc3a97df6acf81ba5a88; D1Bound5/SmallPairPureClosureData10.lean, lines 12-12, SHA-256 e87e0313b6e0dc6d3637ca44e78aa29deebce618d351cc3a97df6acf81ba5a88; D1Bound5/SmallPairPureClosureData10.lean, lines 14-16, SHA-256 e87e0313b6e0dc6d3637ca44e78aa29deebce618d351cc3a97df6acf81ba5a88. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-1,-2)
noncomputable def b : PairLightCoordinate := (1,0)
noncomputable def anchorRoot : PairLightCoordinate := (1, -1)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared10
end


