-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData8_Definitions
-- name    : D1Bound5_SmallPairPureClosureData8_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:58:53.419978+00:00
-- url     : https://prove2.me/theorems/1116a038-f63f-465d-ae0d-d8182a8f0c5d
-- title:
--   Small Pair Pure Closure Data8
-- statement:
--   Exact anchor coordinates and assembled square-root witness data for the coordinate mutation-closure calculation. The named objects in this bundle include `PairLightClosurePrepared8.a`, `PairLightClosurePrepared8.b`, `PairLightClosurePrepared8.anchorRoot`, `PairLightClosurePrepared8.witnesses`.
-- source:
--   D1Bound5/SmallPairPureClosureData8.lean, lines 10-10, SHA-256 cba4bc08fc45c9ba11354d91617b7fc6b6fcaf61925b5b9204b2cd94c227292d; D1Bound5/SmallPairPureClosureData8.lean, lines 11-11, SHA-256 cba4bc08fc45c9ba11354d91617b7fc6b6fcaf61925b5b9204b2cd94c227292d; D1Bound5/SmallPairPureClosureData8.lean, lines 12-12, SHA-256 cba4bc08fc45c9ba11354d91617b7fc6b6fcaf61925b5b9204b2cd94c227292d; D1Bound5/SmallPairPureClosureData8.lean, lines 14-16, SHA-256 cba4bc08fc45c9ba11354d91617b7fc6b6fcaf61925b5b9204b2cd94c227292d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8RootPairs_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8Vertices_Definitions

section
namespace D1Bound5.PairLightClosurePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def a : PairLightCoordinate := (-2,0)
noncomputable def b : PairLightCoordinate := (1,0)
noncomputable def anchorRoot : PairLightCoordinate := (0, 1)

noncomputable def witnesses : List PairLightRootWitness :=
  List.zipWith (fun (z : PairLightCoordinate) (rs : PairLightCoordinate × PairLightCoordinate) =>
    ⟨z, rs.1, rs.2⟩) vertices rootPairs

end D1Bound5.PairLightClosurePrepared8
end


