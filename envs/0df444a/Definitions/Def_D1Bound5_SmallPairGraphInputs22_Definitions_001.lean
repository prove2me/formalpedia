-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs22_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:22:07.899231+00:00
-- url     : https://prove2.me/theorems/c2090816-85fe-40d2-b315-b0cd933dd1d9
-- title:
--   Small Pair Graph Inputs22 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_22`, `smallPairB_22`.
-- source:
--   D1Bound5/SmallPairGraphInputs22.lean, lines 8-8, SHA-256 80fc64a577b7f0bce1fad78a8a739fd743a5d3d0a54b1fba3b6fe37336797e1f; D1Bound5/SmallPairGraphInputs22.lean, lines 9-9, SHA-256 80fc64a577b7f0bce1fad78a8a739fd743a5d3d0a54b1fba3b6fe37336797e1f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt

def smallPairA_22 : QuadInt 1 1 := ⟨-2,0⟩
def smallPairB_22 : QuadInt 1 1 := ⟨2,0⟩





namespace PairGraphPrepared22



end PairGraphPrepared22
end D1Bound5
end


