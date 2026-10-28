-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs3_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:26:24.669191+00:00
-- url     : https://prove2.me/theorems/87998d55-3f16-4f1e-a0af-677b916d3d32
-- title:
--   Small Pair Graph Inputs3 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_3`, `smallPairB_3`.
-- source:
--   D1Bound5/SmallPairGraphInputs3.lean, lines 8-8, SHA-256 a2060547d6581e20f545c7e19b614ba81c5b621f4b74f09542728f5c0cd6e190; D1Bound5/SmallPairGraphInputs3.lean, lines 9-9, SHA-256 a2060547d6581e20f545c7e19b614ba81c5b621f4b74f09542728f5c0cd6e190. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt

def smallPairA_3 : QuadInt 0 1 := ⟨-2,-2⟩
def smallPairB_3 : QuadInt 0 1 := ⟨2,0⟩





namespace PairGraphPrepared3



end PairGraphPrepared3
end D1Bound5
end


