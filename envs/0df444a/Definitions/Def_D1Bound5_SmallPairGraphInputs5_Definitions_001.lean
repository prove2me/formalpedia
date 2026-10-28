-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs5_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:26:09.521355+00:00
-- url     : https://prove2.me/theorems/e34cf83f-5434-4bdb-9ab6-5416db75fd41
-- title:
--   Small Pair Graph Inputs5 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_5`, `smallPairB_5`.
-- source:
--   D1Bound5/SmallPairGraphInputs5.lean, lines 8-8, SHA-256 4e6175434f08a998da01f33d442f64d85d9b1aac9654c3c0e0129d277e7f396e; D1Bound5/SmallPairGraphInputs5.lean, lines 9-9, SHA-256 4e6175434f08a998da01f33d442f64d85d9b1aac9654c3c0e0129d277e7f396e. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_5 : QuadInt 0 1 := ⟨-2,-1⟩
def smallPairB_5 : QuadInt 0 1 := ⟨0,2⟩





namespace PairGraphPrepared5



end PairGraphPrepared5
end D1Bound5
end


