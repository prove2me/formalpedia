-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs35_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:23:23.225413+00:00
-- url     : https://prove2.me/theorems/3f7fdcc1-8526-4807-91f6-3a0a4912f3e1
-- title:
--   Small Pair Graph Inputs35 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_35`, `smallPairB_35`.
-- source:
--   D1Bound5/SmallPairGraphInputs35.lean, lines 8-8, SHA-256 b99f4ed9ec14e1019988b04b79e862d326e9d95a222ed037df10eaca78e09176; D1Bound5/SmallPairGraphInputs35.lean, lines 9-9, SHA-256 b99f4ed9ec14e1019988b04b79e862d326e9d95a222ed037df10eaca78e09176. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_35 : QuadInt 1 2 := ⟨-2,-1⟩
def smallPairB_35 : QuadInt 1 2 := ⟨-1,2⟩





namespace PairGraphPrepared35



end PairGraphPrepared35
end D1Bound5
end


