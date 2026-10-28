-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs19_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:19:37.36898+00:00
-- url     : https://prove2.me/theorems/f0508459-06bb-4e43-b00b-81688db3f55c
-- title:
--   Small Pair Graph Inputs19 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_19`, `smallPairB_19`.
-- source:
--   D1Bound5/SmallPairGraphInputs19.lean, lines 8-8, SHA-256 30ad07567881482cb51433ba7277178b8be9aa68fbd82129d3335a0c8d9aba0b; D1Bound5/SmallPairGraphInputs19.lean, lines 9-9, SHA-256 30ad07567881482cb51433ba7277178b8be9aa68fbd82129d3335a0c8d9aba0b. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_19 : QuadInt 1 1 := ⟨-2,-1⟩
def smallPairB_19 : QuadInt 1 1 := ⟨1,1⟩





namespace PairGraphPrepared19



end PairGraphPrepared19
end D1Bound5
end


