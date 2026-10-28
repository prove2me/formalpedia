-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs14_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:24:59.396992+00:00
-- url     : https://prove2.me/theorems/6689c53d-20b4-4c22-be48-92ce694dbfe2
-- title:
--   Small Pair Graph Inputs14 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_14`, `smallPairB_14`.
-- source:
--   D1Bound5/SmallPairGraphInputs14.lean, lines 8-8, SHA-256 913412abc11ab9aa604484441e17ee54b337c51b65dcdf65fc30132ae147e923; D1Bound5/SmallPairGraphInputs14.lean, lines 9-9, SHA-256 913412abc11ab9aa604484441e17ee54b337c51b65dcdf65fc30132ae147e923. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_14 : QuadInt 0 2 := ⟨-2,0⟩
def smallPairB_14 : QuadInt 0 2 := ⟨1,-1⟩





namespace PairGraphPrepared14



end PairGraphPrepared14
end D1Bound5
end


