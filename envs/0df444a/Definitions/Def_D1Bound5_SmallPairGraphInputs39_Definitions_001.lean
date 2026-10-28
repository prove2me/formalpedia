-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs39_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:26:24.335815+00:00
-- url     : https://prove2.me/theorems/325ae441-cf9f-4281-9f0c-4ec8df0913a2
-- title:
--   Small Pair Graph Inputs39 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_39`, `smallPairB_39`.
-- source:
--   D1Bound5/SmallPairGraphInputs39.lean, lines 8-8, SHA-256 160ac97a2be982c0553d704358797eadd21a266d2cb5d58956a449f97594fc59; D1Bound5/SmallPairGraphInputs39.lean, lines 9-9, SHA-256 160ac97a2be982c0553d704358797eadd21a266d2cb5d58956a449f97594fc59. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_39 : QuadInt 1 2 := ⟨-1,-1⟩
def smallPairB_39 : QuadInt 1 2 := ⟨1,1⟩





namespace PairGraphPrepared39



end PairGraphPrepared39
end D1Bound5
end


