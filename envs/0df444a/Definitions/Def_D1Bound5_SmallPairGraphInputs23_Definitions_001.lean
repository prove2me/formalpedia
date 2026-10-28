-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs23_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:19:35.209152+00:00
-- url     : https://prove2.me/theorems/6bfc50de-95f2-400a-829e-30e11583844a
-- title:
--   Small Pair Graph Inputs23 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_23`, `smallPairB_23`.
-- source:
--   D1Bound5/SmallPairGraphInputs23.lean, lines 8-8, SHA-256 37be4e50a7c309ed7169f219df043f40ae6d1cbc0256f256dfc9395232b14d8c; D1Bound5/SmallPairGraphInputs23.lean, lines 9-9, SHA-256 37be4e50a7c309ed7169f219df043f40ae6d1cbc0256f256dfc9395232b14d8c. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_23 : QuadInt 1 1 := ⟨-1,-1⟩
def smallPairB_23 : QuadInt 1 1 := ⟨-2,1⟩





namespace PairGraphPrepared23



end PairGraphPrepared23
end D1Bound5
end


