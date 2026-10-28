-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs28_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs28_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:20:42.852557+00:00
-- url     : https://prove2.me/theorems/58d3d3b7-8182-40f2-a923-792d6c5763ae
-- title:
--   Small Pair Graph Inputs28 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_28`, `smallPairB_28`.
-- source:
--   D1Bound5/SmallPairGraphInputs28.lean, lines 8-8, SHA-256 2d1f54020040b796f5fa2ce20b0cb5d6e80fdf5c0f3e2eab321bf1c320dd92e1; D1Bound5/SmallPairGraphInputs28.lean, lines 9-9, SHA-256 2d1f54020040b796f5fa2ce20b0cb5d6e80fdf5c0f3e2eab321bf1c320dd92e1. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_28 : QuadInt 1 1 := ⟨-1,0⟩
def smallPairB_28 : QuadInt 1 1 := ⟨1,-3⟩





namespace PairGraphPrepared28



end PairGraphPrepared28
end D1Bound5
end


