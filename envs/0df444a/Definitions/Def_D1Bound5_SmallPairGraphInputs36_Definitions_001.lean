-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs36_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:26:24.538388+00:00
-- url     : https://prove2.me/theorems/42c1535f-c3d2-4d65-8255-e97b529fe510
-- title:
--   Small Pair Graph Inputs36 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_36`, `smallPairB_36`.
-- source:
--   D1Bound5/SmallPairGraphInputs36.lean, lines 8-8, SHA-256 a6a4480b74a784398264e480e77831de37730ececbb5a84d976243b025b5b18f; D1Bound5/SmallPairGraphInputs36.lean, lines 9-9, SHA-256 a6a4480b74a784398264e480e77831de37730ececbb5a84d976243b025b5b18f. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_36 : QuadInt 1 2 := ⟨-2,-1⟩
def smallPairB_36 : QuadInt 1 2 := ⟨1,0⟩





namespace PairGraphPrepared36



end PairGraphPrepared36
end D1Bound5
end


