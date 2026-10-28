-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs34_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:22:14.923406+00:00
-- url     : https://prove2.me/theorems/aab658e2-00da-4c9f-99d2-267bb705beec
-- title:
--   Small Pair Graph Inputs34 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_34`, `smallPairB_34`.
-- source:
--   D1Bound5/SmallPairGraphInputs34.lean, lines 8-8, SHA-256 80081fbe80d8267dc85a4c97cf17a7c063a9e61364395f31e58acc93a3d048b9; D1Bound5/SmallPairGraphInputs34.lean, lines 9-9, SHA-256 80081fbe80d8267dc85a4c97cf17a7c063a9e61364395f31e58acc93a3d048b9. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_34 : QuadInt 1 2 := ⟨-2,-1⟩
def smallPairB_34 : QuadInt 1 2 := ⟨0,-1⟩





namespace PairGraphPrepared34



end PairGraphPrepared34
end D1Bound5
end


