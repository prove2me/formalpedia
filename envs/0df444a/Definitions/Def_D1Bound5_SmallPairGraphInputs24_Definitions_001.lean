-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs24_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:26:24.666043+00:00
-- url     : https://prove2.me/theorems/318fe53e-4199-4c3d-955a-8b1f3bff3ca9
-- title:
--   Small Pair Graph Inputs24 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_24`, `smallPairB_24`.
-- source:
--   D1Bound5/SmallPairGraphInputs24.lean, lines 8-8, SHA-256 0c23919a4646059158c9a8cacfaafd3c1a79a639601d57f38c3cac30e782c7c9; D1Bound5/SmallPairGraphInputs24.lean, lines 9-9, SHA-256 0c23919a4646059158c9a8cacfaafd3c1a79a639601d57f38c3cac30e782c7c9. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_24 : QuadInt 1 1 := ⟨-1,-1⟩
def smallPairB_24 : QuadInt 1 1 := ⟨2,-3⟩





namespace PairGraphPrepared24



end PairGraphPrepared24
end D1Bound5
end


