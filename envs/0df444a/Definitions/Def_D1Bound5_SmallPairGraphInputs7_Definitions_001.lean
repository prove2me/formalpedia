-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs7_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:26:08.6171+00:00
-- url     : https://prove2.me/theorems/a3eb95d4-fab2-4ce3-8d90-d2eb900e5280
-- title:
--   Small Pair Graph Inputs7 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_7`, `smallPairB_7`.
-- source:
--   D1Bound5/SmallPairGraphInputs7.lean, lines 8-8, SHA-256 0c6a50693b080eb714e72cba8f1a8cabf6d56ceae0b49770b8a8581c06335097; D1Bound5/SmallPairGraphInputs7.lean, lines 9-9, SHA-256 0c6a50693b080eb714e72cba8f1a8cabf6d56ceae0b49770b8a8581c06335097. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_7 : QuadInt 0 1 := ⟨-2,0⟩
def smallPairB_7 : QuadInt 0 1 := ⟨-1,-2⟩





namespace PairGraphPrepared7



end PairGraphPrepared7
end D1Bound5
end


