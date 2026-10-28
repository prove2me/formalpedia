-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs25_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs25_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:22:10.875964+00:00
-- url     : https://prove2.me/theorems/fd7a61db-e97c-4526-a92a-a5e5750610da
-- title:
--   Small Pair Graph Inputs25 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_25`, `smallPairB_25`.
-- source:
--   D1Bound5/SmallPairGraphInputs25.lean, lines 8-8, SHA-256 e21e9c8c3f0ad8438726b3bcb26af38e89411d1090e9304422abee471ce9c18b; D1Bound5/SmallPairGraphInputs25.lean, lines 9-9, SHA-256 e21e9c8c3f0ad8438726b3bcb26af38e89411d1090e9304422abee471ce9c18b. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_25 : QuadInt 1 1 := ⟨-1,-1⟩
def smallPairB_25 : QuadInt 1 1 := ⟨1,-1⟩





namespace PairGraphPrepared25



end PairGraphPrepared25
end D1Bound5
end


