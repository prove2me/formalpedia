-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs15_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:22:09.853873+00:00
-- url     : https://prove2.me/theorems/70ae2a06-fbda-49b4-8d20-29a261a6869f
-- title:
--   Small Pair Graph Inputs15 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_15`, `smallPairB_15`.
-- source:
--   D1Bound5/SmallPairGraphInputs15.lean, lines 8-8, SHA-256 5cbbeb5290906da99b793e377eadac74f874585dcfa4d7efe019dbb4b21155ec; D1Bound5/SmallPairGraphInputs15.lean, lines 9-9, SHA-256 5cbbeb5290906da99b793e377eadac74f874585dcfa4d7efe019dbb4b21155ec. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_15 : QuadInt 0 2 := ⟨-1,-1⟩
def smallPairB_15 : QuadInt 0 2 := ⟨-1,1⟩





namespace PairGraphPrepared15



end PairGraphPrepared15
end D1Bound5
end


