-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs30_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:19:32.896876+00:00
-- url     : https://prove2.me/theorems/6138d6e2-8662-4bc1-9748-6ba92ed4e24c
-- title:
--   Small Pair Graph Inputs30 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_30`, `smallPairB_30`.
-- source:
--   D1Bound5/SmallPairGraphInputs30.lean, lines 8-8, SHA-256 2596ea6721a775627e48823bf016d57c8d6352503a30474af080bc62df058875; D1Bound5/SmallPairGraphInputs30.lean, lines 9-9, SHA-256 2596ea6721a775627e48823bf016d57c8d6352503a30474af080bc62df058875. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_30 : QuadInt 1 1 := ⟨1,-2⟩
def smallPairB_30 : QuadInt 1 1 := ⟨-1,2⟩





namespace PairGraphPrepared30



end PairGraphPrepared30
end D1Bound5
end


