-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs43_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:26:19.884016+00:00
-- url     : https://prove2.me/theorems/cc8c4e14-0c7f-4720-9f72-82a170c62b77
-- title:
--   Small Pair Graph Inputs43 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_43`, `smallPairB_43`.
-- source:
--   D1Bound5/SmallPairGraphInputs43.lean, lines 8-8, SHA-256 4f8fe115d6404e1d98e2072adad71686b983e444069ed6e86739c4ba59ead417; D1Bound5/SmallPairGraphInputs43.lean, lines 9-9, SHA-256 4f8fe115d6404e1d98e2072adad71686b983e444069ed6e86739c4ba59ead417. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_43 : QuadInt 1 3 := ⟨0,-1⟩
def smallPairB_43 : QuadInt 1 3 := ⟨-1,1⟩





namespace PairGraphPrepared43



end PairGraphPrepared43
end D1Bound5
end


