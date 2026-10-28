-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs8_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs8_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:26:33.381997+00:00
-- url     : https://prove2.me/theorems/8836b5a3-c23d-4884-85eb-43d5b0db23d6
-- title:
--   Small Pair Graph Inputs8 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_8`, `smallPairB_8`.
-- source:
--   D1Bound5/SmallPairGraphInputs8.lean, lines 8-8, SHA-256 2d35e2b09b182b5fe2000efc71ee2619bb0d2ada0178ccf47bec2cf1af061a77; D1Bound5/SmallPairGraphInputs8.lean, lines 9-9, SHA-256 2d35e2b09b182b5fe2000efc71ee2619bb0d2ada0178ccf47bec2cf1af061a77. Project: https://github.com/tomislav-math/d1-bound5-lean

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

noncomputable def smallPairA_8 : QuadInt 0 1 := ⟨-2,0⟩
noncomputable def smallPairB_8 : QuadInt 0 1 := ⟨1,0⟩





namespace PairGraphPrepared8



end PairGraphPrepared8
end D1Bound5
end


