-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs6_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:23:19.552863+00:00
-- url     : https://prove2.me/theorems/a7464b18-84ea-46c9-8e37-f1d97728ae5c
-- title:
--   Small Pair Graph Inputs6 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_6`, `smallPairB_6`.
-- source:
--   D1Bound5/SmallPairGraphInputs6.lean, lines 8-8, SHA-256 abe4222e5f2cfd8c04b627415b530656050952ce8f2826b982c40df366b2c344; D1Bound5/SmallPairGraphInputs6.lean, lines 9-9, SHA-256 abe4222e5f2cfd8c04b627415b530656050952ce8f2826b982c40df366b2c344. Project: https://github.com/tomislav-math/d1-bound5-lean

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

noncomputable def smallPairA_6 : QuadInt 0 1 := ⟨-2,-1⟩
noncomputable def smallPairB_6 : QuadInt 0 1 := ⟨2,-1⟩





namespace PairGraphPrepared6



end PairGraphPrepared6
end D1Bound5
end


