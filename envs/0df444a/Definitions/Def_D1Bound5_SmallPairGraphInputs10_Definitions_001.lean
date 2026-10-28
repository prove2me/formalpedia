-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs10_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:19:33.271515+00:00
-- url     : https://prove2.me/theorems/77a80493-d685-425f-9c7f-3c83467942ad
-- title:
--   Small Pair Graph Inputs10 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_10`, `smallPairB_10`.
-- source:
--   D1Bound5/SmallPairGraphInputs10.lean, lines 8-8, SHA-256 219b2b1a4f7fcdb3fcd8d93c4768da1d8fb4cc3edb1c20b183f23c91353db0d1; D1Bound5/SmallPairGraphInputs10.lean, lines 9-9, SHA-256 219b2b1a4f7fcdb3fcd8d93c4768da1d8fb4cc3edb1c20b183f23c91353db0d1. Project: https://github.com/tomislav-math/d1-bound5-lean

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

noncomputable def smallPairA_10 : QuadInt 0 1 := ⟨-1,-2⟩
noncomputable def smallPairB_10 : QuadInt 0 1 := ⟨1,0⟩





namespace PairGraphPrepared10



end PairGraphPrepared10
end D1Bound5
end


