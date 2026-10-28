-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs21_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:20:39.737762+00:00
-- url     : https://prove2.me/theorems/8af5cfb0-9935-47e0-899c-19b6b0ae936c
-- title:
--   Small Pair Graph Inputs21 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_21`, `smallPairB_21`.
-- source:
--   D1Bound5/SmallPairGraphInputs21.lean, lines 8-8, SHA-256 a825d89608291e2e65b4c0e868604e01c90aeb48a977268554f932e7828d58e3; D1Bound5/SmallPairGraphInputs21.lean, lines 9-9, SHA-256 a825d89608291e2e65b4c0e868604e01c90aeb48a977268554f932e7828d58e3. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_21 : QuadInt 1 1 := ⟨-1,-2⟩
def smallPairB_21 : QuadInt 1 1 := ⟨0,1⟩





namespace PairGraphPrepared21



end PairGraphPrepared21
end D1Bound5
end


