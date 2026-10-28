-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs29_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:26:22.007+00:00
-- url     : https://prove2.me/theorems/107ccb93-9c88-4101-bfc6-a09f1d118f68
-- title:
--   Small Pair Graph Inputs29 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_29`, `smallPairB_29`.
-- source:
--   D1Bound5/SmallPairGraphInputs29.lean, lines 8-8, SHA-256 83d8096af5153ef2a46dfecec9766ab37b4c65476c37fc8afb2c5a9bc632bc81; D1Bound5/SmallPairGraphInputs29.lean, lines 9-9, SHA-256 83d8096af5153ef2a46dfecec9766ab37b4c65476c37fc8afb2c5a9bc632bc81. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def smallPairA_29 : QuadInt 1 1 := ⟨0,-1⟩
def smallPairB_29 : QuadInt 1 1 := ⟨1,-2⟩





namespace PairGraphPrepared29



end PairGraphPrepared29
end D1Bound5
end


