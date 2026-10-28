-- Prove2me | Definitions.Def_D1Bound5_PairLightClosureBridge_Definitions
-- name    : D1Bound5_PairLightClosureBridge_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:42:10.928652+00:00
-- url     : https://prove2.me/theorems/9eacaf8f-0089-4104-ba4d-e110ffb31d39
-- title:
--   Pair Light Closure Bridge
-- statement:
--   Definitions for pair light closure bridge in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `pairLightRootWitnessCoordinates`.
-- source:
--   D1Bound5/PairLightClosureBridge.lean, lines 7-10, SHA-256 0da6268742f73a449f0c5571cfb1ac1e208c0ee42ca0b3c987a294921bc357aa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Order.Ring.Abs
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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions

section
namespace D1Bound5

def pairLightRootWitnessCoordinates {tau nu : ℤ} (w : PairRootWitness tau nu) :
    PairLightRootWitness :=
  ⟨pairLightCoordinates w.vertex, pairLightCoordinates w.leftRoot,
    pairLightCoordinates w.rightRoot⟩













end D1Bound5
end


