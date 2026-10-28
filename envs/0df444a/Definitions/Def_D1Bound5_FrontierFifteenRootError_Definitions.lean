-- Prove2me | Definitions.Def_D1Bound5_FrontierFifteenRootError_Definitions
-- name    : D1Bound5_FrontierFifteenRootError_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:49:02.849657+00:00
-- url     : https://prove2.me/theorems/b423caac-e8ca-459a-b85e-0dae7d17f6b9
-- title:
--   Frontier Fifteen Root Error
-- statement:
--   Definitions for frontier fifteen root error in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `frontierFifteenK`, `frontierFifteenMin`.
-- source:
--   D1Bound5/FrontierFifteenRootError.lean, lines 52-56, SHA-256 24dc95017a8ebeb8c577aed5d93ddcda41177bb23f3f88798738501f0f343cfb; D1Bound5/FrontierFifteenRootError.lean, lines 58-59, SHA-256 24dc95017a8ebeb8c577aed5d93ddcda41177bb23f3f88798738501f0f343cfb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5





noncomputable def frontierFifteenK : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,5506/10000,5087/10000,5014/10000;
     5506/10000,0,5029/10000,5005/10000;
     5087/10000,5029/10000,0,5001/10000;
     5014/10000,5005/10000,5001/10000,0]

noncomputable def frontierFifteenMin : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,3,15,90; 3,0,45,270; 15,45,0,1350; 90,270,1350,0]



end D1Bound5
end


