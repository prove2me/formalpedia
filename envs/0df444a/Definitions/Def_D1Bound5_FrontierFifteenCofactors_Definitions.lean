-- Prove2me | Definitions.Def_D1Bound5_FrontierFifteenCofactors_Definitions
-- name    : D1Bound5_FrontierFifteenCofactors_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:26:17.183828+00:00
-- url     : https://prove2.me/theorems/86953027-7bb1-414b-8c7d-d43ac24a2b74
-- title:
--   Frontier Fifteen Cofactors
-- statement:
--   Rounded rational entrywise bounds still retain enough margin for 59/20. Rounding avoids propagating large cubic rational coefficients. The named objects in this bundle include `frontierFifteenG`.
-- source:
--   D1Bound5/FrontierFifteenCofactors.lean, lines 57-63, SHA-256 829c42be3230279544c3ada7eba6c524a34af4542d6dc0b41600e5c49f9ec39c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix

namespace D1Bound5





/-- Rounded rational entrywise bounds still retain enough margin for
59/20. Rounding avoids propagating large cubic rational coefficients. -/
noncomputable def frontierFifteenG : Matrix (Fin 4) (Fin 4) ℝ :=
  !![252/1000,142/1000,142/1000,144/1000;
     142/1000,256/1000,143/1000,148/1000;
     142/1000,143/1000,277/1000,181/1000;
     144/1000,148/1000,181/1000,282/1000]



end D1Bound5
end


