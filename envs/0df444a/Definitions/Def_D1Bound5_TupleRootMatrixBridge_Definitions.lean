-- Prove2me | Definitions.Def_D1Bound5_TupleRootMatrixBridge_Definitions
-- name    : D1Bound5_TupleRootMatrixBridge_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T03:35:43.283077+00:00
-- url     : https://prove2.me/theorems/46df74c0-2b14-456f-aca0-bfc89ddd01a6
-- title:
--   Tuple Root Matrix Bridge
-- statement:
--   Choose a square root indexed by the unordered pair {i,j}; swapping indices does not change the chosen root. The named objects in this bundle include `tuplePairRoot`. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/TupleRootMatrixBridge.lean, lines 9-18, SHA-256 18bf68c70f7461d132ff1bb7a87d58364bb611e213e0471f018bd1b883568dd6; D1Bound5/TupleRootMatrixBridge.lean, lines 20-24, SHA-256 18bf68c70f7461d132ff1bb7a87d58364bb611e213e0471f018bd1b883568dd6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField
open Module

namespace D1Bound5

 theorem min_ne_max_fin {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    min i j ≠ max i j := by
  intro h
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have he : i = j := by
      simpa [min_eq_left hlt.le, max_eq_right hlt.le] using h
    exact hij he
  · have he : j = i := by
      simpa [min_eq_right hgt.le, max_eq_left hgt.le] using h
    exact hij he.symm

/-- Choose a square root indexed by the unordered pair {i,j}; swapping
indices does not change the chosen root. -/
 noncomputable def tuplePairRoot {R : Type*} [CommRing R] {n : ℕ}
    (t : Fin n → R) (ht : IsD1Tuple t) (i j : Fin n) (hij : i ≠ j) : R :=
  Classical.choose (ht.2.2 (min i j) (max i j) (min_ne_max_fin i j hij))









end D1Bound5
end


