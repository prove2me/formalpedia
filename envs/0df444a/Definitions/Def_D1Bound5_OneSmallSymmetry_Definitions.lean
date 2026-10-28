-- Prove2me | Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
-- name    : D1Bound5_OneSmallSymmetry_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:55:19.125383+00:00
-- url     : https://prove2.me/theorems/44ff14fd-fc4b-4e0c-90a2-9af7455d3b02
-- title:
--   One Small Symmetry
-- statement:
--   Definitions for one small symmetry in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `firstPairRowA`, `firstPairRowB`, `OneSmallNormalizedThirdRows`.
-- source:
--   D1Bound5/OneSmallSymmetry.lean, lines 8-9, SHA-256 5e7e3f65dba87e2dd4102a7d04f343cef185fdf9cab42f19077c0873af7b7347; D1Bound5/OneSmallSymmetry.lean, lines 11-12, SHA-256 5e7e3f65dba87e2dd4102a7d04f343cef185fdf9cab42f19077c0873af7b7347; D1Bound5/OneSmallSymmetry.lean, lines 68-72, SHA-256 5e7e3f65dba87e2dd4102a7d04f343cef185fdf9cab42f19077c0873af7b7347. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
namespace D1Bound5
open QuadInt

def firstPairRowA (tau nu : ℤ) (row : (ℤ × ℤ) × (ℤ × ℤ)) : QuadInt tau nu :=
  ⟨row.1.1,row.1.2⟩

def firstPairRowB (tau nu : ℤ) (row : (ℤ × ℤ) × (ℤ × ℤ)) : QuadInt tau nu :=
  ⟨row.2.1,row.2.2⟩







def OneSmallNormalizedThirdRows {tau nu : ℤ} (a b s : QuadInt tau nu) : Prop :=
  ∃ sgn conj : Bool,
    let F := smallExtensionSymmetry (tau := tau) (nu := nu) sgn conj
    (F a = 1 ∧ F b = -3 ∧ F s = 3) ∨
      ∃ cutoff, OneSmallRowMembership (F a) (F b) (F s) cutoff



end D1Bound5
end


