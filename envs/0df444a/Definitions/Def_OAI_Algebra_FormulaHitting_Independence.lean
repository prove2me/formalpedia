-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_Independence
-- name    : OAI_Algebra_FormulaHitting_Independence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:02:37.193335+00:00
-- url     : https://prove2.me/theorems/f93ce004-341d-4378-ac1e-25335090eb2f
-- title:
--   Pole products and punctured pole products of a family of field elements
-- statement:
--   Let $F$ be a field, $\iota$ a finite index set with decidable equality, and $a:\iota\to F$ a family of points.
--
--   1. **Pole product.**
--   $$
--   \pi_a(X)=\prod_{i\in\iota}\bigl(X-a_i\bigr)\in F[X].
--   $$
--   2. **Punctured pole product.** For $i\in\iota$, $\pi_{a,i}(X)=\prod_{j\ne i}(X-a_j)$.
--
--   When the $a_i$ are distinct, $\pi_{a,i}/\pi_a=1/(X-a_i)$. These polynomials are used to put sums of simple fractions over a common denominator, for instance in linear-independence arguments for rational functions with distinct poles.
--
--   **Formalization Note** The names are `poleProduct a` and `puncturedPoleProduct a i`; the second product runs over `Finset.univ.erase i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Independence.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Independence.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FormulaHitting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis
import Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity
import Definitions.Def_OAI_Algebra_FormulaHitting_Formula
import Definitions.Def_OAI_Algebra_FormulaHitting_Representation
import Definitions.Def_OAI_Algebra_FormulaHitting_Series
import Definitions.Def_OAI_Algebra_FormulaHitting_System
import Definitions.Def_OAI_Algebra_FormulaHitting_Evaluation
import Definitions.Def_OAI_Algebra_FormulaHitting_FormulaSeries

namespace OAI

noncomputable section
open Polynomial
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F]

section FormalResidue
open PowerSeries

end FormalResidue

section DistinctPoles
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def poleProduct (a : ι → F) : F[X] := ∏ i, (Polynomial.X - Polynomial.C (a i))

def puncturedPoleProduct (a : ι → F) (i : ι) : F[X] :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (a j))

end DistinctPoles

end NCHitting

end

end OAI


