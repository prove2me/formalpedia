-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity
-- name    : OAI_Algebra_FormulaHitting_Multiplicity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T08:56:42.508868+00:00
-- url     : https://prove2.me/theorems/388ee02f-c1c8-4a06-b124-c90932c9f2b4
-- title:
--   Derivative matrix of a family of power series and the scalar output of a matrix system
-- statement:
--   Let $F$ be a field and $F[[X]]$ its power series ring, with iterated formal derivatives $D^j$.
--
--   1. **Derivative matrix.** For $k\in\mathbb{N}$ and a family $(h_t)_{t\in I}$ of power series indexed by a type $I$, this is the $k\times I$ matrix
--   $$
--   \bigl(D^jh_t\bigr)_{0\le j<k,\ t\in I}.
--   $$
--   2. **Scalar output.** For a finite index set $I$, vectors $u,v\in F^I$ and a matrix $G\in F[[X]]^{I\times I}$,
--   $$
--   \mathrm{out}(u,v,G)=\sum_{l\in I}\Bigl(\sum_{t\in I}u_t\,G_{tl}\Bigr)v_l=u^{\mathsf T}G\,v\in F[[X]].
--   $$
--
--   The derivative matrix collects the first $k$ derivatives of a family, which is the input to rank and multiplicity arguments. The scalar output reads off the power series that a weighted automaton computes from its solution matrix.
--
--   **Formalization Note** The names are `derivativeMatrix k h` and `systemScalarOutput u v G`. Scalars enter through the constant embedding `PowerSeries.C`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Multiplicity.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Multiplicity.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Polynomial Matrix Submodule

variable {F : Type*} [Field F] [CharZero F]

def derivativeMatrix {I : Type*} (k : ℕ) (h : I → PowerSeries F) :
    Matrix (Fin k) I (PowerSeries F) := fun j t => derivativeIter j.val (h t)

variable {I : Type*} [Fintype I] [DecidableEq I]

def systemScalarOutput (u v : I → F) (G : Matrix I I (PowerSeries F)) :
    PowerSeries F := ∑ l : I, (∑ t : I, PowerSeries.C (u t) * G t l) * PowerSeries.C (v l)

end NCHitting

end

end OAI


