-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis
-- name    : OAI_Algebra_FormulaHitting_OrderBasis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T08:56:04.803988+00:00
-- url     : https://prove2.me/theorems/319fdb97-59fc-4097-9d11-767400cdcf45
-- title:
--   Order bases of subspaces of formal power series
-- statement:
--   Let $F$ be a field and $V$ an $F$-linear subspace of the power series ring $F[[X]]$. Write $[X^r]f$ for the coefficient of $X^r$ in $f$. The subspace $V$ has an order basis if there are $k\in\mathbb{N}$, power series $b_0,\dots,b_{k-1}$ and natural numbers $a_0,\dots,a_{k-1}$ such that:
--
--   1. $b_0,\dots,b_{k-1}$ are linearly independent over $F$ and span $V$;
--   2. the numbers $a_0,\dots,a_{k-1}$ are pairwise distinct;
--   3. each $b_i$ has order exactly $a_i$:
--   $$
--   [X^{a_i}]\,b_i\neq0,\qquad [X^r]\,b_i=0\quad\text{for all } r<a_i .
--   $$
--
--   In other words, $V$ has a basis whose elements have pairwise different orders. Every finite-dimensional subspace has one, by Gaussian elimination on leading coefficients. Such a basis makes the possible orders of elements of $V$ explicit and feeds into Wronskian arguments.
--
--   **Formalization Note** The predicate is `HasOrderBasis V`. Although the enclosing section assumes characteristic zero, the definition does not use that assumption.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/OrderBasis.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/OrderBasis.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Submodule

variable {F : Type*} [Field F] [CharZero F]

def HasOrderBasis (V : Submodule F (PowerSeries F)) : Prop :=
  ∃ (k : ℕ) (b : Fin k → PowerSeries F) (a : Fin k → ℕ),
    LinearIndependent F b ∧ Submodule.span F (Set.range b) = V ∧
      Function.Injective a ∧
      (∀ i, PowerSeries.coeff (a i) (b i) ≠ 0) ∧
      (∀ i r, r < a i → PowerSeries.coeff r (b i) = 0)

end NCHitting

end

end OAI


