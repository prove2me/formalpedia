-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_RationalTransfer
-- name    : OAI_Algebra_FormulaHitting_RationalTransfer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:04:30.50516+00:00
-- url     : https://prove2.me/theorems/b1a7efac-e378-4cae-a7bf-c52e38cc9e37
-- title:
--   Jets of power series and the kernel of a jet map
-- statement:
--   Let $F$ be a field and $d\in\mathbb{N}$.
--
--   1. **Jet.** The $F$-linear map $F[[X]]\to F^d$ given by
--   $$
--   \mathrm{jet}_d(a)=\bigl([X^0]a,\,[X^1]a,\dots,[X^{d-1}]a\bigr),
--   $$
--   which records the first $d$ coefficients.
--   2. **Jet kernel.** For a finite family $(a_\iota)_{\iota\in\iota_0}$ of power series, this is the subspace of coefficient vectors $c\in F^{\iota_0}$ whose combination vanishes to order $d$:
--   $$
--   \Bigl\{\,c\;:\;[X^r]\sum_\iota c_\iota a_\iota=0\ \text{ for all } r<d\,\Bigr\}.
--   $$
--
--   Jets transfer statements about power series to finite-dimensional linear algebra. A linear relation among power series that holds up to order $d$ is a vector in the jet kernel.
--
--   **Formalization Note** `jet d` is a linear map into `Fin d → F`. `jetKernel a d` is the kernel of `jet d` composed with `Fintype.linearCombination F a`, and `mem_jetKernel` unfolds membership.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/RationalTransfer.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/RationalTransfer.lean by skeleton subtraction
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
import Definitions.Def_OAI_Algebra_FormulaHitting_Independence
import Definitions.Def_OAI_Algebra_FormulaHitting_WordIndependence

namespace OAI

noncomputable section
open PowerSeries
namespace NCHitting

variable {F : Type*} [Field F]

def jet (d : ℕ) : PowerSeries F →ₗ[F] (Fin d → F) where
  toFun a r := PowerSeries.coeff r.val a
  map_add' a b := by ext r; simp
  map_smul' c a := by ext r; simp

@[simp] theorem jet_apply (d : ℕ) (a : PowerSeries F) (r : Fin d) :
    jet d a r = PowerSeries.coeff r.val a := rfl

section FiniteFamily
variable {ι : Type*} [Fintype ι]

def jetKernel (a : ι → PowerSeries F) (d : ℕ) : Submodule F (ι → F) :=
  LinearMap.ker ((jet d).comp (Fintype.linearCombination F a))

@[simp] theorem mem_jetKernel (a : ι → PowerSeries F) (d : ℕ) (c : ι → F) :
    c ∈ jetKernel a d ↔ ∀ r < d,
      PowerSeries.coeff r (Fintype.linearCombination F a c) = 0 := by
  simp only [jetKernel, LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro h r hr
    exact congrFun h ⟨r, hr⟩
  · intro h
    ext r
    exact h r.val r.isLt

end FiniteFamily
end NCHitting

end

end OAI


