-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_System
-- name    : OAI_Algebra_FormulaHitting_System
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T08:59:55.89799+00:00
-- url     : https://prove2.me/theorems/62dcfa21-045d-4db1-879c-927c3ce6427b
-- title:
--   Linear differential system, fundamental matrix and rational coefficients of an acyclic automaton
-- statement:
--   Let $F$ be a field of characteristic zero. Let $R$ be an acyclic representation with state set $Q$, vectors $u,v\in F^Q$ and transition matrices $B_0,\dots,B_{n-1}$; every transition strictly increases a rank function bounded by $|Q|$. Write $\kappa_i=\sum_r(-1)^ri^{-r-1}X^r$ for the power series of $1/(X+i)$ and $J_i(a)=\int a\,\kappa_i$ for the formal integral against it. The file defines the following.
--
--   1. **Levels.** Matrices $L_k\in F[[X]]^{Q\times Q}$ with $L_0=I$ and
--   $$
--   (L_{k+1})_{ab}=\sum_{i=0}^{n-1}\sum_{c\in Q}(B_i)_{ac}\,J_{i+1}\bigl((L_k)_{cb}\bigr).
--   $$
--   2. **System matrix.** $A_{ab}=\sum_{i}(B_i)_{ab}\,\kappa_{i+1}$, the coefficient matrix of the differential system satisfied by the levels.
--   3. **Fundamental matrix.** $\Gamma=\sum_{k=0}^{|Q|-1}L_k$. Acyclicity makes later levels vanish, so this finite sum plays the role of the full solution.
--   4. **Denominator and cofactors.** $\delta_n=\prod_{i=1}^{n}(X+i)\in F[X]$, and $c_i=\prod_{j\ne i}(X+j+1)$ for $i\in\{0,\dots,n-1\}$, so that $\kappa_{i+1}=c_i/\delta_n$.
--   5. **Numerator matrix.** $N_{ab}=\sum_i(B_i)_{ab}\,c_i\in F[X]$, so that $A=N/\delta_n$.
--   6. **Contraction.** The $F[[X]]$-linear functional $M\mapsto u^{\mathsf T}Mv$ on $Q\times Q$ matrices.
--
--   These objects express the power series computed by the automaton as the output of a linear differential system with rational coefficients, whose poles lie at $-1,\dots,-n$.
--
--   **Formalization Note** All definitions live in the namespace `AcyclicRepresentation`. Polynomials enter power series through the usual coercion, and scalars through `PowerSeries.C`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/System.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/System.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace NCHitting
namespace AcyclicRepresentation

open Matrix
variable {F : Type*} {n : ℕ} [Field F] [CharZero F]

def systemLevel (R : AcyclicRepresentation F n) :
    ℕ → Matrix R.State R.State (PowerSeries F)
  | 0 => 1
  | k + 1 => fun a b => ∑ i : Fin n, ∑ c : R.State,
      PowerSeries.C (R.B i a c) * J (i.val + 1) (systemLevel R k c b)

def systemMatrix (R : AcyclicRepresentation F n) :
    Matrix R.State R.State (PowerSeries F) :=
  fun a b => ∑ i : Fin n, PowerSeries.C (R.B i a b) * kernel (i.val + 1)

def fundamentalMatrix (R : AcyclicRepresentation F n) :
    Matrix R.State R.State (PowerSeries F) :=
  fun a b => ∑ k ∈ Finset.range (Fintype.card R.State), R.systemLevel k a b

def denominator (n : ℕ) : Polynomial F :=
  ∏ i : Fin n, (Polynomial.X + Polynomial.C ((i.val + 1 : ℕ) : F))

def cofactor (i : Fin n) : Polynomial F :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X + Polynomial.C ((j.val + 1 : ℕ) : F))

def systemNumerator (R : AcyclicRepresentation F n) :
    Matrix R.State R.State (Polynomial F) :=
  fun a b => ∑ i : Fin n, Polynomial.C (R.B i a b) * cofactor i

def contract (R : AcyclicRepresentation F n) :
    Matrix R.State R.State (PowerSeries F) →ₗ[PowerSeries F] PowerSeries F where
  toFun M := (fun a => PowerSeries.C (R.u a)) ⬝ᵥ
    (M *ᵥ (fun b => PowerSeries.C (R.v b)))
  map_add' M N := by simp [add_mulVec, dotProduct_add]
  map_smul' c M := by simp [smul_mulVec, dotProduct_smul]

end AcyclicRepresentation

end NCHitting

end

end OAI


