-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
-- name    : OAI_Algebra_FormulaHitting_Wronskian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T08:55:09.193332+00:00
-- url     : https://prove2.me/theorems/0e5f34be-d9f1-41a8-b6ea-c07a7c70e9a9
-- title:
--   Iterated formal derivatives, Wronskian of power series, and its normalized form
-- statement:
--   Let $F$ be a field and $F[[X]]$ the ring of formal power series over $F$, with formal derivative $f\mapsto f'$.
--
--   1. **Iterated derivative.** $D^0f=f$ and $D^{j+1}f=(D^jf)'$. Each $D^j$ is additive and $F$-linear.
--   2. **Shifted derivative tail.** For $f=\sum_r f_rX^r$ and $a,j\in\mathbb{N}$,
--   $$
--   T_{a,j}(f)=\sum_{r\ge0}f_{r+a}\,(r+a)^{\underline{j}}\,X^r,
--   $$
--   where $m^{\underline{j}}=m(m-1)\cdots(m-j+1)$ is the falling factorial. If $f$ vanishes to order $a$, then $X^jD^jf=X^aT_{a,j}(f)$.
--   3. **Wronskian.** For $b_0,\dots,b_{k-1}\in F[[X]]$, the Wronskian matrix is the $k\times k$ matrix $\bigl(D^jb_l\bigr)_{0\le j,l<k}$, and the Wronskian $W(b)$ is its determinant.
--   4. **Normalized Wronskian matrix.** For orders $a_0,\dots,a_{k-1}\in\mathbb{N}$, it is the matrix $\bigl(T_{a_l,j}(b_l)\bigr)_{0\le j,l<k}$.
--
--   The Wronskian detects linear independence of power series, and its order (the index of its first nonzero coefficient) can be read off from the orders of the $b_l$. The normalized matrix is the device for computing it.
--
--   **Formalization Note** $D^j$ is `derivativeIter j` (built from `PowerSeries.derivative`) and $T_{a,j}(f)$ is `derivativeTail f a j`. The file also records the simplification lemmas for $D^0$, sums, scalar multiples, and the coefficients of $T_{a,j}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Wronskian.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Wronskian.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Matrix

variable {F : Type*} [Field F]

def derivativeIter : ℕ → PowerSeries F → PowerSeries F
  | 0, f => f
  | j + 1, f => PowerSeries.derivative (R := F) (derivativeIter j f)

@[simp] theorem derivativeIter_zero (f : PowerSeries F) : derivativeIter 0 f = f := rfl

@[simp] theorem derivativeIter_add (j : ℕ) (f g : PowerSeries F) :
    derivativeIter j (f + g) = derivativeIter j f + derivativeIter j g := by
  induction j with
  | zero => rfl
  | succ j ih => simp [derivativeIter, ih]

@[simp] theorem derivativeIter_smul (j : ℕ) (c : F) (f : PowerSeries F) :
    derivativeIter j (c • f) = c • derivativeIter j f := by
  induction j with
  | zero => rfl
  | succ j ih => simp [derivativeIter, ih]

def derivativeTail (f : PowerSeries F) (a j : ℕ) : PowerSeries F :=
  PowerSeries.mk fun r => PowerSeries.coeff (r+a) f * ((r+a).descFactorial j : F)

@[simp] theorem coeff_derivativeTail (f : PowerSeries F) (a j r : ℕ) :
    PowerSeries.coeff r (derivativeTail f a j) =
      PowerSeries.coeff (r+a) f * ((r+a).descFactorial j : F) := by
  simp [derivativeTail]

def wronskianMatrix {k : ℕ} (b : Fin k → PowerSeries F) :
    Matrix (Fin k) (Fin k) (PowerSeries F) :=
  fun j l => derivativeIter j.val (b l)

def wronskian {k : ℕ} (b : Fin k → PowerSeries F) : PowerSeries F :=
  (wronskianMatrix b).det

def normalizedWronskianMatrix {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) : Matrix (Fin k) (Fin k) (PowerSeries F) :=
  fun j l => derivativeTail (b l) (a l) j.val

end NCHitting

end

end OAI


