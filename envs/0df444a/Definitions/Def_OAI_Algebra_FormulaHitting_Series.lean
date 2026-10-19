-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_Series
-- name    : OAI_Algebra_FormulaHitting_Series
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T08:59:07.906045+00:00
-- url     : https://prove2.me/theorems/f9c3de6c-a3fc-4043-ba86-1df80d649557
-- title:
--   Formal integration against the kernels $1/(X+i)$ and the power series attached to words
-- statement:
--   Let $F$ be a field of characteristic zero and $F[[X]]$ its power series ring; $[X^r]a$ denotes the $r$-th coefficient.
--
--   1. **Formal integral.** $\displaystyle\int a=\sum_{r\ge0}\frac{[X^r]a}{r+1}X^{r+1}$. It has constant term $0$, satisfies $(\int a)'=a$, and is $F$-linear.
--   2. **Kernels.** For $i\in\mathbb{N}$,
--   $$
--   \kappa_i=\sum_{r\ge0}\frac{(-1)^r}{i^{\,r+1}}X^r ,
--   $$
--   which for $i\ge1$ is the expansion of $\dfrac{1}{X+i}$.
--   3. **The operators $J_i$.** $J_i(a)=\int a\,\kappa_i$. Thus $J_i(a)'=a\,\kappa_i$ and $J_i(a)$ has constant term $0$. Each $J_i$ is $F$-linear and commutes with finite sums.
--   4. **Word series.** For a word $w=w_1\cdots w_m$ over letters $\{0,\dots,n-1\}$,
--   $$
--   \Phi(\varepsilon)=1,\qquad \Phi(w_1w_2\cdots w_m)=J_{w_1+1}\bigl(\Phi(w_2\cdots w_m)\bigr).
--   $$
--   In particular $\Phi(iw)'=\Phi(w)\,\kappa_{i+1}$, and $\Phi(iw)$ has constant term $0$.
--
--   The word series are iterated integrals with logarithmic kernels attached to the letters. A noncommutative polynomial is sent to a power series by replacing each word $w$ with $\Phi(w)$, and the hitting-set argument works with these series.
--
--   **Formalization Note** Most lemmas hold over any field and omit the characteristic-zero assumption; $(\int a)'=a$ uses it. Division by zero is $0$ in Lean, so $\kappa_0=0$; only $\kappa_{i+1}$ is used. `JLinear i` packages $J_i$ as a linear map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Series.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Series.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open PowerSeries
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F]

def integral (a : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun r => match r with
    | 0 => 0
    | r + 1 => PowerSeries.coeff r a / (r + 1 : F)

omit [CharZero F] in
@[simp] theorem coeff_integral_zero (a : PowerSeries F) :
    PowerSeries.coeff 0 (integral a) = 0 := by simp [integral]

omit [CharZero F] in
@[simp] theorem coeff_integral_succ (a : PowerSeries F) (r : ℕ) :
    PowerSeries.coeff (r+1) (integral a) = PowerSeries.coeff r a / (r+1 : F) := by
  simp [integral]

omit [CharZero F] in
@[simp] theorem constantCoeff_integral (a : PowerSeries F) :
    PowerSeries.constantCoeff (integral a) = 0 := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using coeff_integral_zero a

@[simp] theorem derivative_integral (a : PowerSeries F) :
    PowerSeries.derivative (R := F) (integral a) = a := by
  ext r
  rw [PowerSeries.coeff_derivative, coeff_integral_succ]
  exact div_mul_cancel₀ _ (by simpa using (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r) : ((r + 1 : ℕ) : F) ≠ 0))

omit [CharZero F] in
@[simp] theorem integral_zero : integral (0 : PowerSeries F) = 0 := by
  ext r
  cases r <;> simp [integral]

omit [CharZero F] in
@[simp] theorem integral_add (a b : PowerSeries F) :
    integral (a+b) = integral a + integral b := by
  ext r
  cases r with
  | zero => simp
  | succ r => simp [add_div]

omit [CharZero F] in
@[simp] theorem integral_smul (c : F) (a : PowerSeries F) :
    integral (c • a) = c • integral a := by
  ext r
  cases r with
  | zero => simp
  | succ r => simp [smul_eq_mul, mul_div_assoc]

def kernel (i : ℕ) : PowerSeries F :=
  PowerSeries.mk fun r => (-1 : F)^r / (i : F)^(r+1)

omit [CharZero F] in
@[simp] theorem coeff_kernel (i r : ℕ) :
    PowerSeries.coeff r (kernel (F := F) i) = (-1 : F)^r / (i : F)^(r+1) := by
  simp [kernel]

def J (i : ℕ) (a : PowerSeries F) : PowerSeries F := integral (a * kernel i)

@[simp] theorem derivative_J (i : ℕ) (a : PowerSeries F) :
    PowerSeries.derivative (R := F) (J i a) = a * kernel i := by simp [J]

omit [CharZero F] in
@[simp] theorem constantCoeff_J (i : ℕ) (a : PowerSeries F) :
    PowerSeries.constantCoeff (J i a) = 0 := by simp [J]

omit [CharZero F] in
@[simp] theorem J_zero (i : ℕ) : J i (0 : PowerSeries F) = 0 := by simp [J]

omit [CharZero F] in
@[simp] theorem J_add (i : ℕ) (a b : PowerSeries F) :
    J i (a+b) = J i a + J i b := by simp [J, add_mul]

omit [CharZero F] in
@[simp] theorem J_smul (i : ℕ) (c : F) (a : PowerSeries F) :
    J i (c • a) = c • J i a := by simp [J]

def JLinear (i : ℕ) : PowerSeries F →ₗ[F] PowerSeries F where
  toFun := J i
  map_add' := J_add i
  map_smul' := J_smul i

omit [CharZero F] in
@[simp] theorem J_sum {ι : Type*} (i : ℕ) (s : Finset ι) (a : ι → PowerSeries F) :
    J i (∑ j ∈ s, a j) = ∑ j ∈ s, J i (a j) :=
  map_sum (JLinear i) a s

def wordSeries {n : ℕ} : List (Fin n) → PowerSeries F
  | [] => 1
  | i :: w => J (i.val + 1) (wordSeries w)

omit [CharZero F] in
@[simp] theorem wordSeries_nil {n : ℕ} : wordSeries (F := F) (n := n) [] = 1 := rfl
omit [CharZero F] in
@[simp] theorem wordSeries_cons {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    wordSeries (F := F) (i :: w) = J (i.val + 1) (wordSeries w) := rfl

@[simp] theorem derivative_wordSeries_cons {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    PowerSeries.derivative (R := F) (wordSeries (i :: w)) = wordSeries w * kernel (i.val + 1) := by simp

omit [CharZero F] in
@[simp] theorem constantCoeff_wordSeries_cons {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    PowerSeries.constantCoeff (wordSeries (F := F) (i :: w)) = 0 := by simp

section Map
variable {K : Type*} [Field K] [CharZero K]

end Map

end NCHitting

end

end OAI


