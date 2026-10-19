-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_Formula
-- name    : OAI_Algebra_FormulaHitting_Formula
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T08:57:25.819717+00:00
-- url     : https://prove2.me/theorems/a9ded45a-498e-4de8-b92b-e08556267c78
-- title:
--   Prefix-suffix expansion of word convolution and finite support of formula coefficients
-- statement:
--   Fix $n\in\mathbb{N}$. A word is a finite list $w=w_1w_2\cdots w_m$ of letters $w_r\in\{0,\dots,n-1\}$, with length $|w|=m$; $\varepsilon$ denotes the empty word. A noncommutative formula over a semiring $F$ in variables $x_0,\dots,x_{n-1}$ is built from scalars $a\in F$, variables $x_i$, sums $f+g$ and products $f\cdot g$. Its size counts each leaf as $1$ and each $+$ or $\cdot$ node as $1$ plus the sizes of its two parts. Its coefficient series $w\mapsto f_w\in F$ assigns $a$ to $\varepsilon$ for a scalar $a$ (and $0$ to other words), the indicator of the one-letter word $i$ to $x_i$, adds termwise for sums, and takes the convolution
--   $$
--   (f\cdot g)_w=\sum_{uv=w}f_u\,g_v
--   $$
--   over all ways of cutting $w$ into a prefix $u$ and a suffix $v$ for products.
--
--   The file adds the following basic facts and objects.
--
--   1. **Convolution as a finite sum.** For word series $f,g$ and a word $w$, the convolution is a sum over cut positions: $(f\cdot g)_w=\sum_{k=0}^{|w|}f_{w_{\le k}}\,g_{w_{>k}}$. Here $w_{\le k}$ is the prefix of length $k$ and $w_{>k}$ the remaining suffix.
--   2. **Degree bound.** If $f$ is a formula with $\mathrm{size}(f)<|w|$, then $f_w=0$.
--   3. **Words of a given length.** The finite set of all words of length $k$ over $n$ letters.
--   4. **The polynomial of a formula.** Its coefficient series has finite support, so a formula determines a noncommutative polynomial: a finitely supported function from words to $F$.
--
--   These facts let the coefficient series of a formula be treated as a genuine noncommutative polynomial of degree at most its size.
--
--   **Formalization Note** The names are `convolution_eq_sum`, `Formula.coeff_eq_zero_of_length_gt`, `wordsOfLength`, `Formula.coeff_support_finite` and `Formula.polynomial` (a `Finsupp`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Formula.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Formula.lean by skeleton subtraction
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

namespace OAI

namespace NCHitting

theorem convolution_eq_sum {F : Type*} {n : ℕ} [Semiring F]
    (f g : WordSeries F n) (w : Word n) :
    convolution f g w =
      ∑ k ∈ Finset.range (w.length + 1), f (w.take k) * g (w.drop k) := by
  induction w generalizing f with
  | nil => simp [convolution]
  | cons i w ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.take_zero, List.drop_zero, List.take_succ_cons,
      List.drop_succ_cons]
    rw [convolution, ih]
    exact add_comm _ _

namespace Formula

theorem coeff_eq_zero_of_length_gt {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) (w : Word n) (hw : f.size < w.length) :
    f.coeff w = 0 := by
  induction f generalizing w with
  | scalar a =>
    simp only [size] at hw
    have : w ≠ [] := by intro h; simp [h] at hw
    simp [coeff, this]
  | var i =>
    simp only [size] at hw
    have : w ≠ [i] := by intro h; simp [h] at hw
    simp [coeff, this]
  | add f g ihf ihg =>
    simp only [size] at hw
    have hf : f.size < w.length := by omega
    have hg : g.size < w.length := by omega
    simp [coeff, ihf w hf, ihg w hg]
  | mul f g ihf ihg =>
    simp only [size] at hw
    rw [coeff, convolution_eq_sum]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≤ w.length := by
      have hk'' := Finset.mem_range.mp hk
      omega
    by_cases hf : f.size < (w.take k).length
    · rw [ihf _ hf, zero_mul]
    · have hg : g.size < (w.drop k).length := by
        simp only [List.length_take, List.length_drop, Nat.min_eq_left hk'] at hf ⊢
        omega
      rw [ihg _ hg, mul_zero]

end Formula

def wordsOfLength (n : ℕ) : ℕ → Finset (Word n)
  | 0 => {[]}
  | k + 1 => Finset.univ.biUnion fun i => (wordsOfLength n k).image (List.cons i)

theorem mem_wordsOfLength {n k : ℕ} (w : Word n) :
    w ∈ wordsOfLength n k ↔ w.length = k := by
  induction k generalizing w with
  | zero => simp [wordsOfLength]
  | succ k ih =>
    cases w with
    | nil => simp [wordsOfLength]
    | cons i w => simp [wordsOfLength, ih]

theorem Formula.coeff_support_finite {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) : (Function.support f.coeff).Finite := by
  classical
  let bound := (Finset.range (f.size + 1)).biUnion (wordsOfLength n)
  apply Set.Finite.subset bound.finite_toSet
  intro w hw
  have hlen : w.length ≤ f.size := by
    by_contra h
    exact hw (f.coeff_eq_zero_of_length_gt w (by omega))
  exact Finset.mem_biUnion.mpr ⟨w.length, Finset.mem_range.mpr (by omega),
    (mem_wordsOfLength w).mpr rfl⟩

noncomputable def Formula.polynomial {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) : Word n →₀ F :=
  Finsupp.ofSupportFinite f.coeff f.coeff_support_finite

@[simp] theorem Formula.polynomial_apply {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) (w : Word n) : f.polynomial w = f.coeff w := rfl

end NCHitting

end OAI


