-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_Evaluation
-- name    : OAI_Algebra_FormulaHitting_Evaluation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:00:52.706982+00:00
-- url     : https://prove2.me/theorems/71fca3cb-5124-47f4-975e-188ede79656b
-- title:
--   Noncommutative formulas as elements of the free monoid algebra
-- statement:
--   Fix $n\in\mathbb{N}$. A word is a finite list $w=w_1w_2\cdots w_m$ of letters $w_r\in\{0,\dots,n-1\}$, with length $|w|=m$; $\varepsilon$ denotes the empty word. A noncommutative formula over a semiring $F$ in variables $x_0,\dots,x_{n-1}$ is built from scalars $a\in F$, variables $x_i$, sums $f+g$ and products $f\cdot g$. Its size counts each leaf as $1$ and each $+$ or $\cdot$ node as $1$ plus the sizes of its two parts. Its coefficient series $w\mapsto f_w\in F$ assigns $a$ to $\varepsilon$ for a scalar $a$ (and $0$ to other words), the indicator of the one-letter word $i$ to $x_i$, adds termwise for sums, and takes the convolution
--   $$
--   (f\cdot g)_w=\sum_{uv=w}f_u\,g_v
--   $$
--   over all ways of cutting $w$ into a prefix $u$ and a suffix $v$ for products.
--
--   Let $F\langle x_0,\dots,x_{n-1}\rangle$ be the free monoid algebra over a semiring $F$, whose basis is the free monoid of words.
--
--   1. **Cuts of a word.** The finite set of pairs $(u,v)$ of words with $uv=w$ consists of the prefix-suffix splittings $(w_{\le k},w_{>k})$, $0\le k\le|w|$. Different $k$ give different pairs.
--   2. **Coefficients of a product.** For $f,g\in F\langle x\rangle$, the coefficient of a word $w$ in $fg$ is the convolution of the coefficient series of $f$ and $g$ at $w$.
--   3. **Polynomial of a formula.** Each formula is interpreted in $F\langle x\rangle$: a scalar $a$ maps to $a\cdot1$, a variable $x_i$ to the one-letter word $x_i$, and sums and products to sums and products. For every word $w$, the coefficient of $w$ in this element equals $f_w$.
--
--   So the coefficient series of a formula is exactly the noncommutative polynomial it computes. This connects the combinatorial definition of the coefficients with evaluation of the formula in any algebra, for example at matrices.
--
--   **Formalization Note** The free monoid algebra is `MonoidAlgebra F (FreeMonoid (Fin n))`, and the interpretation is `Formula.monoidPolynomial`. A local `DecidableEq` instance on the free monoid is inherited from lists.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Evaluation.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Evaluation.lean by skeleton subtraction
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

namespace OAI

namespace NCHitting

local instance instDecidableEqFreeMonoidFin_oAI {n : ℕ} : DecidableEq (FreeMonoid (Fin n)) :=
  inferInstanceAs (DecidableEq (List (Fin n)))

 def wordCuts {n : ℕ} (w : Word n) :
    Finset (FreeMonoid (Fin n) × FreeMonoid (Fin n)) :=
  (Finset.range (w.length + 1)).image fun k =>
    (FreeMonoid.ofList (w.take k), FreeMonoid.ofList (w.drop k))

 theorem mem_wordCuts {n : ℕ} (w : Word n)
    (p : FreeMonoid (Fin n) × FreeMonoid (Fin n)) :
    p ∈ wordCuts w ↔ p.1 * p.2 = FreeMonoid.ofList w := by
  unfold wordCuts
  constructor
  · rintro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    change w.take k ++ w.drop k = w
    exact List.take_append_drop k w
  · intro h
    apply Finset.mem_image.mpr
    have hp : p.1.toList ++ p.2.toList = w := h
    refine ⟨p.1.toList.length, Finset.mem_range.mpr ?_, ?_⟩
    · rw [← hp, List.length_append]
      omega
    · apply Prod.ext <;> apply FreeMonoid.toList.injective
      · simp [← hp]
      · simp [← hp]

 theorem cuts_injective {n : ℕ} (w : Word n) :
    Set.InjOn (fun k => (FreeMonoid.ofList (w.take k), FreeMonoid.ofList (w.drop k)))
      (Finset.range (w.length + 1)) := by
  intro k hk l hl h
  have he := congrArg (fun p : FreeMonoid (Fin n) × FreeMonoid (Fin n) =>
    p.1.toList.length) h
  simp only [FreeMonoid.toList_ofList, List.length_take] at he
  have hk' : k ≤ w.length := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hl' : l ≤ w.length := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  simpa [Nat.min_eq_left hk', Nat.min_eq_left hl'] using he

theorem monoidAlgebra_coeff_mul {F : Type*} {n : ℕ} [Semiring F]
    (f g : MonoidAlgebra F (FreeMonoid (Fin n))) (w : Word n) :
    (f * g).coeff (FreeMonoid.ofList w) =
      convolution (fun v => f.coeff (FreeMonoid.ofList v))
        (fun v => g.coeff (FreeMonoid.ofList v)) w := by
  rw [MonoidAlgebra.coeff_mul_antidiag f g _ (wordCuts w) (fun {_} => mem_wordCuts w _),
    convolution_eq_sum]
  exact Finset.sum_image (cuts_injective w)

namespace Formula

noncomputable def monoidPolynomial {F : Type*} {n : ℕ} [Semiring F] :
    Formula F n → MonoidAlgebra F (FreeMonoid (Fin n))
  | scalar a => MonoidAlgebra.single 1 a
  | var i => MonoidAlgebra.single (FreeMonoid.of i) 1
  | add f g => monoidPolynomial f + monoidPolynomial g
  | mul f g => monoidPolynomial f * monoidPolynomial g

@[simp] theorem monoidPolynomial_coeff {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) (w : Word n) :
    f.monoidPolynomial.coeff (FreeMonoid.ofList w) = f.coeff w := by
  classical
  induction f generalizing w with
  | scalar a =>
    simp only [monoidPolynomial, coeff, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    change (if ([] : Word n) = w then a else 0) = (if w = [] then a else 0)
    simp [eq_comm]
  | var i =>
    simp only [monoidPolynomial, coeff, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    change (if [i] = w then 1 else 0) = (if w = [i] then 1 else (0 : F))
    simp [eq_comm]
  | add f g ihf ihg => simp [monoidPolynomial, coeff, ihf, ihg]
  | mul f g ihf ihg =>
    rw [monoidPolynomial, monoidAlgebra_coeff_mul]
    simp only [ihf, ihg, coeff]

end Formula
end NCHitting

end OAI


