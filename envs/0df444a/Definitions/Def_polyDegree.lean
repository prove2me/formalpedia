-- Prove2me | Definitions.Def_polyDegree
-- name    : polyDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-04-24T03:37:24.427074+00:00
-- url     : https://prove2.me/theorems/5a59a0bf-e7be-481a-a9ed-c7e500743533
-- statement:
--   Polynomial degree `deg(f)`: smallest d with a real multilinear polynomial of total degree ≤ d matching f on {0,1}^n.

import Definitions.Def_BoolFunc
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# Polynomial degree of a Boolean function

`deg(f)` is the smallest `d` such that `f : {0,1}ⁿ → {0,1}` is realized by a
real multilinear polynomial of total degree `≤ d` on the cube.

To make the definition well-posed without any `sorry`, we inline the classic
multilinear-interpolation existence witness: every `f` is representable by a
polynomial of total degree `≤ n` (the *Lagrange interpolant* on the cube,
using indicator polynomials `∏ᵢ (xᵢ·Xᵢ + (1-xᵢ)·(1-Xᵢ))`). This lets us
construct `polyDegree` as `Nat.find` with a provable witness.
-/

open MvPolynomial

namespace BooleanInterpolation

variable {n : ℕ}

/-- Indicator polynomial of `x ∈ {0,1}ⁿ`: its value on `y` is `1` if `x = y`,
    else `0`. Formula: `∏ᵢ (if xᵢ then Xᵢ else 1 - Xᵢ)`. -/
noncomputable def indicatorPoly (x : Fin n → Bool) : MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin n, if x i then X i else 1 - X i

lemma indicatorPoly_factor_totalDegree_le (x : Fin n → Bool) (i : Fin n) :
    (if x i then (X i : MvPolynomial (Fin n) ℝ) else 1 - X i).totalDegree ≤ 1 := by
  split_ifs with h
  · simp [totalDegree_X]
  · refine (totalDegree_sub _ _).trans ?_
    simp [totalDegree_one, totalDegree_X]

lemma indicatorPoly_totalDegree_le (x : Fin n → Bool) :
    (indicatorPoly x).totalDegree ≤ n := by
  unfold indicatorPoly
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc ∑ i : Fin n, (if x i then (X i : MvPolynomial (Fin n) ℝ) else 1 - X i).totalDegree
      ≤ ∑ _ : Fin n, 1 :=
        Finset.sum_le_sum (fun i _ => indicatorPoly_factor_totalDegree_le x i)
    _ = n := by simp

lemma indicatorPoly_eval (x y : Fin n → Bool) :
    eval (fun i => if y i then (1 : ℝ) else 0) (indicatorPoly x)
      = if x = y then 1 else 0 := by
  unfold indicatorPoly
  rw [eval_prod]
  by_cases heq : x = y
  · subst heq
    rw [if_pos rfl]
    refine Finset.prod_eq_one ?_
    intros i _
    split_ifs with hx
    · simp [eval_X, hx]
    · have hx' : x i = false := by cases h : x i <;> simp [h] at hx ⊢
      simp [eval_X, hx']
  · rw [if_neg heq]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp heq
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases hx : x i = true
    · have hy : y i = false := by
        cases hy' : y i
        · rfl
        · exfalso; apply hi; rw [hx, hy']
      simp [eval_X, hx, hy]
    · have hx' : x i = false := by cases h : x i <;> simp [h] at hx ⊢
      have hy : y i = true := by
        cases hy' : y i
        · exfalso; apply hi; rw [hx', hy']
        · rfl
      simp [eval_X, hx', hy]

/-- Lagrange-style multilinear interpolant of `f` on the cube. -/
noncomputable def interpolant (f : BoolFunc n) : MvPolynomial (Fin n) ℝ :=
  ∑ x : Fin n → Bool, (if f x then (1 : ℝ) else 0) • indicatorPoly x

lemma interpolant_totalDegree_le (f : BoolFunc n) :
    (interpolant f).totalDegree ≤ n := by
  unfold interpolant
  refine MvPolynomial.totalDegree_finsetSum_le (fun x _ => ?_)
  calc ((if f x then (1 : ℝ) else 0) • indicatorPoly x).totalDegree
      ≤ (indicatorPoly x).totalDegree := totalDegree_smul_le _ _
    _ ≤ n := indicatorPoly_totalDegree_le x

lemma interpolant_eval (f : BoolFunc n) (y : Fin n → Bool) :
    eval (fun i => if y i then (1 : ℝ) else 0) (interpolant f)
      = if f y then (1 : ℝ) else 0 := by
  unfold interpolant
  simp only [map_sum, smul_eval, indicatorPoly_eval]
  rw [Finset.sum_eq_single y]
  · simp
  · intros x _ hxy
    rw [if_neg hxy, mul_zero]
  · intro h
    exact (h (Finset.mem_univ y)).elim

end BooleanInterpolation

open BooleanInterpolation

/-- `f : BoolFunc n` has a real polynomial representation of total degree ≤ `d`
    on the cube. -/
def HasPolyRep {n : ℕ} (f : BoolFunc n) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    ∀ x : Fin n → Bool,
      eval (fun i => if x i then (1 : ℝ) else 0) p =
        if f x then (1 : ℝ) else 0

/-- Existence witness: every Boolean function on `n` bits has a polynomial
    representation of degree at most `n`. -/
lemma hasPolyRep_card {n : ℕ} (f : BoolFunc n) : HasPolyRep f n :=
  ⟨interpolant f, interpolant_totalDegree_le f, interpolant_eval f⟩

open Classical in
/-- Polynomial degree `deg(f)`: smallest `d` for which a real multilinear
    polynomial of total degree ≤ `d` agrees with `f` on the cube. -/
noncomputable def polyDegree {n : ℕ} (f : BoolFunc n) : ℕ :=
  Nat.find (p := fun d => HasPolyRep f d) ⟨n, hasPolyRep_card f⟩


