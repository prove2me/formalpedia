-- Prove2me | Definitions.Def_PretorsionImageClosed_Gandhi_Delta
-- name    : PretorsionImageClosed_Gandhi_Delta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:43.939115+00:00
-- url     : https://prove2.me/theorems/87e00b37-041c-4aed-893d-f986b047b104
-- title:
--   Delta
-- statement:
--   Definitions and structural lemmas for Delta, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed.Statement
open Polynomial
abbrev U : Rq[X] := 1 + C q * X
theorem one_add_C_sub_mul_X : (1 + C (q - 1) * X : Rq[X]) = U - X := by
  rw [C_sub, C_1]
  ring
theorem IsDelta.add {f g f' g' : Rq[X]} (h : IsDelta f g) (h' : IsDelta f' g') :
    IsDelta (f + f') (g + g') := by
  unfold IsDelta at *
  rw [add_mul, h, h', add_comp]
  ring
theorem IsDelta.C_mul {f g : Rq[X]} (c : Rq) (h : IsDelta f g) : IsDelta (C c * f) (C c * g) := by
  unfold IsDelta at *
  rw [mul_assoc, h, C_mul_comp]
  ring
theorem isDelta_one : IsDelta (1 : Rq[X]) 0 := by
  unfold IsDelta
  simp
def geomSum (m : ℕ) : Rq[X] := ∑ i ∈ Finset.range (m + 1), X ^ i * U ^ (m - i)
theorem geomSum_zero : geomSum 0 = 1 := by
  simp [geomSum]
theorem geomSum_succ (m : ℕ) : geomSum (m + 1) = U * geomSum m + X ^ (m + 1) := by
  unfold geomSum
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have : m + 1 - i = (m - i) + 1 := by omega
  rw [this, pow_succ]
  ring
theorem geomSum_mul_sub (m : ℕ) : geomSum m * (U - X) = U ^ (m + 1) - X ^ (m + 1) := by
  induction m with
  | zero => rw [geomSum_zero]; ring
  | succ m ih =>
    rw [geomSum_succ, add_mul, mul_assoc, ih]
    ring
theorem isDelta_X_pow_succ (m : ℕ) : IsDelta (X ^ (m + 1)) (geomSum m) := by
  unfold IsDelta
  rw [one_add_C_sub_mul_X, geomSum_mul_sub, X_pow_comp]
def deltaXPow : ℕ → Rq[X]
  | 0 => 0
  | m + 1 => geomSum m
theorem isDelta_X_pow (m : ℕ) : IsDelta (X ^ m) (deltaXPow m) := by
  cases m with
  | zero =>
    show IsDelta (X ^ 0) 0
    rw [pow_zero]
    exact isDelta_one
  | succ m => exact isDelta_X_pow_succ m
theorem exists_isDelta (f : Rq[X]) : ∃ g, IsDelta f g := by
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨g, hg⟩ := hp
    obtain ⟨g', hg'⟩ := hr
    exact ⟨g + g', hg.add hg'⟩
  | monomial m c =>
    rw [← C_mul_X_pow_eq_monomial]
    exact ⟨C c * deltaXPow m, (isDelta_X_pow m).C_mul c⟩
def gandhiFirst : ℕ → Rq[X]
  | 0 => 0
  | 1 => 1
  | m + 2 => Classical.choose (exists_isDelta (X ^ 2 * gandhiFirst (m + 1)))
def gandhiSecond : ℕ → Rq[X]
  | 0 => 0
  | 1 => 1
  | m + 2 => U * Classical.choose (exists_isDelta (X * gandhiSecond (m + 1)))
end PretorsionImageClosed.Statement


