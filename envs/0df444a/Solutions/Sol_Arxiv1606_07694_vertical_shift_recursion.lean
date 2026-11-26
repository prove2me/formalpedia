-- Prove2me | solution 1 for Arxiv1606_07694.vertical_shift_recursion
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T03:04:47.15111+00:00
-- url     : https://prove2.me/submissions/b37d3ade-22cd-4e80-a29c-cfb238d94da5

import Mathlib
import Definitions.Def_Arxiv1606_07694_Basic

set_option autoImplicit false

open MeasureTheory Complex

namespace S76VS
open Arxiv1606_07694

lemma app0 {n m : ℕ} (κ : Fin n → Vec2) (i : Fin (n + m)) :
    Fin.append κ (0 : Fin m → Vec2) i = if h : (i : ℕ) < n then κ ⟨i, h⟩ else 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left]
  · simp [Fin.append_right]

lemma app_zero {n : ℕ} (κ : Fin n → Vec2) : Fin.append κ (0 : Fin 0 → Vec2) = κ := by
  funext i
  rw [app0]
  simp [i.2]

lemma app_assoc {n m : ℕ} (κ : Fin n → Vec2) :
    Fin.append κ (0 : Fin (m + 1) → Vec2) =
      Fin.append (Fin.append κ (0 : Fin m → Vec2)) (0 : Fin 1 → Vec2) := by
  funext i
  rw [app0, app0 (m := 1)]
  by_cases h : (i : ℕ) < n
  · have h' : (i : ℕ) < n + m := by omega
    simp only [h, h', dif_pos]
    rw [app0]; simp [h]
  · simp only [h, dif_neg, not_false_eq_true]
    split_ifs with h'
    · rw [app0]; simp [h]
    · rfl

lemma hyp_app {n m : ℕ} (k k0 : Vec2) (κ : Fin n → Vec2) (hκ : OnHyperplane k k0 κ) :
    OnHyperplane k k0 (Fin.append κ (0 : Fin m → Vec2)) := by
  unfold OnHyperplane at *
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right, hκ]

end S76VS

open Arxiv1606_07694 S76VS in
theorem solution (G : KernelFamily) (hG : IsSymmetricKernel G)
    (qv : Vec2 → ℂ) (k k0 : Vec2)
    (h14 : ∀ (n p : ℕ) (κ : Fin n → Vec2), 0 < p → OnHyperplane k k0 κ →
      ∑ j ∈ Finset.range (p + 1), (-1 : ℂ) ^ j * (p.choose j : ℂ) * shiftFactor qv k k0 ^ (p - j) *
        G (n + j) k k0 (Fin.append κ (0 : Fin j → Vec2)) = 0) :
    ∀ (n m : ℕ) (κ : Fin n → Vec2), OnHyperplane k k0 κ →
      G (n + m) k k0 (Fin.append κ (0 : Fin m → Vec2)) = shiftFactor qv k k0 ^ m * G n k k0 κ := by
  have step : ∀ (n : ℕ) (κ : Fin n → Vec2), OnHyperplane k k0 κ →
      G (n + 1) k k0 (Fin.append κ (0 : Fin 1 → Vec2)) = shiftFactor qv k k0 * G n k k0 κ := by
    intro n κ hκ
    have h := h14 n 1 κ (by norm_num) hκ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, mul_one, Nat.sub_zero,
      Nat.sub_self] at h
    have h0 : G (n + 0) k k0 (Fin.append κ (0 : Fin 0 → Vec2)) = G n k k0 κ := by
      rw [app_zero]; rfl
    rw [h0] at h
    linear_combination -h
  intro n m κ hκ
  induction m with
  | zero => simp only [pow_zero, one_mul]; exact congrArg (G n k k0) (app_zero κ)
  | succ m ih =>
    rw [app_assoc]
    show G (n + m + 1) k k0 _ = _
    rw [step (n + m) _ (hyp_app k k0 κ hκ), ih, pow_succ]
    ring
