-- Prove2me | solution 1 for AirlineYieldMgmt.BookingLimits.value_concave_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:12:09.179897+00:00
-- url     : https://prove2.me/submissions/d2c16f06-c18d-4a05-8d6d-b211965db618

import Mathlib
import Definitions.Def_AirlineYieldMgmt_BookingLimits_Model
import Theorems.Thm_AirlineYieldMgmt_BookingLimits_terminal_value_concave

namespace AirlineYieldMgmt.BookingLimits

/-- The accept/reject maximum preserves monotonicity: if `V` is nonincreasing at `x, x+1`, so is
`h(x) = max (r + V(x+1)) (V x)`. -/
theorem max_term_mono (V : ℕ → ℝ) (r : ℝ) (x : ℕ) (h0 : V (x + 1) ≤ V x)
    (h1 : V (x + 2) ≤ V (x + 1)) :
    max (r + V (x + 1 + 1)) (V (x + 1)) ≤ max (r + V (x + 1)) (V x) := by
  rw [show x + 1 + 1 = x + 2 by ring]
  exact max_le_max (by linarith) h0

/-- The accept/reject maximum preserves concavity: if `V` has nondecreasing decrements
`V x - V (x+1) ≤ V (x+1) - V (x+2) ≤ V (x+2) - V (x+3)`, then
`h(y) = max (r + V(y+1)) (V y)` satisfies `h x - h (x+1) ≤ h (x+1) - h (x+2)`. -/
theorem max_term_concave (V : ℕ → ℝ) (r : ℝ) (x : ℕ)
    (h0 : V x - V (x + 1) ≤ V (x + 1) - V (x + 2))
    (h1 : V (x + 1) - V (x + 2) ≤ V (x + 2) - V (x + 3)) :
    max (r + V (x + 1)) (V x) - max (r + V (x + 1 + 1)) (V (x + 1)) ≤
      max (r + V (x + 1 + 1)) (V (x + 1)) - max (r + V (x + 2 + 1)) (V (x + 2)) := by
  rw [show x + 1 + 1 = x + 2 by ring, show x + 2 + 1 = x + 3 by ring]
  have hm : max (r + V (x + 1)) (V x) + max (r + V (x + 3)) (V (x + 2)) ≤
      2 * max (r + V (x + 2)) (V (x + 1)) := by
    have a1 := le_max_left (r + V (x + 2)) (V (x + 1))
    have a2 := le_max_right (r + V (x + 2)) (V (x + 1))
    rcases max_cases (r + V (x + 1)) (V x) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases max_cases (r + V (x + 3)) (V (x + 2)) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
    rw [e1, e2] <;> linarith
  linarith

/-- One step of the induction (Lippman–Stidham): if `U_n` is nonincreasing and concave on
`0 ≤ x ≤ N - n`, then `U_{n+1}` is nonincreasing and concave on `0 ≤ x ≤ N - (n+1)`. -/
theorem value_step {m : ℕ} (M : Model m) (hM : M.Standing) (n : ℕ) (hn : n + 1 ≤ M.N)
    (ih1 : ∀ x : ℕ, x + 1 ≤ M.N - n → M.U n (x + 1) ≤ M.U n x)
    (ih2 : ∀ x : ℕ, x + 2 ≤ M.N - n → M.U n x - M.U n (x + 1) ≤ M.U n (x + 1) - M.U n (x + 2)) :
    (∀ x : ℕ, x + 1 ≤ M.N - (n + 1) → M.U (n + 1) (x + 1) ≤ M.U (n + 1) x) ∧
      (∀ x : ℕ, x + 2 ≤ M.N - (n + 1) →
        M.U (n + 1) x - M.U (n + 1) (x + 1) ≤ M.U (n + 1) (x + 1) - M.U (n + 1) (x + 2)) := by
  set V := M.U n with hV
  set P : ℝ := ∑ i, M.p (n + 1) i with hP
  set q : ℕ → ℝ := M.q (n + 1) with hq
  set A : ℕ → ℝ := fun x => ∑ i, M.p (n + 1) i * max (M.r (n + 1) i + V (x + 1)) (V x) with hA
  have hU : ∀ x, M.U (n + 1) x = A x + q x * V (x - 1) + (1 - P - q x) * V x := by
    intro x; rfl
  have hp0 : ∀ x, x ≤ M.N - (n + 1) → 0 ≤ 1 - P - q x := by
    intro x hx
    have := hM.p0_nonneg (n + 1) (by omega) hn x hx
    simpa [Model.p0] using this
  -- `V (x-1) - V x ≥ 0`
  have hE : ∀ x, x ≤ M.N - n → 0 ≤ V (x - 1) - V x := by
    intro x hx
    rcases x with _ | y
    · simp
    · simp only [Nat.add_sub_cancel]
      linarith [ih1 y (by omega)]
  -- `V (x-1) - V x ≤ V x - V (x+1)`
  have hE2 : ∀ x, x + 1 ≤ M.N - n → V (x - 1) - V x ≤ V x - V (x + 1) := by
    intro x hx
    rcases x with _ | y
    · simp only [Nat.zero_sub, sub_self]
      linarith [ih1 0 (by omega)]
    · simp only [Nat.add_sub_cancel]
      have := ih2 y (by omega)
      rw [show y + 1 + 1 = y + 2 by ring]
      exact this
  have hpi : ∀ i, 0 ≤ M.p (n + 1) i := fun i => hM.p_nonneg (n + 1) i
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hU (x + 1), hU x]
    simp only [Nat.add_sub_cancel]
    have hAm : A (x + 1) ≤ A x := by
      simp only [hA]
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact mul_le_mul_of_nonneg_left
        (max_term_mono V _ x (ih1 x (by omega)) (ih1 (x + 1) (by omega))) (hpi i)
    have e1 : 0 ≤ q x * (V (x - 1) - V x) := mul_nonneg (hM.q_nonneg _ _) (hE x (by omega))
    have e2 : 0 ≤ (1 - P - q (x + 1)) * (V x - V (x + 1)) :=
      mul_nonneg (hp0 (x + 1) hx) (by linarith [ih1 x (by omega)])
    nlinarith
  · intro x hx
    rw [hU (x + 1), hU x, hU (x + 2)]
    simp only [Nat.add_sub_cancel, show x + 2 - 1 = x + 1 by omega]
    have hAc : A x - A (x + 1) ≤ A (x + 1) - A (x + 2) := by
      simp only [hA]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [← mul_sub, ← mul_sub]
      exact mul_le_mul_of_nonneg_left
        (max_term_concave V _ x (ih2 x (by omega)) (ih2 (x + 1) (by omega))) (hpi i)
    have hqc : 0 ≤ 2 * q (x + 1) - q (x + 2) - q x := by
      have := hM.q_concave (n + 1) x
      simp only [hq]; linarith
    have f1 : 0 ≤ (1 - P - q (x + 2)) * ((V (x + 1) - V (x + 2)) - (V x - V (x + 1))) :=
      mul_nonneg (hp0 (x + 2) hx) (by linarith [ih2 x (by omega)])
    have f2 : 0 ≤ (2 * q (x + 1) - q (x + 2) - q x) * (V x - V (x + 1)) :=
      mul_nonneg hqc (by linarith [ih1 x (by omega)])
    have f3 : 0 ≤ q x * ((V x - V (x + 1)) - (V (x - 1) - V x)) :=
      mul_nonneg (hM.q_nonneg _ _) (by linarith [hE2 x (by omega)])
    nlinarith

end AirlineYieldMgmt.BookingLimits

open AirlineYieldMgmt.BookingLimits in
theorem solution {m : ℕ} (M : Model m) (hM : M.Standing)
    (n : ℕ) (hn : n ≤ M.N) :
    (∀ x : ℕ, x + 1 ≤ M.N - n → M.U n (x + 1) ≤ M.U n x) ∧
      (∀ x : ℕ, x + 2 ≤ M.N - n →
        M.U n x - M.U n (x + 1) ≤ M.U n (x + 1) - M.U n (x + 2)) := by
  induction n with
  | zero =>
    obtain ⟨h1, h2⟩ := terminal_value_concave M hM.β_nonneg hM.β_le_one hM.π_convex hM.π_mono
    exact ⟨fun x _ => h1 (Nat.le_succ x), fun x _ => by linarith [h2 x]⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    exact value_step M hM n hn ih1 ih2
