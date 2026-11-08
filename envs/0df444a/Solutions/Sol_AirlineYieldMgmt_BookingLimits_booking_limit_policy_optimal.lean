-- Prove2me | solution 1 for AirlineYieldMgmt.BookingLimits.booking_limit_policy_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:10:42.729458+00:00
-- url     : https://prove2.me/submissions/cb83d68f-871e-4187-b0bb-ae6ec64035a4

import Mathlib
import Definitions.Def_AirlineYieldMgmt_BookingLimits_Model
import Theorems.Thm_AirlineYieldMgmt_BookingLimits_value_concave_nonincreasing

namespace AirlineYieldMgmt.BookingLimits

/-- If the differences `D y` are nondecreasing step by step on `0 ≤ y ≤ L`, they are monotone
on that range. -/
theorem diff_mono_of_step (D : ℕ → ℝ) (L : ℕ) (hstep : ∀ y, y + 1 ≤ L → D y ≤ D (y + 1)) :
    ∀ y z, y ≤ z → z ≤ L → D y ≤ D z := by
  intro y z hyz hzL
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hyz
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hstep (y + k) (by omega)
    rw [← add_assoc]
    linarith

/-- The threshold structure: if the differences are monotone on the reachable range, the set of
states where rejection is strictly better is an upper segment, and its minimum is the booking
limit. -/
theorem accept_iff_lt_min (D : ℕ → ℝ) (L : ℕ) (r : ℝ)
    (hmono : ∀ y z, y ≤ z → z ≤ L → D y ≤ D z) (x : ℕ) (hx : x ≤ L) :
    D x ≤ r ↔ (x : WithTop ℕ) < ((Finset.range (L + 1)).filter (fun y => r < D y)).min := by
  constructor
  · intro hDx
    cases h : ((Finset.range (L + 1)).filter (fun y => r < D y)).min with
    | top => exact WithTop.coe_lt_top x
    | coe y =>
      have hy := Finset.mem_of_min h
      rw [Finset.mem_filter, Finset.mem_range] at hy
      refine WithTop.coe_lt_coe.mpr ?_
      by_contra hxy
      push Not at hxy
      have := hmono y x hxy hx
      linarith [hy.2]
  · intro hlt
    by_contra hDx
    push Not at hDx
    have hmem : x ∈ (Finset.range (L + 1)).filter (fun y => r < D y) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hDx⟩
    have := Finset.min_le hmem
    exact absurd hlt (not_lt.mpr this)

end AirlineYieldMgmt.BookingLimits

open AirlineYieldMgmt.BookingLimits in
theorem solution {m : ℕ} (M : Model m) (hM : M.Standing)
    (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ M.N) (i : Fin m) (x : ℕ) (hx : x ≤ M.N - n) :
    M.U (n - 1) x ≤ M.r n i + M.U (n - 1) (x + 1) ↔
      (x : WithTop ℕ) < M.bookingLimit n i := by
  have hc := (value_concave_nonincreasing M hM (n - 1) (by omega)).2
  set D : ℕ → ℝ := fun y => M.U (n - 1) y - M.U (n - 1) (y + 1) with hD
  have hstep : ∀ y, y + 1 ≤ M.N - n → D y ≤ D (y + 1) := by
    intro y hy
    exact hc y (by omega)
  have key := accept_iff_lt_min D (M.N - n) (M.r n i)
    (diff_mono_of_step D (M.N - n) hstep) x hx
  unfold Model.bookingLimit
  rw [← key]
  simp only [hD]
  constructor <;> intro h <;> linarith
