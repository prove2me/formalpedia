-- Prove2me | solution 1 for ActuarialValuation.srStoppedExp_bound_on_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:58:15.676089+00:00
-- url     : https://prove2.me/submissions/65f3d928-89e0-45f2-869d-29605baa39b8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_srRuinBy
import Definitions.Def_actuarial_srStoppedExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (R u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω)
    (hR : 0 < R) (h : srRuinBy u c W Y N ω) :
    Real.exp (R * u) ≤ srStoppedExp R u c W Y N ω := by
  classical
  have hruin : srRuinBy u c W Y N ω := h
  rcases h with ⟨n, hnN, hn⟩
  let hex : ∃ j : ℕ, srRuinAt u c W Y j ω := ⟨n, hn⟩
  have hk_le_n : Nat.find hex ≤ n := by
    by_contra hnot
    exact Nat.find_min hex (lt_of_not_ge hnot) hn
  let k : ℕ := Nat.find hex
  have hkN : k ≤ N := le_trans hk_le_n hnN
  have hkFirst : srFirstHit u c W Y k ω := by
    constructor
    · exact Nat.find_spec hex
    · intro j hj
      exact Nat.find_min hex hj
  have hnet : u < srNetLoss c W Y k ω := by
    have hr : srRuinAt u c W Y k ω := hkFirst.1
    change srSurplus u c W Y k ω < 0 at hr
    unfold srSurplus at hr
    linarith
  have hExp : Real.exp (R * u) ≤ srExpLoss R c W Y k ω := by
    unfold srExpLoss
    exact le_of_lt ((Real.exp_lt_exp).2 (mul_lt_mul_of_pos_left hnet hR))
  have hterm_nonneg (j : ℕ) :
      0 ≤ (if srFirstHit u c W Y j ω then srExpLoss R c W Y j ω else 0) := by
    by_cases hj : srFirstHit u c W Y j ω
    · simp only [if_pos hj]
      unfold srExpLoss
      exact (Real.exp_pos _).le
    · simp [hj]
  have hsum :
      (if srFirstHit u c W Y k ω then srExpLoss R c W Y k ω else 0) ≤
        ∑ j ∈ Finset.range (N + 1),
          if srFirstHit u c W Y j ω then srExpLoss R c W Y j ω else 0 := by
    exact Finset.single_le_sum
      (s := Finset.range (N + 1))
      (f := fun j => if srFirstHit u c W Y j ω then srExpLoss R c W Y j ω else 0)
      (a := k)
      (fun j _ => hterm_nonneg j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkN))
  have hterm : Real.exp (R * u) ≤
      (if srFirstHit u c W Y k ω then srExpLoss R c W Y k ω else 0) := by
    simpa only [if_pos hkFirst] using hExp
  calc
    Real.exp (R * u) ≤
        (if srFirstHit u c W Y k ω then srExpLoss R c W Y k ω else 0) := hterm
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          if srFirstHit u c W Y j ω then srExpLoss R c W Y j ω else 0 := hsum
    _ = srStoppedExp R u c W Y N ω := by
      simp [srStoppedExp, hruin]
