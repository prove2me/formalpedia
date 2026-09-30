-- Prove2me | solution 1 for AlgMechDesign.Rounding.rounded_opt_approx
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:19:11.839093+00:00
-- url     : https://prove2.me/submissions/29834164-9eff-43a9-acac-5cf8d43d9544

import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism

set_option autoImplicit false
open AlgMechDesign.Rounding

private theorem rounding_bounds (a ε δ r : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδε : δ ≤ ε * a) (hr : a ≤ r) :
    r ≤ roundUp δ r ∧ roundUp δ r ≤ (1 + ε) * r := by
  have hlo := Int.le_ceil (r / δ)
  have hhi := Int.ceil_lt_add_one (r / δ)
  have hlo' : r ≤ δ * (⌈r / δ⌉ : ℝ) := by
    have := (div_le_iff₀ hδ).mp hlo
    nlinarith
  have hhi' : δ * (⌈r / δ⌉ : ℝ) < r + δ := by
    have := mul_lt_mul_of_pos_left hhi hδ
    field_simp at this
    nlinarith
  change r ≤ δ * (⌈r / δ⌉ : ℝ) ∧ δ * (⌈r / δ⌉ : ℝ) ≤ (1 + ε) * r
  constructor
  · exact hlo'
  · have := mul_le_mul_of_nonneg_left hr (le_of_lt hε)
    nlinarith

theorem solution {n k : ℕ} [NeZero n] (a b ε δ : ℝ)
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε * a)
    (t : Fin n → Fin k → ℝ) (ht : IsBoundedType a b t) (x : Fin k → Fin n)
    (hx : ∀ y, makespan (roundType δ t) x ≤ makespan (roundType δ t) y) :
    ∀ y, makespan t x ≤ (1 + ε) * makespan t y := by
  intro y
  have hlower : makespan t x ≤ makespan (roundType δ t) x := by
    unfold makespan
    apply Finset.sup'_mono_fun
    intro i hi
    unfold load
    apply Finset.sum_le_sum
    intro j hj
    exact (rounding_bounds a ε δ (t i j) hε hδ hδε (ht i j).1).1
  have hupper : makespan (roundType δ t) y ≤ (1 + ε) * makespan t y := by
    unfold makespan
    apply Finset.sup'_le
    intro i hi
    calc
      load (roundType δ t) y i ≤ (1 + ε) * load t y i := by
        unfold load
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        exact (rounding_bounds a ε δ (t i j) hε hδ hδε (ht i j).1).2
      _ ≤ (1 + ε) * Finset.univ.sup' Finset.univ_nonempty (load t y) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.le_sup' (load t y) hi
        · linarith
  exact hlower.trans ((hx y).trans hupper)
