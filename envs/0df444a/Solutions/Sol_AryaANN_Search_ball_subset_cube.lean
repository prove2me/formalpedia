-- Prove2me | solution 1 for AryaANN.Search.ball_subset_cube
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:01:50.840482+00:00
-- url     : https://prove2.me/submissions/eb54e277-227f-4275-a434-5dd6f0fd15b2

import Mathlib
import Definitions.Def_AryaANN_Search_Setting
set_option autoImplicit false

theorem solution {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (c : Fin d → ℝ) (r : ℝ) :
    ∀ x : Fin d → ℝ, AryaANN.Search.lmDist m c x ≤ r → ∀ i, |x i - c i| ≤ r := by
  intro x hx i
  rw [abs_sub_comm]
  refine le_trans ?_ hx
  unfold AryaANN.Search.lmDist
  split_ifs with h
  · exact le_ciSup (f := fun i => |c i - x i|) (Set.finite_range _).bddAbove i
  · have hk : 1 ≤ m.toNat := by
      have : m ≠ ⊤ := h
      lift m to ℕ using this
      simpa using hm
    set k := m.toNat with hkdef
    have h1 : |c i - x i| ^ k ≤ ∑ j, |c j - x j| ^ k :=
      Finset.single_le_sum (f := fun j => |c j - x j| ^ k) (fun j _ => by positivity) (Finset.mem_univ i)
    have h2 : (|c i - x i| ^ k) ^ ((1 : ℝ) / k) ≤ (∑ j, |c j - x j| ^ k) ^ ((1 : ℝ) / k) :=
      Real.rpow_le_rpow (by positivity) h1 (by positivity)
    have h3 : (|c i - x i| ^ k) ^ ((1 : ℝ) / k) = |c i - x i| := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      have : (k : ℝ) * (1 / k) = 1 := by
        have : (k : ℝ) ≠ 0 := by positivity
        field_simp
      rw [this, Real.rpow_one]
    rw [← h3]; exact h2
