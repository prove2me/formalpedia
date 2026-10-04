-- Prove2me | solution 1 for Apery.tendsto_pow_mul_exp_neg_sq_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T15:18:13.06578+00:00
-- url     : https://prove2.me/submissions/23007b48-a054-4ff7-89f4-a5c029dc2f76

import Mathlib

open Filter Topology Real

theorem solution {c : ℝ} (hc : 0 < c) (b : ℕ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ (37 * n) * exp (-c * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hinner :
      Tendsto (fun n : ℕ => (37 : ℝ) * log (b : ℝ) - c * (n : ℝ)) atTop atBot := by
    rw [tendsto_atBot]
    intro A
    refine eventually_atTop.2 ?_
    let N : ℕ := Nat.ceil (((37 : ℝ) * log (b : ℝ) - A) / c)
    refine ⟨N, fun n hn => ?_⟩
    have hN : ((37 : ℝ) * log (b : ℝ) - A) / c ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [div_le_iff₀ hc] at hN
    linarith
  have hexp :
      Tendsto (fun n : ℕ => (n : ℝ) * ((37 : ℝ) * log (b : ℝ) - c * (n : ℝ))) atTop atBot :=
    tendsto_natCast_atTop_atTop.atTop_mul_atBot₀ hinner
  refine (tendsto_exp_comp_nhds_zero.mpr hexp).congr fun n => ?_
  have hpow : (b : ℝ) ^ (37 * n) = exp (((37 * n : ℕ) : ℝ) * log (b : ℝ)) := by
    calc
      (b : ℝ) ^ (37 * n) = exp (log (b : ℝ)) ^ (37 * n) := by rw [exp_log hbpos]
      _ = exp (((37 * n : ℕ) : ℝ) * log (b : ℝ)) := by
        rw [← exp_nat_mul]
  rw [hpow, ← exp_add]
  congr 1
  push_cast
  ring
