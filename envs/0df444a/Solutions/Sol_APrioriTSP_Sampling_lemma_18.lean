-- Prove2me | solution 1 for APrioriTSP.Sampling.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T21:10:35.913076+00:00
-- url     : https://prove2.me/submissions/14382a1b-d5da-4fad-af2f-6ad60dfc6db8

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

namespace Queelius.APrioriTSP

theorem geometric_tail (n : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => if n + 1 ≤ k then (k : ℝ) * q ^ (k - 1) else 0)
      (q ^ n / (1 - q) ^ 2 * (1 + n - q * n)) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hne : 1 - q ≠ 0 := by linarith
  have hs := (((hasSum_geometric_of_norm_lt_one hnorm).mul_left ((n : ℝ) + 1)).add
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm)).mul_left (q ^ n)
  have hf : (fun j : ℕ => ((j : ℝ) + n + 1) * q ^ (j + n)) =
      (fun j : ℕ => q ^ n * (((n : ℝ) + 1) * q ^ j + (j : ℝ) * q ^ j)) := by
    funext j
    rw [pow_add]
    ring
  have hv : q ^ n / (1 - q) ^ 2 * (1 + n - q * n) =
      q ^ n * (((n : ℝ) + 1) * (1 - q)⁻¹ + q / (1 - q) ^ 2) := by
    field_simp
    <;> ring
  have hs' : HasSum (fun j : ℕ => ((j : ℝ) + n + 1) * q ^ (j + n))
      (q ^ n / (1 - q) ^ 2 * (1 + n - q * n)) := by
    rw [hf, hv]
    exact hs
  let f : ℕ → ℝ := fun k => if n + 1 ≤ k then (k : ℝ) * q ^ (k - 1) else 0
  have ht : HasSum (fun j : ℕ => f (j + (n + 1)))
      (q ^ n / (1 - q) ^ 2 * (1 + n - q * n)) := by
    convert hs' using 1
    ext j
    dsimp [f]
    rw [if_pos (by omega)]
    have he : j + (n + 1) - 1 = j + n := by omega
    try rw [he]
    push_cast
    ring
  have hz : ∑ i ∈ Finset.range (n + 1), f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    dsimp [f]
    rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
  have hall := (hasSum_nat_add_iff (n + 1)).mp ht
  simpa only [hz, add_zero] using hall

end Queelius.APrioriTSP

open APrioriTSP.Sampling

/-- Lemma 18 (p. 14): `Σ_{k=n+1}^∞ k q^{k−1} = q^n / (1 − q)² · (1 + n − q n)` for `n ∈ ℕ`,
`q ∈ (0, 1)`. -/
theorem solution (n : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => if n + 1 ≤ k then (k : ℝ) * q ^ (k - 1) else 0)
      (q ^ n / (1 - q) ^ 2 * (1 + n - q * n)) := by
  exact Queelius.APrioriTSP.geometric_tail n q hq0 hq1

