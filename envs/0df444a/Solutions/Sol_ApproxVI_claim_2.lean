-- Prove2me | solution 1 for ApproxVI.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:12:44.302194+00:00
-- url     : https://prove2.me/submissions/5486c025-7bc9-4238-84e7-c8497b72b3b2

import Mathlib
import Definitions.Def_ApproxVI_wNorm
import Definitions.Def_ApproxVI_euclNorm

open ApproxVI in
theorem solution {d : ℕ} [NeZero d] (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (z : Fin d → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty ν * wNorm ν z ≤ ‖z‖ ∧
      ‖z‖ ≤ euclNorm z ∧
      euclNorm z ≤ Real.sqrt d * Finset.univ.sup' Finset.univ_nonempty ν * wNorm ν z := by
  set m := Finset.univ.inf' Finset.univ_nonempty ν with hm
  set M := Finset.univ.sup' Finset.univ_nonempty ν with hM
  have hmle : ∀ i, m ≤ ν i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have hMge : ∀ i, ν i ≤ M := fun i => Finset.le_sup' _ (Finset.mem_univ i)
  have hmpos : 0 < m := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty ν
    rw [hm, hi]
    exact hν i
  have hbdd : BddAbove (Set.range fun i => |z i| / ν i) := Set.finite_range _ |>.bddAbove
  have hle : ∀ i, |z i| / ν i ≤ wNorm ν z := fun i => le_ciSup hbdd i
  have hW0 : 0 ≤ wNorm ν z :=
    le_trans (div_nonneg (abs_nonneg _) (hν 0).le) (hle 0)
  have hzi : ∀ i, |z i| ≤ ‖z‖ := fun i => by
    have := norm_le_pi_norm (f := z) i
    rwa [Real.norm_eq_abs] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_comm, ← le_div_iff₀ hmpos]
    unfold wNorm
    apply ciSup_le
    intro i
    calc |z i| / ν i ≤ |z i| / m := div_le_div_of_nonneg_left (abs_nonneg _) hmpos (hmle i)
      _ ≤ ‖z‖ / m := div_le_div_of_nonneg_right (hzi i) hmpos.le
  · unfold euclNorm
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (f := fun j => z j ^ 2) (fun j _ => sq_nonneg (z j))
      (Finset.mem_univ i)
  · unfold euclNorm
    have hb : ∀ i, |z i| ≤ M * wNorm ν z := by
      intro i
      have h1 : |z i| = ν i * (|z i| / ν i) := (mul_div_cancel₀ _ (hν i).ne').symm
      rw [h1]
      exact mul_le_mul (hMge i) (hle i) (div_nonneg (abs_nonneg _) (hν i).le)
        (le_trans (hν i).le (hMge i))
    have hMW : 0 ≤ M * wNorm ν z := le_trans (abs_nonneg _) (hb 0)
    have hsum : ∑ i, z i ^ 2 ≤ (d : ℝ) * (M * wNorm ν z) ^ 2 := by
      calc ∑ i, z i ^ 2 ≤ ∑ _i : Fin d, (M * wNorm ν z) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
        _ = (d : ℝ) * (M * wNorm ν z) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc Real.sqrt (∑ i, z i ^ 2) ≤ Real.sqrt ((d : ℝ) * (M * wNorm ν z) ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt d * (M * wNorm ν z) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hMW]
      _ = Real.sqrt d * M * wNorm ν z := by ring
