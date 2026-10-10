-- Prove2me | solution 1 for ActuarialValuation.wholeLifeHattendorff_finiteTailEnergyXXIII
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T23:08:05.865996+00:00
-- url     : https://prove2.me/submissions/ea069f20-21ba-4e38-977a-940eb95daee7

import Mathlib
import Definitions.Def_actuarial_wholeLifeTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    (w rho : ℕ → ℝ) (T N : ℕ) (hTN : T ≤ N)
    (hNonneg : ∀ t, 0 ≤ w t)
    (hS : ∀ t, 0 < wholeLifeTailMass w t)
    (hTail : ∀ t, wholeLifeTailMass w t =
      w t + wholeLifeTailMass w (t + 1)) :
  wholeLifeTailMass w N *
    (∑ t ∈ Finset.Ico T N, rho t * (w t / wholeLifeTailMass w t)) ^ 2 ≤
  ∑ t ∈ Finset.Ico T N, (rho t) ^ 2 * w t *
    (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t) := by
  classical
  let S (t : ℕ) : ℝ := wholeLifeTailMass w t
  let r (t : ℕ) : ℝ := rho t * (w t / S t)
  let f (t : ℕ) : ℝ := (rho t) ^ 2 * w t * (S (t + 1) / S t)
  let g (t : ℕ) : ℝ := w t / (S t * S (t + 1))
  have hrf (t : ℕ) : (r t) ^ 2 = f t * g t := by
    dsimp [r, f, g, S]
    field_simp [ne_of_gt (hS t), ne_of_gt (hS (t + 1))]
  have hfn (t : ℕ) : 0 ≤ f t := by
    dsimp [f, S]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (hNonneg t))
      (div_nonneg (le_of_lt (hS (t + 1))) (le_of_lt (hS t)))
  have hgn (t : ℕ) : 0 ≤ g t := by
    dsimp [g, S]
    exact div_nonneg (hNonneg t)
      (mul_nonneg (le_of_lt (hS t)) (le_of_lt (hS (t + 1))))
  have htel (t : ℕ) : g t = 1 / S (t + 1) - 1 / S t := by
    dsimp [g, S]
    have h := hTail t
    field_simp [ne_of_gt (hS t), ne_of_gt (hS (t + 1))]
    linarith
  have hgsum :
      (∑ t ∈ Finset.Ico T N, g t) = 1 / S N - 1 / S T := by
    simp_rw [htel]
    simpa using (Finset.sum_Ico_sub (fun t : ℕ => 1 / S t) hTN)
  have hscale :
      S N * (∑ t ∈ Finset.Ico T N, g t) ≤ 1 := by
    rw [hgsum]
    have hN : S N ≠ 0 := ne_of_gt (hS N)
    have hT : S T ≠ 0 := ne_of_gt (hS T)
    have hge : 0 ≤ S N / S T := div_nonneg (le_of_lt (hS N)) (le_of_lt (hS T))
    have heq : S N * (1 / S N - 1 / S T) = 1 - S N / S T := by
      field_simp [hN, hT]
    rw [heq]
    linarith
  have hcauchy :
      (∑ t ∈ Finset.Ico T N, r t) ^ 2 ≤
        (∑ t ∈ Finset.Ico T N, f t) *
          (∑ t ∈ Finset.Ico T N, g t) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Ico T N)
      (by intro t ht; exact hfn t)
      (by intro t ht; exact hgn t)
      (by intro t ht; exact le_of_eq (hrf t))
  have hfnonneg : 0 ≤ ∑ t ∈ Finset.Ico T N, f t :=
    Finset.sum_nonneg (by intro t ht; exact hfn t)
  change S N * (∑ t ∈ Finset.Ico T N, r t) ^ 2 ≤
    ∑ t ∈ Finset.Ico T N, f t
  calc
    S N * (∑ t ∈ Finset.Ico T N, r t) ^ 2 ≤
        S N * ((∑ t ∈ Finset.Ico T N, f t) *
          (∑ t ∈ Finset.Ico T N, g t)) :=
          mul_le_mul_of_nonneg_left hcauchy (le_of_lt (hS N))
    _ = (∑ t ∈ Finset.Ico T N, f t) *
        (S N * ∑ t ∈ Finset.Ico T N, g t) := by ring
    _ ≤ ∑ t ∈ Finset.Ico T N, f t := by
      simpa using (mul_le_mul_of_nonneg_left hscale hfnonneg)

