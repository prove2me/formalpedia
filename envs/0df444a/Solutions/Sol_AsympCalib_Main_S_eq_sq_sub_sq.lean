-- Prove2me | solution 1 for AsympCalib.Main.S_eq_sq_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:45:34.20745+00:00
-- url     : https://prove2.me/submissions/79caeb98-9aed-46f7-988b-874d6f0f67b5

import Mathlib
import Definitions.Def_AsympCalib_Main_Setting
set_option autoImplicit false
noncomputable section
open AsympCalib.Main

theorem solution (k : ℕ) (hk : 0 < k) (X : ℕ → ℝ)
    (μ : ℕ → Fin (k + 1) → ℝ)
    (hμ : ∀ s, CalibratedCE.Forecast.IsDist (μ s))
    (t : ℕ) (i j : Fin (k + 1)) :
    CalibratedCE.Forecast.S (brierLoss k X) μ t i j =
      nTilde k μ t i * (rhoTilde k X μ t i - gridPt k i) ^ 2 -
      nTilde k μ t i * (rhoTilde k X μ t i - gridPt k j) ^ 2 := by
  unfold CalibratedCE.Forecast.S brierLoss rhoTilde
  have hnn : ∀ s, 0 ≤ μ s i := fun s => (hμ s).1 i
  have hLHS : ∑ s ∈ Finset.range t, μ s i * ((X s - gridPt k i) ^ 2 - (X s - gridPt k j) ^ 2)
      = -2 * (gridPt k i - gridPt k j) * (∑ s ∈ Finset.range t, μ s i * X s)
        + (gridPt k i ^ 2 - gridPt k j ^ 2) * nTilde k μ t i := by
    unfold nTilde
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hLHS]
  have key : nTilde k μ t i * ((∑ s ∈ Finset.range t, μ s i * X s) / nTilde k μ t i)
      = ∑ s ∈ Finset.range t, μ s i * X s := by
    by_cases h0 : nTilde k μ t i = 0
    · have hz : ∀ s ∈ Finset.range t, μ s i = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hnn s)).mp h0
        exact this
      rw [h0, zero_mul]
      symm
      exact Finset.sum_eq_zero fun s hs => by rw [hz s hs, zero_mul]
    · field_simp
  set r := (∑ s ∈ Finset.range t, μ s i * X s) / nTilde k μ t i
  set n := nTilde k μ t i
  rw [← key]
  ring
